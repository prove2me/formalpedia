-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3376
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:29:04.622985+00:00
-- url     : https://prove2.me/submissions/f75565bb-7320-459c-9be2-8f4e395cc1e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 607014388 ≤ n < 607194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 607015638 1250 607014388 607014431
    0x21c050609060406080d20010e070f05030d0e0906030c10180e0c0307050c01020f0d0506040c080103050309041d0604050105010e0714071403090a0e0709060e0904060c0c050303150a09 80
    0x20104032603104040241c940140c400101500041f00a0003030100303040c10b07555514500d001d03003031461a02042c0019640b40010b08031207080c03082e4a0701806258494100004694001d0480790075000302410420103550f82156440c100c0c02030b4a0f0441d8109540300c403d0b1803000983c01090120110109000040d0350311000c0d260b0041d00351410558500b4040c2d415170180c00b0702c0b110a010080d004c6410f123088080ca41146104040940d030801a83c9410700b8115508402031201612603001001030141d642032540040003100e000e100461104602c94007100d16042c1c00f15800d0310b480c0d65480050049100b012603031500314005241c0311547c00e80c504504d1f0440d21600600500780701c02c1400184140c4014402e603021140c00030034403900990364000408a40d801112090009200d661000c5141401041b4840046a0280c11080950380c1d5980b840010481880f82c0c00c18048106502c000140082005611034200803186000c16400c0e00280550f842c01c80d0840030819042c4551900703020509070b100c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 607016888 1250 607015638 607015663
    0x152615041401060f0929010e030c120d0e0307030803010e04060b040e15130804030206132102010207050f0310050a11040306060e060603040c03030f0201021c05060906040608 76
    0x1805a850364a032003069840d14440d255155420003900054041c450141ca908641081800f40140ca102d40040c48400400c84d03032201c1d41b007440202c112115441000d100000070406400c6031300404140700003030346c84141e01c43e40311403c1d40015040310080d58401082210b4007002c0d00204041c90442e9503802440c00140910002e41c400c8500040903ca0550002500343e00040e1042015844074080c144e01e4845203000d40c0728400ca2400401d0b02c403081da1040098041d001521281014115403c02007107501011506507402525100491500c0c01451099801640240c000c80c03030180ba4400682000ca040c2d205901c610320301103041c40180c90120300038226900c0c03440009000d84c0c90180d89401002507034004083ca1102060210410103103a00c40d80c280c802040e41c4413100d035141d8007002180d01c001c58000301a541c01090410000780108810701c0c034921607000150400d000040450303004016444807903202e075214400d010080c2003039089150845030a841c01c1c806076081600d0559184102c01c050b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 607018138 1250 607016888 607016923
    0xf1b02060403030c1b0b0f0f01060c060b12031b0d030218040507031103010b04081203011a03070219060b010318050304050f1504080102030615070201020624041526 72
    0x20300c4049172050069541d4105000d10020300212513080102d003001048031000001426400400e24241e042c2199a048404a64860f545040310b5660140901424544d007a000081d0001c02c002001080c0060304800313045440f50340b100c024000030503142051300040c8000707051040204030188569160600201c88069030081008c0d22006812001081009c401041c101c4002c0000714083c09003000500494044104607104048104152032140c4000c1c800e03d540d04690343c031968617000c10341c40030f980c0c0103886005803103071030740d0018580c0000740500c602100e4441d514010030080f0b40e01442640c84614100c520b60940f103005a40d107c0d40ea10903801100d01c946004500301c1c0040d44c4034007022240c0d0328080c20040c3c03903c1e5940103580c00f0350002ea44051242111104220b41d003449007090f0781d021501603004160980354a01c070116014592282d2040e1082100324242d0141c0380d900410b01072012400c050703403c00345401582c0c40d058021000c080d030030030301a4290512218002450003207a10b6400c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 607019388 1250 607018138 607018151
    0x3090506280e0c010302160f03030507020d18290a0c0c0b0a0e0609060904020d0605012a110409080c0a12050408070e091e0703030f140d0e01110705010f1b0206040303 73
    0xa61041401c0c000010b0600d023215103100105076050300524002d8030340c1d408075442101241001d4501e18000c05902c0030b21035060f902049180241c10188054010a0444600712860300391012120303441540030501042c0950394040410810302013140044c00c0a00440d8100000c50300001c4c00301c40d00420f014410300c0c004c601a081c0d030b0780d542d08441110400500455480c00c005100c000038109512035507011030201e04c1c1008000f044480400c2c0d500c4030a0040480f51703036051380c940c8a1901c80c0f843d05901325588462410006408400401c030385119031005000e0040280740c040740c1400340300300c40c8081090034801045603c030006100c400b51a0001c41c190003607902c0c5c0c89032518000e0021006110342035080800b5108000210b08071082e80d0003540d50104c03803181e4990a1382d500f105aa42848440c0007040514a2100030b41c0c4212210918a0008070703100580404810894028803000e840036552807040c0078070b095003885001e1b011160b00c0305102c084100180c02a44800e0028806401d0584401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 607020638 1250 607019388 607019407
    0x2090906040c111911040b100c050a0b01030b040c15020a02221e0608011e0c0e03030d0c030510030206090108150613180b1f03090506280e0c010302 65
    0x124900e08010b050390840307425540c188913a0321104100c80d01540e0039181510014202c6c00c1c140600c0d04c0448010305078100d200d80d805801c0b83c10290000080e07825001d280320050020f03240030301c4607000350b0040d240700d0b5503410142084400985207a001445111001030142c0c1d240d900070503447c02e003e404840f13001c0940c0d100a6000205007240c06104400380c030b070030104a480980380300d45401e4908840020800300707868958090880c0c0f039801c18040a9404498550100005070b01300044d80c90003842c1084010100c10042440c58202c070b0541ca480c107860303813400aa01641803290b240d0150040c0116407865281d5000305000f0b01c26000030504122185000500c9800c44207503c9000760b4000c0c09441c0e41d60300c030880c491100151400750130101c00c0244e40c0226001002c1c0a007180d01100149013218061070740901a107011042c1c144402410f40382c4454601180d0180030851041d000443d0700c10310904c200c2c0207120000e4619241410ba0703407412120f0245900005148403070301c0001e080046c1d0b80e04828 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 607021888 1250 607020638 607020647
    0x3081b0a150f1803170c090d06020a0c0b0a0c230307030c021606030f0f0b09150f060c0f06010e090d200d0c0c0f0608270f030304031202090906040c 65
    0xa04030742c543c580b04a0404020154012200c0c0f15440050036407080030740b101c4200818500c582602154002008101c00c408955564001d00149000c0e0812443d451155507458150300b10031210102c0c6555a280c6503081035410949035000600b190071480c0718100790940b41c828500018101e18101035440d00003102c0c4900800c0aa0140c2000c09c8038488095580c0100402401054400102c507900b400d81089615065026090300d01c240103119100540e1a80740030240711044169407a0f001c4101d4002441c0c1d51110030040100201010282c41341035845040c0a01c0e222040c5c2c016103038800f0040070001800400301b401c042900c450b190040c2040580c0c8100041e041c08034840045500603100b0034558140c00c280704d504070230312800030400d0301c40d43d410ba001c04c00c100c1c0784140000701d900d4000280100398001c2d00700d02c52501e480c145042e5210141e035078902c0d00c051031801781c50590002050106154022000140c1c518004000790714000881004c2803008002804040c081c60309c4c0c484c24004c03103010703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 607023138 1250 607021888 607021901
    0x190b0703150f031106030402030c090c13030c140108130b0c0f1902060903091302071e20030c0114030603010e010e1006050a030302070b07080d0603081b0a150f 70
    0x1080c031142015196401102010418441110070b05284e1481c0582030404805982c802c5030003d0250141c448114188408414003c110741c004030800c10007010307008200412072024500a0100450f420b085c060340c0744d04039070350859050500c14500104081c1106491183c0780c02070344882c0300483c60316501a65860ba0180710b00c454100c1001154030001795401c41180001c90038550308440007502c1e82c4c05459101d102d01ca010135001048111200510300301500104595403050804403001d0300c0c0c07a1b401e440c000a6068003100c5403c04140d842d180c460001c50011681c0300e0403400b80042c1c090f403000203406400400141204e00c9000301c00030324199801c2d4440c01c401c0060300000d0044001031800395480e1800188140095490000b000c916410202040004c2d00d51680051002c40d09000016100b60840f4404032010481003115800078080307402104010341c0300d103803026202d60040840c1b02c444142c1c540740b85200d901054204000c51715601070b21a00440300f034400a100d811840b0783d0406040b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 607024388 1250 607023138 607023161
    0x3011509030b04030c02030d08070503071803140f06070305010b070609020102160e1915061b08120f0f04050a02090601020c03060906100f231c2003190b0703 69
    0x42c444104400d01da00300307100c900303041c0c4200d003a0741c01c00520007802d990114084d40e41800060b030a000060980d40a80203d0241954044101403500e50b280e541500c5d400380031a920b005504102540f5400e04010480650081031505050103258104081c10300307240944070000c1d100f00c0d101c0011030b00313590007404900e040c0d81c44810000007170340c1c4614112000110a40d5090100e4001c840b07444114040d80c03140001c402c0c1c400b0b1104604130b1421384125141441c111003610032500f00b2640b480041d07680401042c2103910582c131501580b03810f2061040306400204907112680100c4200700002e86c0109090707810941c1290b0b20100794440c400100d10348014800ba15401d4401c540074045200030001e0f01c584074240c1200320007030681c8c43c1c40b4041d12284a910401180b601e2943c2c40c0c10603401d03690028014244040d20b8031602c081510300580319030180070720a07100140c2c4002443c10130700940d01c0103c0415810341c000c1c0365180306224410150b0700c54000141c51054104045400320f0702c42d40000b141c500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 607025638 1250 607024388 607024403
    0x12108120a0b010806060703082a0403030e19060e1327020306070f02190602120a0221061c06060506120a150501050a080702073f080301150903 63
    0x141640207000208049907181d40804e0f012400689175151810880e610254160b0380e10000c5e8881442103c00c6070b02d0004280c61052202d4505480d00102402031700066020ba038440c40061a650280546100c0441d040302141d00d2641b0700b400308940001c2d2192004d04144c3d100c41c20019111041d0b80201017405840f081503605856440e10500182616140301e4021410b5500c2520340751804d541c4100c0b4886800056002030305566008000501440380d4540a410094500480d4206203100380d081116074591b01540480d039400c0c20100b034906000d603078041403810000c41c1444030010311140d400c440380061812000280d4000c108081d00128014500034003c80c2c1c4032480c1200b000c8055000300e5030440c0700d51070022142c070803112508031103040f0f900c10b8685a240c03440f004130032503650400400c01c2d001d502c6202c2000815540c0e520220301c2041011308880521078041c0d00140e109000300d0288000354042d900000e011401200450703045451504050408415204e015030303106505501c06800c0c203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 607026888 1250 607025638 607025641
    0xc0606060e0114042702071a0f060102060c1b15040303021c0501140d021c0305040f0b0c12072901090b030102031b1b0a140c030601210812 61
    0x9600458080007404090320383e407408845a02c1d0039096030180e4031079515544d6843c1d42d24440080c0340e54102001400452025150049580b603107103000080612004c803420b092010481405c102d6480107400007400d1014152504140944100300e000303698000c601d1580d90341c1181036a070010000e10045080ca80e03a800c3d45440c0500340903009400c43c90449a03190402c078209024180c5070311034503040c1d40c03038410980241c3e041c204c1400000031501c0d400f01e81058651000030011036504111005040c4a0341c1c5035a600c50a00c9100010344000b41c2c04845c0c0d08100b80440d0209003004152107111102d24169951a0600e43c140840103038481110a5140b034149502414240000359466060300ca410900340410000e41003414201d210403112003000c1c0722018040d840c0001c2c148020701d250801e0040214080301440303615070400010a00c00c683d4200100c103000070412050240122010b411400780990390f00d000c022a80300140304480302c26400c5002d0a0008004140003522a41c08241d00d10100d079 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 607028138 1250 607026888 607026899
    0xa020a03030e1804150501360b030a12120b01080610090b030f0403200613020a0b28030504050a03050c03040905010b0a350903040e09070e09060618070c0606 69
    0x45d00f00c501c214281505180c000b00700645081c84a443c4458070b0f8244040800813403070b4903102e66000320300e0790409540b181500c24030f65400b00103400c0c020380210902c2c0743c0c800210302c1c050718620311504115101d504101e054610703680c00102d0a68011403d880180800d40c2011b0201c034200499003100126030400300900109007140c56119100754800d48410815181040000505400e2501559401d03800100054001c070380f24103620b00c030184043c00d40101552250701014140c0c010785514540400c09071841c41011540c040e1282400007030b81001c100c0340c14141c95041e29100980d8001e402e21800080d544241a010000c46001300b0040311f0802c982e50b120171049096610003207c4100184030703040018109040a8010440c25928410b0301c2503030480c83c2951818024002d00d2881d060000f40000107512522091030752082103400b02030014182071560019a290700030740703580f0300b5900410801c8000e445441490400140d408020f080a0f600c0210454000540e44001040617091600001300e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 607029388 1250 607028138 607028153
    0x90a03051b040203010e070f180b210603030a08101a07050d0315060e0102030c06130b09281103101e02090f01080712050405060f01080a020a03030e1804 67
    0x400c9100c40ca581e0714004510402c00040c0d000c01e01860640d4103143c40490700c818000c50010b8036042041c01c00c0e40d594444c2d01040e0741c0383c20040e4803030a0b171a080012203540414038285040441140b004038003a083c100000801d5680c011102c6400500c10300d600401c44038484044550010803a2021580121100b9141007442c1d07045640101c07107520442c1220039071a402402036522101c01c2180056440e45056021500c14508500541c1540420072071900c02000910040303210b00e0001d00301107040360052411415440004004440c00d4006025200407103d5542500c000340030a82034100e0950f0050928022051100c00f480b03925104460311000c46900e01c1e080f40d904d4120814810786040d1a0303e6604040c1d2140f10a8607038082c1d5030203108406503000307000240c0c210110385003014101207154000c0e01218401c1c1d40550f4035510603810060110b804002c15405803c05601400c0407101e00d41c00b2804500042c000141881400b006503021a1902010444504441c81c40ca00707590419041504 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 607030638 1250 607029388 607029403
    0xd050403120507020d080a0507080409021b0303090a081b0607020105060310090b1f0b070f110a030201121a0402120a0e07050901060e01020c0621100b1b03090a0305 72
    0x120401080c2500d504064018801d40d500f09401a0852146480d1603681d0402980300c4d2180034241300c803d105903030100311881c020740003504080740d00590b610740021403540c10540110001c24654010820003a03004000b04088000c260b0121126888800e11a03214602c0d01a49a00261501c500070401207801e134150405405000b00754251001c11286103000400e0b100e0b5408013030041d0b00200b0200f106110400000418580f4000083c400caa444403070042c042c0e0301001050310703e020741c8200082481061819802e03009411600fa10030580303140c2c0060086c40100b2a034820851780c4000d0f02c0741c0c0303040600240000c81c00082086503200003040703004400040945480d10303045e10b420f61314051007000081100030703a00010320f08840f580ca07185007151807840e450016411805103100c080419102d010280082498518000c00403140004802d440307040003c200307000d0f55002400400818203142c1c11a4100c02041e00e020300c440e0b840c040c0c640d196100d441080c0341c000003420b1000017400700108100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 607031888 1250 607030638 607030643
    0x80c0708121e011a28020a0605010806060d1e05060a1a040c020c101407030f02060604270302120c0a0c060309380f0a0c140307030902120d050403 64
    0x201c040307404091a400402800d018640070301500704c00d00c0101040d0540a400454400545e00c0640b0700c807510340210703821355144104003580c0052420345c20020203020f0355014003c02c5005011602d0680c0000c1c01d05a9013080c007a2400305040c4e1038912540c51060000c8241e9008030407941181882012400284224020507030696040740c280f2001e454140a41302050429a00504a09003504208642c80c0c41c0d0441a40c144590340d50180e074012400d102419805002c2e4880e044c604070614030180c1024801445544224600401389007407051040300d01c440c1c4007000407800c4a109281c94140e00e07210404021800075000421206803401002800980300740c851404004041c0d540c07071040e02610021003008002d80c20404a0141d1004401011a001030003034104200c1001408404024080f0035204244a84a41010810f0f0900d007802100b102c0c0c000b9103405240d40c6400c51036250103000c00780c040790405403580c0c001e00039903441d200400030344039100041d640050b0101001070231662062004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 607033138 1250 607031888 607031911
    0x7051c050d11031005010305060d1205030a0f0e120c0c1905010e06120f04150c08070318020114090d140c01120605090f06030f070306091509030906080c070812 70
    0x2e00c20b01c02000b0b01500e00880c8100c0c2e210010b282400019405044002c10903604551100441c4010038031208600c1c003050620307290301d030352030406030481c506031014803442020003803c1908441c04044006800e40c001001c46401903107070602e90522034100a014504594000400407413078a5000030400898121a03090b06c800c0920903104092000f28050310b014800205481c00c00a10f0011101e034240f40e10501c0f41d603d012011950100e00e004030b07050003840c0000160755104002c15581c02d40310b518001801c06e1041600300c0f14503030009264450400d00075629610220b24a11035466080018410641c40300c0780810f00300c2e807541e405035078688491001d400145208080da008442d244104825280c6c0507104030310a541e50402400c40e800040c080e01d4051041c054080010309090105001552040502161840c0381e401d2440e40f5100b0861801c0e03c0600c0c0c00c5c2d02200203500501400c3c2240e200c2e0074034840e55030703a09800f0320580c00344840c040c1000720000380100003845484001e501c1800b10b1000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 607034388 1250 607033138 607033151
    0x8060a0608010b0307060f0e0405070509030c0901050d030e190b0c0c1c0605100b0c0706020705100c021504030b070e030607020d1b080f07030306261207051c050d 71
    0x1c40c5098404015003542c0541010b042413100610983c0c030407070a211941070202c10302c0c12041c0802c040b10300885404000801c08214114580f03410b000040342081e00300c0300c2804650408000462201c004d040003020f0107001001c0c0360446e103036450303c01c01c0301c00000d8980d84020341e0b800c8044966031002101c3c1c500b6010300b01100c01180b0f8105041c0209800310343d00380da40301d080c1ea42c0e0f00d4000c05014010712020b1180103000503030412184010040d401006000d44851480c0540180c0760600c10f40200c1d21540da4280d844615a51100c3e0700305210741c040396895003055200c0154021441150400740c00c1c000d42004024060f0717000381c0b80400d04807054003115201e0390303082e43c1281c80320589c40c2d9400c000341030000d8042044500e01c840b041c146000d10b80712440e02a14511841d401ea0140d00224082074598804001160002e4000b030412145602c044003100740c2d0302e03070560300c582d0101c02d01d0410355000b264520911804000b00000000580d0030303420100850100541642c21020325409110704040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 607035638 1250 607034388 607034399
    0xd0503091008220321060f080601240c080a0302090f010f02071415070606080111070809040f09080307090e060402070506150f090103060f05010b04150e010201060f08060a06 76
    0xe465a109446034422009501c60402c01d440c0d100c800f0803c1a070810101c05002d1458000e003038900310500780110380000c0c80c20316001c40c0030010364499024101c20340007039004000321548214418184010340407a4141030301c1504040e20003858090700a0300501c80840c3c1386c1c5005400d0341c003d0407524812100080d44003080b0f401180c0750404180d0400040e00014420011628000815107030440014243d0700c0d051680350480081d13402010003a203040d900c4100c1080007400a1040d01c4020380d07030220303d40c07400a09485422180c40b40c4141710740150b0b45c81c00f8075203c1c2e420f10381c04045000e5001d00d4856a80c140524000c00d00303040c038040c031f440e803071050320102d56546090302c00c40e072181d54808094400c580d920700131161a003ca004035035070406032480401d4030301e43c1d600005034040c0d40b0035000041e9280c0d100841c84220352050700410702c80d01080009000c030b80c1c00040244c040008500e0a422080000c100407809010b0383e600c5081d650404074804108004003094a038131170181c10008000850b90f52 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 607036888 1250 607035638 607035647
    0xd1b38010b07050a0201080a20031009020901090b09032b0305060913060b18090d110102070b01030213060f0906030b0603070f1a130902091201060302150d06050d05030910 75
    0x1c9400030444d51000e940300005500965a1581c80005050001800707022040b0300111000000c411030702805000041100e0344140541d0034010303042040b402c504052000700041c000851034040c4c01c04169000c6600106984d04220303d941007600c80303a95217068004a0f001c01c1440c1c00307294010740031909080005070f06040920300d0921650000c20315000e102d1054030307100000c284101e2100d4000c400c6669160301a101003420b0350150a070800104003046c16003d0040010f8681200d44005074010042d841c0403401e1f030840705045d01e030110303007000800d10103626010007050254040c00c402189540e0000350300707525500040c200ea0050b1140640d9984072420903495030f955014130034050712214800c1c05400c1904042074001c007040e200280ca007003180315034a80801d8480d070081c040c0b1500040c0032645400c0c1202c3c2e54100405c2c5800a200317480c21540081da0001000101401e14031001c500032086080f250000c1c07000340005000a402072032682441070301c0c0c1d8030119606001e40340d85080c0305400d5124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 607038138 1250 607036888 607036897
    0x60605030a06020d0c0e0a12030507080307050403030807081003060b030c1002010c0e0103090203070e040807050628020a120b01052b06050303030903090f041b08070807020d1b38010b 80
    0x821f42d416207420900610701e0030072100f4040c4c00300319092003010002000000250b0107031030315445080e00c45156140041241000404180400810b0340034013581c0b05026102d80f064075032001c1e0102d00c0715041008603150261010040c2c1d84050103a45400c04d441d01035115282040c900e945034100341c41d00c007005506807080c11600039056403017031804000c0e065050600725002840390140c00e207005002d403501c07072400c4400d40c3c0244d007086460114030403c070041100ea081f45401542c05500b00f602401000c3c1c0403807180214500c0c50307511640b600340c103a841003040324090004481d000c40c4c03044001544050150f50b80c00d0340721000d2300d080300214592600200f035a00c500c03424002541307841c040d5421302c1b42d4404c40413680d5801c20740700c0b000c01c40c180c2803401d0f4640e8880310075601c149407458030b10780042c22404081c1c180010741d0054036000444540c8090091071080124160b602d4002140c60000068940800814000001480703040c0c0340e03c0c0910188000d500b84980300094a90300d40d008541036108 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 607039388 1250 607038138 607038167
    0xf030510090501060509041a070809062806032301020c120d090210080f06010e0307051909020a080103030f05250c21031206061b060605030a06020d0c 66
    0x10624200900c0c030919000141854840c00000c107550fa9200081804031605560443e2840c041d1000850000000b07844154000762034a0b1039091814001146078440340c001d080034801a0003070024001c400d40e01241e00195001814040001d640c1e24100320038210424018032040400241d044244a8014000d662b400b60b0250702a0440d40420340d03408425034440744600301070b103403910400300c096614103501d0a48491541c6840c005440e000b55800d4402d4001881c59040c0501c481d40d0044940300069110140c950a80340030185c40c590b0741c074400c09031040d0780c40090281d00000b0036651499020b00144e04a80c400d40b2141242c0349800c0081e0f516000e0242c0d0307600200d0000845a03210420f01c0a20140c15000e9502c0102da55164401c22040e42c42c0005a19000d22810402c4410140d00000030501d070f840f030303081c10020305040050003001307070012030421000500c005c2d2001081c405698440743c0100001400c840b40a2214030f400d40203908603090b00d1104615205820320b105000c0c0c02e07903402620 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 607040638 1250 607039388 607039393
    0x1080c0c1c030e07090506040c3e070609030b0109050c030703020304020f12030406090906142119031403070f121415040c1407023a0506010f0305 64
    0x80d00030020940640c1c410440700701501d840c1c00744500e039001d214070400740403100b034045140c2c54024140000d40e41310740481401c0080d1500c0d5042d695100e2400d091050030100b107414104c207035020341c0b503441d0414601400a14040c2c40c00014105401036420002c581c455480c5a43c1c80e81d031202c0b810115403049500981e070341e000700700146516100358000c613446031008122106405040c00498800360a042440e2619480050180481d6030452040801850301030010301c42242000740c9110802e038a20b8030103004250300054a10528040300c03120407203c0c0c81404907444242d400013100d401c440c2c03941040e808104200181030200242d041201c4c4180210345aa4400355030f007900456029005a142c0302040b41d40f24003d08003142922103444c021911072828054035110441040200c82c01807120b44240201901c003110007082400503103200d07680464a14211001115500000602c08a207003882481400f000c2d60f801212500c0c901c001a008000701c1d8810f2fa01c0300b003014141141c501003d040d55 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 607041888 1250 607040638 607040653
    0x50309150f101517041401090c0504060f03050709020f07080d060303080601052514030a030501170313092409021923130f080d02010c0201020717030a0b031002070201080c0c 76
    0x24001032250304a0b10550742c801c54482c031001da050864050000498409c101c055040040d0310340344c0200d50181180c0c040800089140d6952980c0d103082d10701c109401303560042504216034071070505403010b01f41c201c0680f0b81d441c014042c0000003032030f803400120701050418020600c6544200b0030394031070700492a5141c200041d07050716031b03110345603111044415100d22501c03c50141d0081c400341042407829140450746504000e038805403c542c2d1214201980e10a1281c144010070404400007292000034000410882001d0310f032440e03554400401103c5400e00310009200070007a0f004000c01c0e900740281680e000c0f01c16074101d03041d5904074041060003180f050600008641d280040041080c1d0030507000040340e48000b10011440554803203001608140500c1800310340a02404442d11036600c000c614044199580d01c000300d15003090740301e0740c2801100103030040d90568481100b604004007200c07000002048040d010b5800400e0490004071340101044400e0a15000d490144a04c0301c09042c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 607043138 1250 607041888 607041917
    0xf2d071106031906060903020f15120a02040306092d11040209190b03011d07020d0c020123030a1109180403091d04110108060f01050309150f1015 64
    0x10741d000a0241100f6070b03a258203500581c25203200d008010032680d20342c0c24081c2c3c84c600420058241d40d410080c003c08010140a00343c90518048980051960f54210402d844814142d00203000d15000100b0b19450400d01ca81070206210303005051b0348004c52041c00750b070311544981994a5500c0d0b07004203003e40c880401c806034500b40c0c028090105011303041e40b1419600180322030006000d60301c80c40100724004014454242303101e030a980070351701c41c41418a0b9801d00c010001d68032186500c14600708400750391406c3c116031044001d0780000060000003681c50486e140f0010942d4001c0d182500c1d003610b0f10940d00604880380007034a11501c0c0040c4102d01c801c8408910211180d80117008030200000c110004c2000d0802880d01e00755040b081042c1841454a4a4a00c0d9100040b500160520404004100351661080061b4009003001e10f856600e130b0320340364031440c6000c20b03901458040c030f84000c04000140d0000c4405a210f403401550180b2015500d0b00c00d00f044025a5013090001401e80c0000c0c2d92 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 607044388 1250 607043138 607043149
    0x18040812090115050102012a11010204030c08150403020a03080a0204090509010f0605013e06040308040b060f0d030c061d0f060604270302030d0c08090c0907050a03110f2d0711 77
    0x1d440c03150270a90441b014940546089900076002101c2421000c501841090702c200904009403906a0600798281803a85001c1d596402105000f030400080b44005107030f148440d015240108036001b414800342c1002035a05001e0b0080240c0344580624003000082d140d846000a1849109036805040c903e00780401c980000c1d00094016943c2c1c12482c07000054400820080310b4401e5010390fa03841c00c241800c0c03030700880f2040090256403040c5e5280000d5491503036800144103c003541030600b1080101c2518101d0080c15441050064000f01e0b084d004500f4280822809c86880548042d00c106507203190030002141c0c12408005144103001c21000c41803d2816201680140240112814403048048003025181001c8007000000c50703007401d105807244200052610300b1000c99044c105450084401800da004002108041544819402c500c03680e400040b1400654140c1d081603440648024584c403003280300d455110102050040142480303424019104035541c405841488200328204000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 607045638 1250 607044388 607044461
    0x5070f081308030c0d051005060f07031709030405040f06151101020903061e071d04270605011a07080a0f0203160c060f0e1804081209011505010201 65
    0x7124002440000808110290b01640c400c016001d00ca0b0b65852124036410181c3d50090030101d05010f41940034001d590b41c3d070b81501c0e448003145a0f0071751118001e041c00c481d1845a2112011401c20075424000c2010010000708260f4030156014032000301740e104408101c0c0c0c3c0c0c91180c0e10b40b084502c3d010740c128521074148500100356140026082c0004c8030002810b1110580d05070401c1100751040100c146082148a075200240342054940300360608101290002c403404080d100310b07500c45082c5007018500302481c4040b8601c0c030240541c0d44962070104001c060070300030140344950500d03600322400380d010b04031194164025230f054101104000c0030f0340d2017021000140c0540c0000c2c0b00880307401c0441c41007404060300a00507840c072540340031409044007000c12909010003065820509007070b1110700c11b800c05207c0c0c40c112040f1a0703903641001240350160540b0aa212916030041c030814200c1500144482a0000d5050780b405550301e006a0880301c4030212100e404a03042e204620341d49011b40c200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 607046888 1250 607045638 607045651
    0x20d03051608030a06090e030901090605030c12041208130c0b0a0e0316240c0b090a081309060b04051e040e01020a020a05120403021305040204090c2705070f08 70
    0x3644000c54030354407142c15810442e0308080701669480f04100703650540c025019240c0e00d540255245c00f080000013412240c5c0c9025010a009001004c100c60845c500c08072600d07800a1344614082e07080a00c2c08184103001c0e103c0c00c6001801440101e40424060106401e10a0f40001906507240ca405c43d8800c0c1500028100e0060221161000810ba1400d02001e42d401c4110662602c40b94105002e440e4482244235007840d6480c034083c00c810f5083d4200384101703078064001030488690342d0385441251600d590200002c0c010032003c46e40304000c1c1d0800c2124002c0d50b84060081c821240c44240c01d444130f0080c0c5c0f140c01d602c122051081d005c00c150880d000e07182c100e400f800109031600d5a020f41800e9078844042000140e0103200c140050000a2002401000083d803086282500d1758000440c0600b0000349079404980e1500420115691030b40448000c95028444070344050f580c00506900440b0100038809030504422400c130006602d20034184181002c1e01c41094515011038202c0b403050004008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 607048138 1250 607046888 607046917
    0x81201140a061b2102060109050702030406110c0d1a07140909090106080706050403030212070f0201080901090204060e01030506060f091f090207080310080d02070b07020609040e03090f030703020d0305 88
    0x34140801d228034081013491a240500d4162074140c520000e10b001e10584c0002c1c840c61030302d01402042c81c2d01104a80c111051031621003100c11100b090681003410300c00341c242d44a0150741700f003420002c44600100c80f2802d61318181c0f005541e640b070180e030100c40326994581da41800b04811410342c038200310300a821001c1c001c00060216120100245032140b2500040c0116102240400070907030304200c5241c000401095803801c242071a540e819a0a02104000381031041c0d220010780258000d45c48402c410f6002041404010b03918101c85803400020702050b110b902403200054600d080440c0d0b0711400590240c1080100d680b143c00d000c1001c06000307500e1030400960b0800140201d0180040c02070540615202a541d0410b280910f213200042d42c003403031a54015000703002941f500854840200d0f400703d1607480d91000c0034030004082e0300c1743d0840075030301600d840c0502c10700600000182034203a0040e42c0c0c240858110b039003015501d080d1484029403020a20652000103849a8050452030041050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 607049388 1250 607048138 607048187
    0x509090406021b012408010e1c050c0d090501030b0d02010c15020d110409060806040b0a020a111501090501050103020702030318060702100f020c0406030b06040b0609040207081201140a06 82
    0x109282502c0c29117403a422260144128913024030000d00c0031078020074698000300718415100959544801d40c40c81e011700c10b0300d0042c4038060764074000d50132110210100030507502c02c030f921004082d0003a00c16001c0e40340002d00d44110340c080c03130818100041501e50140c660790305040550f0f458001c0020707001041003da603000d22290400072800c1c041c48000d0300120302c0c030f140c5031410310344007900311002944000e000c0e41c042d00038800410f01000100da00614204005a550152500300351451a242c0d031091400c0d109034012030840f030701c2c401000c0c0e06030364604100f0700440e6a910011070503400b900d44040d500d60800c12a601c03240302c0b404d0b08610300c3e030009813000e410512070307400142500039444440b40105054580007081983c0c14405084612400c84041227500e04503107038401e03540001401e050080b07070351b01d00300c00042d5181c2041d00c0083d58000c005561b0f4884900c0c00040035005915820702021074800085900e4000403d43c030440d50001c1e10f0b039003034036190100840710703030540200b5541821482c10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 607050638 1250 607049388 607049437
    0x5072411030702210109060906050624160b011710020a17060a0e040c1508070e0d0f0b072a030206040209100503030a03020405130b0a050f03010e03030f06010906050909040602 77
    0x21b0903a03600c4c040c0400241c05034850030000705032a13004086c03e11944000c1c8000c052074002e0072094a20100c5030801503141c0f0542882d0a0380b00028600c054510f02e036a0000103502850001e02c4c00101c03e02c1d4068443e04040840c1e43c4041c3d0084000c03910200c0c0100440b21101100e480c41698040ca0040c81090306554075502c014164000b520240c0340030a079914144228040f2980350302c51200107161a00b118503144a008000448900310544699003030350150b4213200038501c140700a02e070482e80b252404d040400340035104c442075a004050341e850024045204020aa03014540c00350590060011555198204004090003e0481903c158200d00c0803555031003c2010b44038050351610010390b510704010400c065050042440c04c1c00d41d00b001c2100b691601c4038900f05c021034400b600c031401422000d9000a0242c00780d41c035030b40c41520002c002c011030706d1104840705004020030f80307480d0146625541d08441034810020b00d80d0704030710a400480c0000c0c4c41540105108a0800d40350f554800c080d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 607051888 1250 607050638 607050641
    0x10e0309010c03140c1c05090d0b090319030b0406060804120302130b0a03020301060e040504020d080a12051311120601050d0f0203030307180506071a0c07050724110307022101 77
    0x4604804164402c020707484030510085082506c8010380d040060514150100080c0c0d1270002503002801c222954001c110a030400700250350300309822004001a00c0c2180302c0003070040004032190b40c455401c01e40c00240c200d00805075a401a5000121500d20380c0480005501a47c031440035480a40b813491000100104410081c00040000e40c0c0e000d0b0b500d516281d001060020080710a0b84200c0c41d00c01888016074a00300242d10940d484802923840320061002550304012245590030118108400c205501181140c010f511500c51a500c401c0c0d070a40000744a40b07211448240140d40e4490741c010b200d28035101c03460090340782c444c50b107000800c0ec0030780c00b082c1107810903104032b40815514440039410640744c82840025010959099003080001d840c0c1e03543d0303503241a4241000d0401c0d1008187c1c166013440850310100d400008550b1202d81e20740f03c1442003202803400007460070002e00501207180c42981ca0032007c900303507001942414120340802c41b85040c01a50b010182180c001e103421105001e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 607053138 1250 607051888 607051897
    0xf0302071d0405010506010318020f0609120102040f060201020910181d0601112404110301140a0e15040318030b1612050103080406110c090c07060b03010e0309010c0314 74
    0x302494140c2410b01e03103070040c00d46001401031340c1031504040950409403a40b0041080c595011140c002c51190490041142d42c07040039003c6800885410050780300c014150010801c50b10211a0804865a0382d04200c0c00c0340903640c81c3c0c40e40060201c4948079280c1c4202e24241a500145119602d000d0b95400b03043c0068250107117410f20b02242504000711517030007030b2400d450b081c0c0078400340441a228020300100301842c9024641400d02e800046003c1c0306625851451071200500200880008101840385a4408441d0031042604055949500120110b40343c3d4545030040c030800c00c0c0da100c55506480040b8000d00800211100010000c04215450401c6000c3c17400e41d2211351201500d0340005150308070791007140c0039a40c2084010800903100740d003207070201c0d0300038580706a4081c00612000e06042e8054140d83c3d2025120044c482003403500c4004000d080e11600d810081c1500c1d000a050a0740c00d401c24024098006021400361540101015000e2500c645402114101d0004160304103410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 607054388 1250 607053138 607053179
    0x61e0d0b010312140301150903020301140f0c1204030c1a160207060c080316020a080f13080a120302030a0905061005040606110d03020a0c150506041112040f030207 72
    0x40c0d00040003482201c0c0f101440580b901d14000d50300f0092078071001c00318071041c4a1039810500b024903d1188600c501079060255500400a0100349600c44026032101402e80e5922034501400c1e010807480b141d0542200d00d40701600743c7d0758803d940d4540702583c51114410055582c0c65024140308204070707903555200c0c8a4003a0f400b410035a10070b1008002e01d0480c0384e412003024018114038200105500f041034950060000c041a016801086c0c012400d0801501c0020101b03480030a15802d2528210080d02c00d807280760b8000072440e42e03200d6141c0d075600002074001d0003c2c1c105003445031905109400071680b14000d5103010480b6287ca544040c43c0410484401c1402d658001c002d011500d41401140000c00c42840e11101c0c11001c804103d4503815030b030202800340b5a0000c0c00001c03c5000f20186805642c1203c1028482840304404501a102c101da481303205a00c0c0c000c111503001140810b5503410031240d1204500f99a90744c2e038011198010a070705605521450000181c00031410080c4100b100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 607055638 1250 607054388 607054403
    0x150207122907032009040b010c050615091005090703240e09010c05070b150103061805180d0c0b061206011d1e0402101205010f08070e010b03061e0d 65
    0xe082d00b0000c1c100d510741284c00090501c85000c401d0b50a01d00016982c020300100c6000401100010040e00c10800160004150340910000c104240c141e100b04113500c5803040e00c000c0c81e596201c444481c0c81c20704901171190b00866400109203211300c80c1d481000c0400311003c1c1100b14900280c0303440042402a40f02c2a028940541000042c807004c0c080e1160102040c14032a00b0000030760b4485450300e2000300192055503c4d1150504943c0c400c0e00010b00405a001061101b5800703090641c01401c0d048030040e05408403000600b500200c00114581c1020702e41d6102c0194500540d035419403801c2c090030b626445001d11596040c40041408414020700345000140504a40b80ca500020100c008000e00c04104d5103a039045805081c807144658003690407980f5000381c00d00c1e130400b5501500d03000b10302d0141c00d140c030002203004400c100b10001aa01300030708039a401c50b6251034a40301d00750240540c4031198010310100742c403410489946180d1100e03000710b500e0f840702d20001049040c1894002659000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 607056888 1250 607055638 607055641
    0x6020c251a0f03241e03100603050c0d1b030b04030816020304050d061401060f180b040501050d0e010903020d120506030309190b0706090b070215061c02060c010501030c1502071229 79
    0x2e146c100301e00b104c400c07620329050284a2554440907264501c4400b22030182241280c184200020010240d1500c5a942010715806850b4180b10041c04d004a408402145001c80030070411f03a01a4161300a00c98264019031405042606008116294034800c0368059140e0a08404070398840340c005002c0c008960380c2c4c5246031000d24005005081541d0f09440b400828001802805450740460b0142d48080c00c00c40d60f1900040d104a008280c20f010380c0c0c2455203800040c00405501060a1001070f62640c2c032100081d4290481d00e04440b401c0d0386c03090381603200700880640b5092241d0851f0320031460060541e5181d40c0c5000700c1180303a00060080f28469990114082001516459280c11840d9032006280716010f401d082d2001c0321001d00307040e108000111403030004486e0002c21400c80c950142000303880d13891010403507010741310030301086035008e60040c0045850f004101e00c43c105024194018480d10340b405d4041240c5260303070f03002903664054004400c5480341c11613200709400c01c0480140e0126 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 607058138 1250 607056888 607056949
    0x306070e030c211908091504090e0d0810241e0201051f050306040b1510320703050c1504030512010504060506040306020c251a0f0324 59
    0x201100c2e51855400085400c0304c24002c074100c81c007518100103080c2c0e8614103043c21000f4801203030040da8000403455050142c20700790b00101041c08143c0e14101d0316864020348518002d28620105406403001080e401136203081144e8081d0103204640742c8a007801c0a0700005240044440c480d00e05182d00035030b460700c0a20059a0010007403044060901d21544404c1d420800080d8644070042d0020340403040c079802103014200d0003c40401d00c0380c0010310304445040450406040706d0820402e14403164442d2441344040400c01809130302c403c01000c0e0342c500c1c00c042aa019146134100e110102d065114030180d4030200c0c0740217218903000b0740c003030b48850ba115100c401459000981c160000c0380201e06001080020380c44000644090769840800581c4a418441001e072904c0b030798241401981c00300e820b601029550060b20340080d01c1c5010107034032511981039a0810544280350218080c5402003001510b035406080e40305408081c40e500e08400c0714070b51070001d20070b0007455042520014020340c0c01c0303c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 607059388 1250 607058138 607058143
    0x609051e1503101d041e1716030905030609030717070c030c091d030a030c020a022119030503070503181c1d030a06020c100905010b0a0506090306070e030c21 69
    0x1030760810f0000136071645003a1b541d504500040c101c0107030b200c941ca0b071214803c01400700c0798034100000c000340301f03921036140c1e80140e18076112107035042d00840d000c0e0b940401c69040c0860854800d0710290000c41c034112860350307954022000303003200510420051100c40c00066030b403c0b40d90000c44c010155910304900746251001250450b05007001c5465014041c9800410080180c0300b0500c440e040009045084800680c00c100000200a60216010f01100c0d0360070980c5018034500344d803010807078141190401c1910901040f5a00c0034010440a000080c09c0c1442003004650080c1d2400050300c040103040b2505140c40902132141c04d19101c400c00740403030681c0c007130f0444100f4001c00c0803960881e28180c2c0480e07146c1074000b6026104540000d40e8000b812010000301010900501e01004002500d04105009041a5076a107120309000e11000a041ca0820107542e02040b00401800403502c616034107030350841c0303024192034142c0101c008000c1ca0b941c030b10910385501c4081011428960381c28140b07070760 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 607060638 1250 607059388 607059419
    0xb01090207061a241e0c0d14040e0a0e06090105070f09030f02270709080c010302031e0403030b1e040605010804120f0903080c010f05010609051e150310 67
    0x2c3c2c00907001d10005036180e6590310740c512110040a035651403603a800b140c20349180300b0801c0c24010b140a181c43c03c00c004e4034000042800490704006d80702a014201400c8400c0c040d82000f0328040c12042c8003d111403103548003069085200160300003464049a407015040100481d405e400a954034000c1000c056008001c03800300700b40b103103800308039a0b0031a55503145403070342440040c3c00342030030804607110301c007546006949002600f00c081070f2078503203081700810402c614000d0790210701407200108955402802540d000f170700c0001d8120030b40141007411608075100180203408150f04c840c00252180c40d0b4402c83d0005801d2510381107491200d80e8140020340300c0d664031943c1003006075801c00000c948043d6042024098034905245490090b500440c1d88100581000d80f01500002d5411a55481544040c000c403038a99400c1c01960707640c08043d6000042071007100d810415124081003104103d8408140403400105594140c0030248020131143d0021100300c4040d0304c0076041409a03903603205900307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 607061888 1250 607060638 607060661
    0x1c030e0405090304260a0c080607030f0212041401110409060e131e0507150c15060311060904020409050f10090b0a260d02061006030612080a0c0b0109020706 69
    0x20751904c2d20b041c02c4030740455011220103070b407500420450f11490000384101402e4036000368851b003010780c80c8d1071141d4642c0d00655541c0f000c40d2400b0720040c800f0f8070030300940320b590520580b011010303511074071442c416052602200b5255540d814401c2150803031000940003401c0140b200040e81820207443d450010006080030803100e140402c94400101c549056086a034180344094194000e5881d0043c98510302d90080c8132128030740c0ca50000910b91262040c0000c2c1c1c0900000f4030036840e0f50705400304655841c0005444100540e25440c51400c0c640f004107102c640192005180c10ba4801c00307102100d40686000000110110521000c8040380c7c1c0d404c0c000d00300f60602000b80c04403000000b0410301f158440c0d00204815140012643e00030100e208044036802401c0d03c0c80c0c0e03200c0c0704009440322400c60b003488411141c4000410f20502c04d01c22042640e40f8040003c50003c00ca844440441d0820320800d010030041e11812000220841701c094000c040c182c9015844003503500d070003804e40d500380041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 607063138 1250 607061888 607061893
    0x70614060a170a0224160605130201091a04210303201611030d0c0611040501090b091c050609010b0f0f040c02013e0c0d0e1c030e040509 60
    0x49042c80400822500942c03641142c030500c4609456803441e41981911a030100b5548010540c01024400040c240c40d0f040d125031000c01281d504c41c144486440c104880190000b030390381809200151301e554a00c082240d60542039402c0c5039880c140558002d10700100c4011080e0703480751035001c064040c01280381c0c103604110000c905000020754604c16000c0c0305a1007a0489014040c507003030000d5507020004004016003520503900030b84001400d0346100c000d00301d0307911746801416040d04c01c2c04801d8034113545e0143d40344a5200d01d8202d00c0002600700c0d8901541c09820038501242030a684181610480e00c62405480d1a24002680300e0031100701c9003109002e215a090840c1460b5240b030308443d002d132402c03900090703032900c480070480c0103110110000380f0702c0c1000b04100c080e02c0c0da00714190724041d00101c0070015044292145a1040c01120381804280c0d1155180d080481d02800020ba801d210181107507441d600b090320b902000146400003900800c0d04c054035070341241494051030713500020f202c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 607064388 1250 607063138 607063169
    0x615090c1303171c020406051c060b2a010921030902091e0109090b2d0c030a18050d030c03090605070f110f0c01080c070614060a 57
    0x41152104000c1800218190009aa1064900218000d03010b15008185420350000c0c1c481c80302c2032940812903c0019036481d00050494015500071102921a107681d01030a00c1600b003150003040650050100480b5183c90f0040340d581c0030341026100103010b480d101c1000344507a500c20706654842d100702045990510302c980c000700f00600e90702106014945a031008188145008400900704580f009600001010601108001c2411101c003550140083c10b0140c2c1d0746d92851350100d800340c2000401c04218032000400924066234207040311503601c0440c00c084013032859000d40e691002c483c401c1c1c0c01d0030080107000d140d510611829079541c000442c00f4000003050349800e5070b035800b0207134480205074507034245518540c460307044a0718040c2d110209100e01d0805d02e40c00b4190005003518200040d094050b03602c100100000d106625064032409403400320071010046070b030361000828000003280104080400150a840390307007101d01842c0b0000000e42010030400a03401e84690041820010998 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 607065638 1250 607064388 607064431
    0x601020706080705090d0303061a250203210a1707120b03010e0f0c03190b070c11120105010608090d0e04051b070510110723010213031406 61
    0x8124007510994100509a41e5444104544074824007020941001c1c4c0d2044880c02c03d03070540c2060050342c0003e000300070102d19180009500b0300400b405046c07140c1300b80c940a10926904510881701a00240a8510380c0c10090b4500c10000e032010005210200001a010002e40d8005603162901c2ca003081e000d00c560416200092150030f0901341d003940d140d03840f00e43c666503503025800303500c45880b85400c0d14000d01c07091011a481ea0085200c00f0b0090199605400c0a01c0c01d0000340114035900200e500c040d61107083c012103400300c203d038040342c1003180c54000c4481d0f0341d00c002041c10840b0001002041960500314018144c6001402c0202c0035030140c1d120380100c0390050f20000c44148280ca001446984408140e460151401c0800c0100f010010f00c0c0028802d001c21601c12041d04000300303000c00780480300004028858508040c00c02e0003040b000c10b9000b02e08200011305101610300160509804030038001158032681d104076240b002e4031401070700c4880280f000702c1d0701c043c540700b041d20342c42040d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 607066888 1250 607065638 607065643
    0x70e011212033207020115060f02010204050411130e10061b0803040c0623030609100504020a0905010206150907050a09081c0314041716080d0b18060102 67
    0x1920040c0000003020000d20840e110398888500303000d100745148070200400712003050000d0f07415400040c2d444410b0004401038014001c4132030052520141c4061189408400c40d0810720405004003195002c10001440d80d90b039018141c42d00d041040c40680d2108613401d0720702000040c1e800301140c5c0d4281d0080144041500c1040011660b06003040104070750302c800010031076250544024100d8401006000500034480303054800d881160f00c84c2044d42c0e0140c0d044401c1141d0307040890814040810002d00c440c1445500c140d00060f4a1203c581456142c02c0010300703176080902014006000028100074940e8100031942c0c01000311584e08600121400210300c10403401402c0340c050240c00507400d40c480340310300240c070300416040041d5142c110011074a030f04010070301146080042c2c1422040d0a2110650302010301680d4016240807034500d8507501505035403c40c00c0401241c582501000f030105003000010b0804810b801c500040c1407400c0010809001c3d0584c0b02c0c1100c0c1b180c007604120181c0d800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 607068138 1250 607066888 607066919
    0x5072a0e0901060f0902130b03040507080d020708060a0c030f06080c04110f07030c08071a1602240a0b04050112030314010803030f131b0801060602030a0e101106010b0c070e01 77
    0x5c4100545e540c40c001d40c031040503610590002504560002c1044117000c4003252682c152120f100940e6642c3c801d408049079a12005d0140c50220340042010403401c0209510030000014141004281401807240344021901160b101c05071a4000b42ca000c4110301d0240324883c014640c0301032040c141a504e0750312203070728050740b8001014811003400d0482402000d00c01ea407001030f48007281019060401c0340034082541c0c152500e0300310100e40c0010030500b03400440e540b151220f164100325000f9903035048014400601a04941c5032541c1c55007805c0c415155401361a020340403a28a001030a201440d005084624031003051000f8005a030050150101c0030044a0700a40d115205c0001c54660804080038041106002400c40760260000c00c00700240e001264100e544090007002160740c0c4000581e124401c001c2c1038000035414140101c02440e085007102c101418070b250141c14001052000c0c2e1030b0040a8110f4407044401080c0d103844020100004000351880d2141002d2a524003201389054604 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 607069388 1250 607068138 607068149
    0xd020703060515130c021b010e040c090b0d0614032b0315120201021204050f060708040b0412050c01020111090409022d010e0d020a030305072a0e0901060f 68
    0x702c4a0108100100c4408040140d000091419481c0c0210702c90700b000400356020840d0150040110a0141d250300c0d500d0f00450140c10f0f104d50b034135402d011080000034242c1c0c4a010303003840b045100c0400c940320f080d009441c82d215480b600049417810f0900c0041504a4070159034401c0d44a60304c80d0386102980680d040c080b01a00a005000101111040d0043c20400c014403001920350140010400041c04205a4560007038003503928000c0c07243c000860320b02c150f00442c1d4025040e108001214200341c0000c081c41409440c100e0306054855901e04c1b5a607129620485400ac50041c0340000e0040c1440181180002400200580242c2d00388421850240c083d06501c9207030742d071210000b5511007011501d10f00f10b109130201746818000d04100400c006d940403550000b907062210a00314101010f80007019500140800705c01c61450b502100d9940c004c503002c8070a4207800314041ca900c00725040240c40d800030210301c0340f0a14205402c0070048440180350028983c1090b10804c100280c03406000c081e9807 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 607070638 1250 607069388 607069391
    0x905010318030f0f03020c0a12031a03030f0a1b060921091202041407022409151306090c0302120606090a150317040e0609011a03180a060e0c030d02070306 68
    0x4c2030150003e01070100c02001c01d000d00c1032040104135611900300c5c800b907202c2e00d0030001c40038050600c0786441505200c0c80d400d940308006100c041403011003e4200300049240c21109690f1600e00014000041002120900d03112581c80c0100300b40021401e0341c100700b4030481c469200400380000e00c032152030b100344202c0c00318607005602036445075013207054140b0807804400da003414100802075a8140044401c080c2c4040352465818040d0400b100c035025000c0f0400401d861920511180e036481030182030708a84240d150511000201d00e4015180000c0c010458a03489a2460062204003c01d00340040416040541007003260307541d1010054010316091800540321841c01a888812010364001414102110405d48d031809a00c0d80200142c41504114040989444040c08025242030040b1a0f03c1095819400d4001d000e54001d95813182c805212800300c12600070720386040c02c04001050742e40507200c489500000b4420024007565100a0b4028a514403145900944598247c08001d1109 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 607071888 1250 607070638 607070657
    0x201050f1029030907050907020309030703060f140405011406090f1f08191101081303032003090f0601060f1b061508030c070f1a0a090e070905010318030f 68
    0x1020300300d45001041c2c6005240c103aaa00384254490b6072030300a0f22400740f0540900d000503003c6071011050703420000026004000b0181540d480c9409400409100d210407562000e10015a00d40d11400c0340c010f500600c000182c01c1c607500324070300c1c01510040c62203026108840522034032203400300b103495200d1004401c1b0501303503170580c80c4401d0314807c5500c03108943c0b0402c0032201c100c120345c0300d103214083e102c0c200c440c0290741e142c0b00640c0c10303c804039150001d0304514085000800c2c06034208803060f908840003101c41c803410307801101c1c09400580701c15809038003440031260380c0c1c2e4003088900d002d4004d40c20101644011524020501d288052000f060340301c0700c0e00800b0800c006500a191940d0420081c4030040b912102401d0f030325005000a580c807480f40c60070000e10070307607400155026900310f01c4200810421805084143e903114510502c00c004448d10000b80c0b040703840d04110300a15080c0d5500b030340180360070001004d88506144103000344a401c4464000030303412418915000800342041e0000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 607073138 1250 607071888 607071929
    0xf01140102010b03030c0c030c040908160602040b070312240603110c070e0f07182d26010203130605041b0305010c080f070c03180f090207030201050f10 67
    0x75000d4840c0c1d00b50503100200345040b148001081404a003401230b400c43d51860786802c00c0106455440c00060b0142c54100001c0e01503403094140c0c5c9864a015200140c5000c1d40c0c0c00c400c02150740304102c2640024582d18124003070310003502602045041c203c078a2145c1c59907000421151002c21710944050544d20408018205160300a448070008200155180135944061600751341000300c0302d8100000c684000501c2003405051061003441c0700c00c500032081401c248101d001d101807000c962840b8550a80b80405802c41181880007500c01700412850714091110511000484c614076003840c0c0e4010710800c40c0d4000000e1a400c140c0360082000f04160300c2d5804c040c512006800344903050341c40c00c07850200911030150000c26140796039a9034120150340f81e110740210418280c568400044005004502103845001c2651030085403012603220203070380d0841c118281c02c80d548085c145a401141090034150284602c9510014503000009a0301d029444034940624a0040540c00c81c5c65402c41c1d4003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 607074388 1250 607073138 607073141
    0x30d0615020705040c0306240f020f0705061303050118020f011d040207061d1f182a1d060306040f0b09070e0711010b06192d050703090e0f0114010201 66
    0x2810f460100d12541980b10041c0300600800c0c0c80410b0100e2102c089d820300c001c3c40040c03420141d6070020003030300c440b03407c205c1040030f664859040340d03800114180c0c0120102d9801c1c0304165444000c90b42915108036503105100f081303844604480d0501c002c0407aa03801000c1004041c00782c240b412200180e6441092403c41d0042982d1010125220340307030041c01820160000d01b40e0070f120010800075250319203c01d0710109032040061901c404002d4400401c0c0010000380e0318030030b40241c0c3d00021311304009041d110460407685600a44154034511070001c0500d545589032900210f080d0081d2010f480c068841e41e1214510403802403040005078009030b407105040c0b008101900741014501d0700c0f82051000201400c22001900300035510f4180c041c2c14a180103000c80310240c0c0d408000501c05202c0c400150f603014540081d4000c940b55601580e40c10040c070300401c0c130702840c85488545e200c803d0390400410259140d0004842e010140050114800f41034041c0e5044800058403812400f280800403170 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 607075638 1250 607074388 607074401
    0x27090504081905070312090f0b040c2706090b0f011413030303021801020129010212121e010b0d02030a090b09071a0325020a0b040302030d0615020705040c03 69
    0x190302da0790000d214180303030b520000902449010f581c84000081c80c041d12042102e140300401440300c1e01c070300c3c0e00d140042c201c000140c3d8400c0c0a610341d446443d9850040685c8800c060381d500000303c480310340c2c600c2c0c90000c900c6514003824074544100b10404550002c01c1c1e410104241da1810301c0b0120700e400740c240d00036904444520820111141440e540ca140c05006901f010385441d81603a55502001c074103510502c42e00c4034681020201120000241c03071407981c0d480ca8080c0d09070440c0140b0a181c002e040b40340004240060740001d000189240c40d081d0841882c3c00c508100041c0080c1000401100300303810140c58001d0242080181c0e2078480311704c40d10003400e80a10081281c02d610040288000010440d101101c01c15201100300c500e40140e651420300c001c0700c0c0c00383c802c10020f103886520b40425510140ca030406004031000b0070104d44403602800401c59044006900c00601400d55040030700030f820080c110114101c0310300c9900d1002035222129030044600032036030707081c48500840c8683c1000303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 607076888 1250 607075638 607075657
    0xa0209130f080a092402070b09120601080618121905040509070c02030c2e0215040c060905060307170603010f090c03050c0d08030a0e101404032709050408 68
    0x942e11080958003030301425080c0309070514000414212000300780c1210b6880c03034141790303070b07014021160030902e0b40d0341541c2000d1880c0343c0008040d08003400101c0704005141c041c21001d4020280e600e085e83c3d481c003810840c400c45d440a070b00591544810801a070050719012400c822840c185020200320890f40b07402580c2c0714540c015906000d11040580040074820818000e03016a40c1c6c182d83e000520600b10307030008075603c0c140d40c1402d80c088204200701c41080c15016602c15161441240e42840c400300c01c1c00e85017501c0c01140d0b20340400c94280c101c48034500070082940c4040c00d5151844003d800c0e80d504410441d10300c0007480004a80e5030382940000c01022681c1c0017001500c2c49414440051030f41800100d92a00c01c2403407542c00ea02d008034001e2655603000745864a51b6032100b481d0406000000100705180c0705c0d040044104507503600070032503101540c50703242c000c5180c2410004d200b2020104004008071460f45150a518290440c0b00141c074054080490107840382c0c5440c1c441c038031641550 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 607078138 1250 607076888 607076903
    0x6050304060f110d0f0c020307020f1203030f091501050f090702070f06120608011802060f0708180405070305040506181501090e100204140d110405040c050102010e0a0209130f 77
    0x400d1440f814400190262044400c0100241c2e801c00c0e5100c03080f255101410001750380300780310706801031400c60604008400043e02210508440c0c0e00300500e190419a48800844120030405c10f0380c01040005c203891081110701d2090b01d526190118480841f58042c15018101220005260b070b030080043c0c100400d8041c1c1c1c940d220640d02c920041000c0070160800f0009402c005000030349034814011010180b4028000925601d0a40c3c2080707444d5124090401c0c040d101401a40042450034010b04030502c4403080d81005813030300504200442c0c1d0020600e80070716107000240001309000041896000345101d0050000c005001042440c02140010f8080001115800401d841001e904205040c000c0082245c150300b41200c94a404d9015030f0060510141a81003c0d04842c5004000034540d07500451452054804c0b1502213410398004032030030f03140300704100410401964244150301c02850104080c100041c20796001070748103040a4886c4120020b000107203000d20080c0011402c1d1550300615 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 607079388 1250 607078138 607078151
    0x30b030115170106050a151115010305010b0117040b0c1e0705010209030717030a08060103110a03090308060103110702040b0117010f0e1b0316030605040e03042301020706050304060f 80
    0xe4010742140b100707070096480d5090040c0020941045081c401c180c50350001140142c1a420b04100c1d40103003141050520381c400c91049020890407108603d01030360040d0300104000c030030540054034480e6a15552945040201c04001c0031841c0f051007590020000d42c0640c0c1d0342c881d0310341c1704600c210f40d0b409490f42d03054000503080e0420005500600060205a0035201f100d55502c1c4400c40e4814081144004c94204010001a00f4401c00c0e8590384944141000a030b8080c0070702134840c03503411410612001c25918480d03c2c0034550003076041c5602c54024a418414007104100c080040c4c014804001d00a503250300c1c104440e40c0c02038001103180c6448002c03840c40c1d580d481e25902704a9119115000e00b000085010503840703140d80c9001020032080b66505407550312141d0001d0b1400b518408044100742d40d0380ea003c40c481d41c66024a04881c1c0100004546950410846464200c00e440c0901746800f085011062141d802045100480b0660308180307889542ea82040c401820002030030400c00340c5081c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 607080638 1250 607079388 607079399
    0x11506020c10090b12060f0103060b0d050424090c081f0908070b240306040209060f0f041e0e01090507060c031106130615080619020f16150203011203030b030115 71
    0x17010980310729001c40c0c22035074415001c0700540898055004091008100300300c03e140105040d0400c0c0e402c80d00c10700410348806010b842c801c6c3c00401d03170303145580c0041d217950000f41801103511341a40981010b1015005000d100c1d00503070b1858000c07804511816458921a20030710412a003607a003150382010f030003c1c142c54100351b6210031034080d41e006400034588180036122814006034951280d42c0c003908441c001c1d100e400401800301c5c1c441d401a40e0045450301c0da40405e4850b8013900b400900811240044c8492214088055070250808070341260f03d00059840401c0b00098a4804c40e411820458010700445c10b04543ea64000d40005105214100c103100720004400b115012550140710200038480081040d1540c0380707014415400700d5842203020941c012041da4840301141c013250f100600e4100805400e03803450704110400c40301c80d4091030f0700c2800d2010002801502c9901000210700d1036044c00403040e0031441c41c900c080d0405a42d80c512140da81c07800d50040c01400d030803001c0b8883d81369845 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 607081888 1250 607080638 607080667
    0x70c0501061e0602070602060601080105061b011119050c10021303121d06190302030705160b0906010b040b0f0a1728021e0d02070c060c05011506020c10090b 69
    0x2d1040f0740042c0b1038901d0001e0381da440440c049000381e505965400e940d0340707000c007044a41e4104400c0005650661501990391080034426030340c118a205480c07a40b18ad0994036082e141014200d81203042c4202049840d6a01c040412001e1040c030003c07000580b1484500c0105001523240d0b080100485030503440c00c2285a00810360600072031046c10701070046585142440580d0180d00d0811001034051040d18546c28020780240d5440111031600905041c4941c14803a0b40203800d1409560340e945100500842c40d50074403125016081c03084000b440d00345040c0c507600052140214000e10028041410446d05200340c6100c0d0a030005c4070006140c03810109500d403070038188500e1492518010000712000214203000740d441e80704250868844a110203104c51000358401000c0107440f580c204a08800107444c54007040241a50343c1c5c80b20841c40e07652411508645041c507049048000b016010071919074001140d84014106441c514400280c50104ad12040980c0c2c001d20811140414102d41a03483c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 607083138 1250 607081888 607081949
    0xa020906100216030339110105090a120221030706150f03050c030d0f0509040b130903081602030403170c0f010e0a03090e01050315130b0705121806070c050106 70
    0x1980101e48941203404000e101500c5613001d050494005071003803901289461f80d42022400c0c040c1001c1d454034900b0740010b810400290000c1248018441c4010103606000c004403a840b03007090701301500e01048420841d0f4a0058610050400f51124514114400030010004c01042010f84084201d503d07442e1403500d4102d0407006034041e104074181c1546052180082051440c45512010304e41a03c480c1440083d01458800c140c1006413000160542c0d0024814001594002e42d81c05025080420046c903020074005404011988180410b00100b03001d402c07600c503c88403c172440341d40ca50304c00d41d40c1410202e407900c10382c00c3765103041d01c0c4c0e01c411362010030410350780d500c42d03540c00e00c000c1d0315030b609100c440b5020f000d46905030b4404441c4000340d80501c1e4000d60003104140104520050b90b40d43c2c0282000101d4818001407000315044d170701340c0002c60034103800c40381701c2c1d0701110000014000c00c0d55515004140d40c0030490003441c82804e000007903104002810080562444e01c0d9070510b00030300c01154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 607084388 1250 607083138 607083167
    0x609310f0507080106082406070b010609061e0302070f020d060b18011d06120307030224070c150b031608060106050309030a030c03111b0c030a0209061002160303 71
    0x4000002d0480c070301c5046401e0598070561641d80058454580600704110310149280321900c40070780c1c0d60720664460001e0544e80f44540b0a40ea115810098010045050b07907020005100c10540c1910100c440c6968410b030314516440c0050725000182000c2c1010700086c00041d4101200e001880c2c244107c64000c4541048151044482c074030032072a10b0101c0d25009d02c2014117072003d40742408940c1da1013601c03140d000b01c0001e088205580c1310700c003c242117600861044001d60301580407100d8981c11402465040c45104886481514120102800c240902c0000404041e0038409a4800203450741c818080f4020180484103080d0b091b1450700181680c030b00501c40c02d44240c1c030000541500c5101101c0c410904c01c4003550a0084400041d0081d010f190001400d254030360300401035440c5940f018050714800048a41180f0090140060034404911000ca00a40140c807003000540c035044c07001ca420680075100c84422204058040703082003007034100030681a1181c035000080c954000480901544c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 607085638 1250 607084388 607084391
    0xe0409110a060f0e040504020f0306072a020607121101140f0c0924040b0c0a030e0f030309091b0a0c03020601060804030c06050702010b040612061a0609310f 69
    0xb42c680c003060321070b5804001d4440c001900003000c1c1409041079002140c0251002e408030340c000741d102d0300190034950304030740d5a400035844038401074aa003103041c0c8ac2c0d81034100355004001901a0758001c205503200e40c8001400d040800d030701154141c3d208004070341d9600d01b290000c002a800e18a4141c1c404c140903610231043c13880c88404600c20a40200440c1ca40c084c0c010100c1c0e200c0c40e40301c0c03455407210381e54130940d200b040d0003031100050341c507000340051014844036005080c0604076440c0190898202d1040d080c02010380e41d40040980c0c40c004200c6603c4002180d280c03401e0750781c4004411100070100c4103a0301c60301011501c103c1ca107400500d82540e551194094613010fa803118011a1241c40464003c4d0000340000381d01c50100742954803080c0c1007241880089240c0680a020405403140d550002c003204003414480d200340030312489052544148004100011903c82000075228000c0d900e119109581080f500006480c03041c88401d10054a640da84081204001c0300000034900c040b03025502030f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 607086888 1250 607085638 607085659
    0xd150b0a051c0c2610053708061303050f091f02030a1b0c03030809030714061b09060405041e0f0204050906040b030615190e070219030c02060304030e040911 69
    0x4c1990000748900c24082c49038129502e000104070101340c403200801d9a1200860101c001c0400317002c0805880d007c0514100e0425242007000307450b0a00041c2040c4000750304140c0c21000030b5102c0d08541c0c0c1d5213240c0100300c1d03c0360700c108005201c3e0428500c0036440b0094101124608640210141413440807a80380d039045468500c0780d00f00d0f601801d01004166602107074040c80043d01856072160408000e804a030705010059076864442100b2540c070103510f40c40501000030b21083c182c0d4500495520400807810314035a840400d100b4000c2e4001c00d4466901d401c0030702c2d0100c10505814103001c0c600c50b802c2c8440359401c48000000d50260140ea4000c082e1000000d0708c50406010f030300d44495010f0006c241a980300c0340100790400ba009400c0d50701c00c0300f01030b0102010345c4c501400d001034400e00814004030300b0955406031507d804005052881d5580401c03003130200740c001c0c40282d0500c0d0140c0e94299655158034003220345c4020740b05030381d5015141c8445c2c282030100514502c224220f054076511601d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 607088138 1250 607086888 607086947
    0x2180907120614061207090906020906030a1a0f0d020d2f041503050618030405060705010209030d0201050105101d10030c0305070e0f0d020d06020f0d150b0a051c0c 72
    0x2e85d07203040200c94584c403510041000c020580c1c0450050743c068000142070512001c00a21030354029112001c90741e03241c071083c10250700c00b2074404240e01800c80782e0201102c00040850211107407182c0291107180240508402d0041030055540b00c0010721203403654010054030500010f081a24034039024a29105000140781001c801610030740e80c02100078000c0359a040c0b81d007205040340c0141c60752240002c0c81300240300e40307070000134110070f81c1302c0c0d800540c4605484d400e1501d0003618819240c03c581c1040300401c0191a10540d0703894055040c5041661421107101004481ca00483c0d03a6402154000412072207650650060740404d0103a0f400380116150301408803100302c021012503034041403d0400d17040b1840c0054403181c00601c050140d204821440d192481280c111012088c418140061031a0400c40584101c0000e004d00320030040e450b908216001a007801410100c0741840300001d03008503201d44000d440b1981d210880303000e0000341074080000742103020144541031812220344441c400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 607089388 1250 607088138 607088149
    0x60c1707080408030112020a0302030706020a060f051308072a0e1509010b090a0302061209060c0304050c2b0501020406030609020702030d14211504090218090712061406 74
    0x42c5800c000201d0641e4203100740c0103407800e045803049900c0302540e007000006803014032a25000f41015000b5150702c441e60704048054443d1100c40b154994504010440d282142905030142c050300101117039203822075881c20064001811403010800000094501d580c0b41c0c1e514004000e44045024130f00858072203003c650b00c103903040c4d0443d0754080b050a0051240d42c140c0c0d0003400101200a0840a441c1c1e81e035000b241107a070101089410380d080510030400c404408100303d58026040000192071407a0548801e0303290b5110240300d503c10190303000316080c0307200380740811034031401c00003600d990050303091502c2c85c000c1d40603203d844046405c10300c0004410b40c4030700c290f509941c0c001d03015040209028004440100c5811050140b4007800e22100000c1c07400c0c06900384903000101c281b1042428030025003c100740520341c070070380706e01d080ca00d0440040c2c072032150945940c0181d00c07090b00d02c0d440c0c11084030700313000e4030381c000441c00815180034806100f0303140c0146803a030b20340006144003902c529080c440c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 607090638 1250 607089388 607089391
    0xf0c020307050c060c070b04080304240906050304210f0909110f0309010618020c06010e0411090c16050a14060103050307140a12031b18031e060c170708 67
    0x1889070f004280d001e880303820b008005090310f04104096400260b01c0c1c0124a5494120b43c214030181e40c400700c2e003480080e580402c414041c045000824001c02e800140047c4114151f0007401300700000480403c040146003030551081c00e441d05000449200324900041c0108080d19403100060381c1000c2c002010303562403282c56070302d4401a0f16540751418000e46551558009080207444c1d44d03035914001075080703500d01c030781036595a151805a40d8a500e056503d10b44007040c6c2001400c00070f00c0b41440002038403100300e0100103000303682408a0f0f030344051034010f44d80241c2c0c1c003400460b1340c05c0a00604129002c10b87d2a1340501c6903120111440b6818004d5541c1d05003408001c10640c810001d4101081000030000c402034145811035040520070354940c0035181c8150291400b29072164540302e44401000780c59410342841e032414941d000c0452200624000040c032024200c0915680c1198032000b1250301903d00c55007150041c00080b403d910001d01c2403090100c0e0f08401036a00e000310310145d20405005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 607091888 1250 607090638 607090643
    0x3060902090120030c19120905010c021905130f0e06060303070b090c1302030420030c0103091b0f0512030f03070f050702090f01050a0605130b09060c07090f0c020307 73
    0x210311030032040f100f030807404505802c0b16616100502201682d00c0041115040c04140c8000100382008070b450305c01c0c400d51041b00010280044201300b1300503640c0c001c5448524a804039403860900c0f80348a52890484c82030b800c4a80c019100540035000c010701c0360084005140745e0302e01040010595102941c440c1c00a85e01117a041d04104014808143d4544107180c0010800301910029481d80001484818540c9203036400503401004201c144040680b06030a507120310006071512904200c00651a120a41d00c003070b040c556031740c115405104a140004400c0c12242a00003c05034072400c1620042c00b1600c1007902c565003440b00c044603040c0100544d800100482522401d545440c681030750003501120300141041410312902d17000d680c0e01c00703082e400781303150001c642ca00394103010a0103101000341d045402400000c001c000701c4c0302d040621003402c860071885250349038507240e00091081e03c42c2045000951041040c08aa8403006500c110700c03603e042c5030100701360640c2e08001d0f40ca90151103c003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 607093138 1250 607091888 607091897
    0x6080c030309030606040b03030412030c0b060102010509101a121627020f0702060d06050a171b0d020a090203060f09041a07050c010204030b1602210f1603050a030609020901 76
    0x405d1321303410141c0150300c1d484001000e0f80c1c01c00e03442d50b0030095804134001007a40001d21301c54040041c030205e015541d07048082840240424a0008500c65a81e40041c0d1086101c596504460401c64141d0428183c00740d8018800e6994410f07081010741c0e920160303104d61100d42c0589100041800122072040c04440b403c0c2c80111320a02c0c21a03a101c0203400078200108002030130000b460042c1d68080040a080a004c1c03000690740781850240b00c070005090704401c2c00d0701040b2640500f80000021051504000d00780d01401c0c1c0a4240b0100f001d044012034025040601f590b00070400c550300e03402440c0b040344240c0b00040c40b414602c1c10082e0800c41a00d001d00390010030754184e403051400e21803060f4441e41d6030409030302e84050352003a642207130b010381c0c410348400018005204e1400c03e0030071040c224200750b200410141110300820300000340c40c0070fa6200c140c200052804e400c0410340041c1d84400c070307103d25803000c084c0740e504028105600405800c0d00281c64202c0110b40080c80340709440401038182e48 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 607094388 1250 607093138 607093141
    0x60f03140601060e0306012106050a05100f080c0d11060a020307120c020d06020a021204080f01060504091a0403180603060e070903052107020307031410060e040803190501060306080c0303090306 85
    0x2403d07004800e4220b80208c4e040c5000802d00089076250103a80e0140b4034072040040c0901d0b2810214124828982047ca4400143c6808016640d0300088080c0107000c122400400305a00b441c0004039003403061580703a080000400e04c0740350a500071006d0080349000760440500c840045600b02c0d426400c07200000d5124401c05281408500c461b40a00081e81c10b5004807207a50315a0420140c00e9040390340500c4199210b1040798900308020f005400050038169800d03c4a038859540b07494541c0119901d0900c01c605da60000b40c02c1c180b180740042d0345552224a000011a200c03d0300030003505440c011409107030640000f04014620503400310085907080000350281c4000c3c04901d4103990101120103079400310520641c00540c0d81485000011440746090704219103061118a00340f007244a5240c503071524007401000703040e106d8528158029400480640d232662040e2100f401c0e1407442c454800c01501d004000304045405502c402c05943e07591080340c01d084076103400c00d80e0380d01c5118062034140c0c11200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 607095638 1250 607094388 607094399
    0x302010f08041e29010e0a05060105041701050703050f071e0509060d020d0501050a080627030d140a021315050c0d0903210503040f06060f03140601060e030601 70
    0x1a49a00948a0701481190f00010030041c0070081d10712405039400e800040003001c200d14030403241c00014491102c210003961504691480c5018014018240c254a07407001403610b0f8440e500310780292170a020307040005194814643c0c001e00c0d0840341e100210740b07844c01240e4140405107410348900040d55946030301501503010280c580c8110301542e8107100c4c4c10f000310003d030b0381c4940c0a01104805014010784660900101e401981c0e01a803005000e1242c03203030140309a0342d0214049501101086075070282c000c01030300907510f80c0b800707105e010ba0030300012070809070310001c80e00b208450412524070300c207590b210914444101e100e45280815482c040180c2044110b24000b101d45070440f450900c24248054540c0c0785040c4018a034240000420881e018002c100c3e0b4140c0f07075119003810003002e802c02c0d42d1690f800b40c000c1c80060006800015841c8103401000150340014010384414000c40290541c0d0f460013020701e001c0159041400d000c0c400010032411311a103103440c0c2d034180040003030001d030340b030710 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 607096888 1250 607095638 607095647
    0xe090c010e0d0f1b03080304060513030207090b060f04090c0807030c051b0708120316033c0f0605120c0306072303152d0f040e0106080607090806010302010f 69
    0x103c4210340f8400d201440800c9011a00000c800841c001c200c156940d207040c4c03030000c08071071000380850414071117005640d020a40c0020f8403400e48032a042c00061864498002070b8003030084480d2440b2414000030003107a000344075081103944e40c03190385517108507407070301c8205400755a07000c180c83e00080e40a00070701d140103100342c4288030755031144800e8800090f00d41424605040400b128090640b01c00014802c0c1c0307074800c0b448103020080d80d1408100d040394111249000404ca6080300500c1c10003082d0114015181c02e006240540e44090b04001c3c1c1049980e5034800391149110b180e20550000340468018070010602d401c032501c0003005411140d079500f0301501c0740040c030070300d403400141141101c0803a140080010f5000f416045a8803007000740103010404926141c0d07494030340503001c9c01c1c020b00c0002e007103d19414013081d00f210501001500003002c5001090010840b00c015070808800140c2650003040b041d00500f00d6983c2d40c0341280e00c5482d001d0343c3d00d02c00c0c0301c001e000480da64503c4254a100307 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 607098138 1250 607096888 607096913
    0x507120b040912090e1503070608071b0309060e0103020313080a0212071a090307150b010203070503070b07080c120a090305160c090e011404140304050a0e090c010e0d 73
    0x51000942844580312000288101e00c2c01c10081410b01405001085d13440380450f901200702d0507007101d048591408641c44140a02c5903000b40240385000c41c103090702540c45404040d5600c007940110f01c185003801420f410161007160041000004042159480781c000c4900c100c940c000d150f194203059944400302540440d103500114042d0034420fa0101c03200d0b10090414901455901032100c041801c1d403205a007005c0c1c4180d009078010841d13440001c1c8a00c40030001520701510000d0070841940040c0d0961007040310080c264040004e0381c0c410400c130040418002c8100381d0300c480c405d60f10460266114407801510b42507141108000a0024900f42c200818452003840c00a0620300c020421225802004400300c854102c918014002c004c95807040140c200310980007030019000c1c2014040c00e4080c003520252005400030014008000c0800444000f4480a0040c1d18407075500c52403011446015100444107010710301660030290310811000c0d10a800040c42000400403e90b80c94115509 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 607099388 1250 607098138 607098161
    0x23030f03040206040e09010903020706030b091317041805070c2a05060d0b040507020105070903020613030b010608011d06011215051c06140c030c0d020904020307050418050712 77
    0x10100400b0445c41040303100940501500400030030003071100d1074040d0510f17506801c80320815241000f544081d43e28007a0b81c0f500303c0307000e07050851607003e40e0400c00624001c1c0b05580b030b00080d000a0014000d2850003644112240c0c2074010030498545603800c449201091201030100c2c11800c244503d00e407503109050304094428900000e605550340c02283d52604161424499296030707450f11105030504d8000c560b440680e91001b00881e03d4844005880031100b070201034001c2c10041040c00340c102d264011100038603004000c1b0031003582d58480003026183c0034000c6105443e01019405481c00b20f581205000b000b05844035a1a21041900c5900400c0306191702450050344a0f00001e4944466104405420800f40c01d2100400b030fa00780001aa001b41c4c12500049510104002c0ca0b00e4070082074a4001c200d403c100c1d0340d41c0e0b0144c0c5046002e80901c2070840e920501c00001c0c40309403078000300100121003030000c10284010081060300c080715402c0741c0102c04141c0e071200440a40b1038540c0030012264 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 607100638 1250 607099388 607099399
    0x80a0903020d06060302040b2b1a0a05070f0201090803070302031f080102180d390b300402121002070b0109050c0a0e06031302130923030f030402 64
    0x203569800141c002c0304044410b0b01c0f400c0e60f600c0c00384154140341c01a00300c81c00041d00c00007070780c4e40300e01c44a90b00365400300d00300c1111003075200c01001001038050700c2c5041e070121003c0d1030106040500402c0002c00303092b116603020951341100d0605840c01805540501c1d600001103500f142e8034041d042c7c02950004251141420510300755503a01c824111440300a0000e0300d00050716a1201d4116001c0700321144100e902c41c00c60203451000107070202e540301d101c0171303060381980940c8850501100c2002440c4c0a0300c4030b1060b0024004501c42c203030b0348040c12101c890310a088002507031030020980150f9080003241c41c1018100002005810403101c888429000e08040360440d10595420b28200c0e08010720462b0106100d5004015084003070203115080341c002e0581d0752415900080141036401c83d800001d001d6000480020080c1a00300d010080761740d000703812a0406040900c120707004101d1904100c8042460300300580c0c1500f01c00d0184403442044400940c64030100301001619900000c00481e4041e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 607101888 1250 607100638 607100657
    0x12060a03060507020f10060f330210050604050f041226061005040b04030f020a0b0c060601080f1612020c030c0708060912030f040303091403090a0f030f080a 69
    0x950180b003280c1c07044200d0742c00fa255842400d03d120b07090200541c00840c0003800c00c481808500603500c0c41c0c004841c01c082c0144409480c40da03881c982c60302d031219000c9c007136040030060040d29500031401840120380c03800200002d9a8850801040f81e1044d14024050100000014002080400c500d110406542010300d5aa0b0601480020704e8040e05490034005203008107002e50350a203202006114241c2e410f050b410b09081909410a50065103c0984030140070a03100d0f056468502c491005005481080c039500d1a1030360009035542c00c1503404d6070000303080c0070005807055400810f60b4003905512081102c070305103181301154500c569000003644550701700803410701c0420810051150141c1c140c0580815841d1825003828810020600701180e0000380704c010b0301144120031240d215492629040f41e686907810100c004114200c2c004211144a20100b40181c50010240c607941404032400c0045a845160780300400021380710040849406601c84c0002400440150a075840c40e460203044c03c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 607103138 1250 607101888 607101893
    0x31906030b0402011d060412050c090705090d06091a04140a03020d140c0601080c150a0807030c111f0c09030506221205040603060501050a090302101403090609060601080c12060a03 79
    0x1b01d910950000c8540c0d90200d220304108101441300380308209048819a03954a003a0348042c08078483d82c080c091007560b4042c440001c00a860303000200c182d4002d200440c08928040103d6140300007540c0a4488510415812560682c00110100d4450740f660281803400700109082d00c0c111340280c0f012910140c03c0c020820503810400200307000b0146a4014105151700b00180548043c1500342d40d06200c00800400078440d400c0304040360051524a0001000020a082150000c000c1c03140d03443c5030b0146201c40203143c106034174204c1c131410304000100301540c144101590010032900c030003030041d00910005840058000d50b02002c450311b01c1e45000480c0f03e199210381d045848200c200b00442c0c00802c0a201c83e9601d4032031400600402e007001441d03c941903130301424a040718030009201d8025a61540703070551045514030010780304030580340c1e05c0b400c240c1200e94442d942200c40899520403200001c82d41d40c45030400501512503850340620709450011501500301e0004c00c101d81141202000000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 607104388 1250 607103138 607103149
    0xf1e090b0418050105060913112215140d030206010b07050304121b0f060509130e0a0c031506030c2108070605061009230310060b031906030b0402011d 66
    0x14018483d02c00081c0a1501108100ea541c0b03014003050b40746450b4480c404000307049002c541d1010030044030182060807005040303005502c00300e01d070980300504000c02c01c007003044496400c10582e12940c403c81c0020b40800103024036520440009001680000c0041042000c02c4006165450185042d0703890552280201580c03408070301c3c801c40f01005103044003071680041031031000280c4884444201a140703003410041044c02070b2950b0501c9401c1183c0f59040b041d8466212044081c03481c400c0c3c0700c03201070300d00b40f14082003060304c8207031002145041941e508518038810304064035888901c485c040b600f4105d99140005e00d0068800b203642c80102503c001c12501d002501c421344c4507410104041c07414005010003500203598800500050000c20b124070065a40081d1141010001c40190440041c0000c0e1518a15201d0a943c0a03d4018007007215501c9000661041c168540780031841030441e1600400c81c1c0b40b9120140003e81c1020200e40150f10030409001c0c0c2a180c0c014002004040c00700152 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 607105638 1250 607104388 607104431
    0x612011b080f060d06021324090b040e2a0318010b150901030c090f06050a1b050d0309020609090a0f11090d020d02130f060f1e090b04 59
    0x20940880310014402080d03021070710703942c0007901d4015089103042910120f40c0c401d00c0c20500070f0100d0b8010820b030b41d4001103070040c1002002a40c0c5030a80418010500171000c0c1d070030390002c20004803c1d08001c215071102d03800722411aa115895035581d5980e4215200b200b1030644c1804614680e1010390065034000d0704e02840c0212200312243c142401800205401c40f07200c10301d11030040001c0d240c4442c41c5080b007410384800103028200401c1c520b4400310100c840d00125004074510240c200c8010030301d564042c000e00b003110311507151a0341d5072a03c2ea80008000800030b01c002c1881e408895281c02d4507220748c01400b2424400b408003810400070360000354001c0da08031001300105607101015a4800178034010407580d85440484a071906203a20b0110303c3c3c0d444084000ba0180c843c0391041801c64441034001c5441d0040030004101e0710500c0c03920400600814441d522056400e80c402148001103020315000142c005851410281e282c00300180140c6102c03c04140d00942e00e04441414810000c1400e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 607106888 1250 607105638 607105661
    0xd1b08030606071703160c031d031e01090221071a12130606060512060904080f0f0703140a170601030b030a110a0b040806040602070f060216050601050114040509061201 74
    0x35117900e00404205481c2021082200800c4261500c010119802a801c646000060035800c41407003032800120f0b03d0038800c40240c8208664013151a00c05500c11740c05054000d108807000350075048000c81540d401003030141064001c0d000910204500c4031741010f40508060310f16092070170306071040f0b0a4480f520b8111440e040350086802c0200030800c4600c1204090800b40c1402c0c1e007441400200c0d0801a0030042401c0d0080f04800003080c14041c0e514243d90f441d800d020606a941c4000d681c0e02541504180421408940c80d104083c000c101003400303550b6030036203a0b035035034651081c15452007511210242030a07061503910201c85440c2c2d18180150301103075004410302d80c03401c8445805c2c0045c442946e403001000190a2000340800c000c0480c0140d00a60081000346c1c03508042e042001c1c8609a2050040401d4800503516000c0301c102c007550f001d0140120141c0e42c80340c0c1d07107030300555010031381c85042441150204018441486d0411031590801000303044110701d9600b001c0b0203400c41c0c01d402c082 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 607108138 1250 607106888 607106933
    0xa150f150803031e011206020f0408030a0c050c040c0c060b1906050406120e0705062b0b040f3c0608030417010b0303070f0809090106030506030d1b0803060607 70
    0x1c00071301380f41034400305481d5044081100000c3d0b1600e6003118024010311001031200741c001030030300c2da01030441040d94050406a070a807684d1700b841c0301001c0c10031110840201c4940c0611000b1280d545810b10905002c00c81c0c580b190503140c036403596000c0090100c4000c81d42d1089403101031483e2100360b02113940180c82503869444e0340e00c0c00c1c59005012480e034802d60300901410f210700c88480c403001180601c100d0703105584075034031003900e4100100d203201c100c0c003440c9034040820810500451550002e42c0628000e079810003c068014411405449402003141d441c002255100c0028003e41c24005030009a400032039903105821201382426125564050842940040f405005015251030248500595100204010b540740740211b510390160302005070a00c800180c0300e40901c203110f4200e80b40c81100521030f040541c3c441034040c0082805440b40d03030080c07080321031622600d8025040085404000f600b0102e08601642d40c04140340e00003058903030450f50500060002920045194a20007030a026 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 607109388 1250 607108138 607108141
    0xd060f0221010f15050d0e010204030c0902070b04080d06210b01170607030c05040513090302210708030615071a160e040f061518080a150f15080303 65
    0x4581030301c15000350000000142000104003403600300d074142048508035030007407640c803a0940d410307103942c02510f480c2401141804080c1c003500506600400980b4400d040311707030344c045c0c036003c00104a000d4282c006060103840004038010401243c0600440713070000d140442c080d0f4a03240004945030310002a085480d04115000e0f04011000c40010701510a80b0007107500c450030349004580d00c0c240905142d0030301d903854801005492040c02114050140640845e41c4002e0001c4600018040520140c00500845100030a0745042900c608130100c4007862560900925482d107132003542c00030304225440300d200032000130403002c081b01408009000b82c00f06209015020b1000301180c40040026a02341d4654021000840e00010005100d134410303940040c0000200d64440010140ca41007564a0546940700e031070b016030b1084440e540072243c00e0000c1460365036035205595440202c20024000200e451051400c00b1159000710100c2000550110303010300c3d1880450a41841a00800b1040d0030000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 607110638 1250 607109388 607109407
    0x2b0903031a060c0d0302070203150f1b090d031101060f031b0605120a1a03031c1a010203090d0309030c03080711010e03210714010b1806100c020d060f02 67
    0x2903800044640903a200383c03a042c00b4015240d100e21a408100d4181640400c110f0300b5074504010300541c4c4c1415112404d0142010301c0b403d82c540e042105d4942c0344601d0000540d45a6a03000f0560f1030195016182d221180710950f801d84046c070042d00244a90340d6240c0d0300050350420009207a000314041c0030420b5000310700c10138080400b000c541240c0180b1a003040000b0090401286040d03106200703590008100354803410780b005c02141e0240256040c0f10210344140b03000e2324070018626580005104001004111940021451004020781e01580081c0329038429400c100501e120058820319003d041103031030369100b07034440d51150000d44005101040c0b10041008a503103644001d031090a00620702409600040c0ea1450810003580324070700380281c00d800d825803040a482c1007684c8003410341c001c10480380c401c41c002e1541901a0b4401c600088160001600d00e00140340160409840c5160341c1c0444803041d01c0c5118040760407038008180c09036007404a003140c400d03003c00990b030f4200540d40c0c54080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 607111888 1250 607110638 607110671
    0x203070309030f0801140409050a0209040c0f0503071d1b070302010203100e090607110f01060e0f0612120304020a0b07051b04180b070917030403021008010503032b090303 75
    0x240c0c1e00b034060240714130041c040d10107044090109001c003203030701003102d180c0f501c0c040b8144011500d0003500203601c6004e110400c41e14024404c281d480102c1d4201c0aa5520000c041e510071a510072201d103e51144a0170078080c1c851030245a00800703180d2500c40500020b40e01c0c83c2d0581c0021403d400503580841803290100c2028081c8000700303602c100c03402c22400d1840d040358072800050700103401c0c088000059041d83e2010b010203500d04844c64000c001c41540c0d681380201040381120922007031200180028146e1401881500e0500407e8004100f5138110303001c0044103030300c0075000f80d80c040c000c0c0380c000039804603600c0107280d410320607001781440d5054003910500002c0f0728881d41d1f22132420411100000720741c1c80c80c0010110f420200c110b060340c450107000e6540180640206c2c8001d51541c40182c10b1420001c001d0089910076036114a68242142045818400130301034240d240d001000361070640d100401502581400c100800003d00013491340000031101d82d04001c0780803980f20041da02054003030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 607113138 1250 607111888 607111907
    0x702070b1c0501050d050c1905062209050405061302130c0f20192a230a06050307020f07080109050c04050609070c1b0605030f06010201090201020316050f01020307030903 75
    0x984641c403400174242d892686816110311014045c09019510f03d180855480d00c403c02407001038170041d0383d070400c00c00c3e5541245c1d11688070742c5111840340000a04160920a00d8030807900071000c1c04107600c440032107050041c1072a000703a83c00009007044040714503003441200c404402c0b98031121000c0c03a04040141c40e031943c0d40a83c61110b1600d4001c0745442a0110300098078030030f1441c504890020b81c5c58040c242a0080340e6481a1280d13068201003001500c0e1303c00310540d40410303030001d01000c4040704c1200940015a11a4200c845d201080050354041c9000d907070410301074010344207041d142070b1509103003000c50f91006520769141c81c201c20500c0f0041c0b01e0f180c6440c100303450a01451a121010680c0480003030001020402102c810b00f040c060180503403020809281e0095980d5a600c0c0030013020b61308107448444900e5a003c0c0481c2a82d030051084003800b95040e00a1410012403c08032500c225a0303d10a490320b010380301d807170a00f141080c1300462103400c0039100019001500e0600400d110344 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 607114388 1250 607113138 607113149
    0x3060c0c050c0315013302060619150804060b090f07180e180a051b041406010c0809010c17030702010c051c020d0905160305010b1005070b0702070b1c0501 68
    0x8003604880c443c0321609160541c1d070b01c40d10f00e405080071918036076011030701403144251030b108071b5800c20308441c4d000c103466008000489158805000d848000601003801c4c0c402c0800c40e0b80c510100c4030b1034900a80e0003507070040c010240041c004400c8808502c143c2d42c02c0301c130010345107000000c000c600c41c0c01c040e16020740401790141040c5913080c1280031405c5a0050550402205441c9081400ba0b004011484220307a0290a51302400c5401e000c105908a0198005221304c0c2010f40701c40308900040310041c401c0700141e466541941e407a8030341c000641d0001041034104a0016074400c00715a502201e10780c131800600c075995492804410090171103003c01c401c8010820f0800c0490001625246400300103142d6a03001640c2d001445007120090200c01c4004105c1d00641a07428540c00d2191400b03002c0f00d0081c1c0c024441d1150850800075146d90207203420340850b0090185501203001106602d03803000d19401181d590985600760425682c01c20707034072920b5426460000d0b034008902c1c0e0081600621 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 607115638 1250 607114388 607114393
    0x200a021c4805031e0f1b01050106051207031a1002030c0c030712120c0c140406090501080d141b0609150714031005040c09030b100302010504030b1003060c0c050c03 72
    0x40c0d456590342d450b07114050454100000e92031310920380c040c400c01116941c1c018588039a80d901070000d9010411001e00c000302c0d2541d441c100c000a21a4019400c0702d0b001d1401e640455040da0300d0f0b00b010b0b80200840a000c1943c0302800640f00d12948a0252684c241909500115258400d030074420340380040040311203000c1d4008250070810702140e05440c031045507112001c41d2800300204000c5540c0f11181d040982910542d1800182c000b801080d0b600e20013031f09840503c50719480c0e1002c1c0e000d6410a11422015070700041100015a105020601081c00000aa60318000d480c4040280c8904011162016500075800307010b000201042048036403400c2440e003807854513010340041c0114512004003021120000000707000665280e15420103000e0090003081510041a4010410351042c0001c50b1004d26190200744030980c00a04041180d07416510b180c5018107554a0564444010707210010060390716101100090190092030b0400040d603075094440d10b40380c00c0040c60048901c1d070440c043e8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 607116888 1250 607115638 607115777
    0x1508030f12010909120518090a050402101d0103020708040503060901060e0115020304050f030a02041b0f02011b180906061d061204230a06200a021c 65
    0xda1030100080d071415490410f180c6480302d0803c0801d12492102c0e085030701108c003400b0010b40948551000307019900a50720a08448106c0400b80c035800c00056800116002500d0380a03605d61003500106403032441040c4060420307a440c00030078900801a609001e031a51501c9040c810402c1054400b13004041c0d801c490318000b40d04403006501ca216901a603802849503031801c46a54408004001150790b018cc000c1081c1e2403002c003070307a52001c105420a000913114080e901c001501c14040c0d11403900200c4400482d61300840030a48880c2d1202011568880300b010000a0901043c8183c0c401041103454880440c0c140c1d1000c2c0580c501c2806400d44604801d020312003140250010181d1700c03036403001da4a64070520814510200f2102d020780d1080c5445801500001c0011903000341d40380f141d003541c5940c0d40c5504c0000c0412540100412040182e10101c3d0200d06403241d910071060400e0300c0e09050f117001600c0005003018040601011804d0b103143c1201c85d002c00f6440300d29140b10100d402c5d040703c08 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 607118138 1250 607116888 607116893
    0x151b041d06120d05030a050717070207060f0c02090c030711030f04050a0506042106020c010905010e0f01060503060c13120609020f040b060d051801020a080103030219080d1508030f12010909 83
    0xc5c000a002e5041003a914400600d01c107005901c10462404802a92082d40c0b4014034000d640e800709008650000340c0090401103054000c1c10b80e1b40030107034001c0140080d5516400b500d034050700014101010008402c906028500e018001000c0b00b414200d04140d5880c240414043c0c4040c1e513520850056402704410000301019214681c2c01d2007a01c1581fa201c21094207240c0c020f400340c2c5941c1c3c00e05d5441c1c00000e004000055120383c40c0304080f0340545003070074080c2141c41d080340c450b07119103601900103000190189000000070000703401f1030b402140002d92103085144002010f004115103259075400e0304015442c0c5400850b6142000301c80a200310307921a8089880c5005900741c07240b030182c94001050b1281462a441901c050380341c0021074075071100e014010302d1800300b0312064001d40241c4540d807180d48482c000b135100035a000035103d8030708141c3d0a042801481e070a0440031418180d41c0c00800d055805000030400e001c005400551107460000103209840e1040e404101071924103801c0400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 607119388 1250 607118138 607118147
    0x70e031c030e0109050102030709090605030604031e1e0906021e0706050a0519080f0907120308062815020619020703020a06090c0e09151b041d06120d 66
    0x1031141030301d0003242c0107440222103405090701040007400b550011003080f01d4140c0c8003d10008035605000140301d566924001c3c55101c20059801400064100c10384001d010214442414010b0151629032a8400590124040001c481264078000381294408224a40d410010f07284180344484400108400c010700d400d640d0852441104140240800c030b10040e14007460a44240007891143d814100c42c49040c0141a200700b01c2d90390240100d101c02045c4224400940c070415038200c81c0d042c2d03a2030541920159080b100040c1810307440850910100680c40711948a0803c0304101c031800d090040c100f040c80d0300110070100c408070856000c40208421040400c0b81e0798a28203110b0401070b51040c1a040c00c90805003540005048103041c0f0038603408000000195008580401100d80066118200a1916038420940090911118802007504031101080e0300d4a810038070400b8502d095556a1210303080d2000c0f250002e420f5070841c08200c01d505240400241301d1140710007800701000131440140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 607120638 1250 607119388 607119433
    0x1003021315030f1a0301110c06060103090c080a06050a0e0111031306020f0a020708100b012c040f0e0c011e0807030b120109020420120c091206070e03 66
    0x69148164420500814001c3d44000d5800312030b264180030503803004040c100315419031010140258a042d42d003e1180040380e06844c102d1800d40c000d0044c944800c00114082c0ca0840401d407215011000002031818007005402c008500c60000030a071840c10082c2a0100d44a168218200d030741880261001c280c0028101c80e1b0001038009445981d40765800d10000034007a001c0c1c0c00302682400105c4507401034001441900302e440d00401c5943d0000400d5000781a40c58080c80f41d030208080c8141e00410300d6a28480e882d024074010f00b02001d0f601d0010004043c1c5144c0c1c000796610f10b136110202c002d039440c2802000b8000900b03091502044004204200094082e450303140208111000403d1549110350040340f4190002000302d4405218090098000d0078010001c030f224078a0301c4480ea11a0500b8146d040c604c452105125082c50000e901b0600342d20001070501c0302d0715108112465040d40e50000b40c0c2c00090240c2c00a2a142c64509400f9003024000050144660b004118442c220300b010140d41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 607121888 1250 607120638 607120649
    0x3080a140601053103050a0b010f05010e040b0d1205040e010509070e01080a11130816030818030c1206070909090831031104111303060b0a0812070210030213 69
    0x83d202ea10a034141c440d1080050b045200340b00c180f0711303000800d000e4000b0350004510700031071040069990360110414481c50902c02c1c00e02040541d40381300110700d042d07401301e0341c2035401401a84108155550700101d00089410b440040340000c074062140201028041d4050031094410424600703141101600352019911000c0c10802c141c00081c0f0702d081903402850030407075200d004c1511a80e10103500d92130302107180100001e502c40e99040c141081c0700e44043d0b10403a50000f80041c50045004401040c8034400800c480e010704c40c07040400581d4482c450503c0c140d030341d6140513041da406e02c0d5a00410880786030344440d10030340c1451508c9012890b400216032a0140c05040e00c1c00700200c0ca0301078000fa480c240c44011005222000000c00d00404070212514541c00315010800d9061074603080400d4042c1451500e00150781000c10700010702c0c1648085903007100280601d414564544121b403a00e00700e2100403100d01004140102141800c8040007070451050505504160180c07507401190890303072084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 607123138 1250 607121888 607121917
    0x3031323030f030706110f0d0912171b0f03010b120105010504180203150d110f0d030816140c10052202211b030d030204150302070c1203080a14060105 66
    0x6048501c0c589204440510000004003510380402023090001416814810760b5103121400b8081c841c0392140007090801100998808a1030b213072001c201180f031840c1406810300140030070a48940c2290040a54000c0480d10343d8142c1d901100d0701e204d4416401a8000703030510205210034041e81c501030900c420358504107900180c90741d8940d21110f0449021480d081d40081611a8010500030348621652850905441c0c41e10032400308020303c20680d0101c0b20103400a0303850808035001e990507080c50a106c5540c0c1c6071040c003240c0011010102399000d820600c0b01580300640004603103941d80100d651240410303068007c900d00031150090070f50980c450091190101c51380e00040c0343c950102c480100c00700c8404031440b902544090303852407000b04080d80e01c00d100305048940d90fa4441e00071a000d4414401c0c102078081c100c004107030b0294110000c1265003004186022a04d1500500e08000e0b86029540c4c3c2c0d031442c18080e45c1002100e41c40f52107001e01c400603404110b09e69800c20100e52001c00300144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 607124388 1250 607123138 607123151
    0xe01020c06161e0305060307230613080d0c03170c0a0516060f06050f030610210602030703020d0516050a0f090302030f030301051804170903031323030f030706 70
    0x411200c0f01d42954205140000c41c144104800b0340c954443d03440f074030055089480264981101c0c5002008400040d070850450244523802400e040e0007500351000341d40e42d04000262500c1c3c0301424403100d1740c0d441d00010408032403207092540c003d0390900c1281908132001840d080c46210710320244a0031400c030090060005020a4610740c5400c10f06142d07070031480070020888074041c0300000d0107241c07207410310038242c40e18411054036000c60302d580900f5240001030300340c5260503044100580c00c4142d110100ea0a00d00107000316100f40011032040702560350050381d0b003607041105811a88041e02c0e207200440e005c8496118980c01c84102c1d0b5000c08a820001c00606a0600442d03508045d41c200030f400d40900080094000000005141651805c03204003000150483c04000e61010455019080c00c0298602c040a21603000c018003150402a094a203014040c00800081e4845540880c11a059803c0d4102003060340c3c20000b00e05034000c4005e02002c2c40d500f69031596034001d050b00504030954403038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 607125638 1250 607124388 607124431
    0x91501030c0504020a1107060e2701170a062a0507020102061b040b181804080313140316020a0504090c1e0f030305120a05160c0c080a05100e01020c06 66
    0x30320410400e806d900442c1c420702e4403800014983c183c08032825000f82c0a001400a60b104180207065a229000e4074404540e03203003001c02d5000c04609500d10009000e41700300380c2c01007803540c058181c58903400c800b5007441d400f8541f03036a8030300c02d000e000d9842000b505000031030061b0327404942c0d03507082070f40b0b00c0f50540d05100b8083d51880c42c0c0300e96030040303c083c1c4001510300c882c10304034404030403005d800300d41d80d0205142460300c480390308108075801421088c1c201b0005520b180c0b1005400c0c020f0b4001c100e98035040c0e00026010f4a50780c4920544029041c42c1024403046103441c0b0300c1c6101610301030701d00f40300b07484040e5100c0c1c0e05001c09000b00a40b811a81c0c45040d100d40c440e0b2840d034001c156040003810902d9030b904010b480c2c0c1c0e00103071170014241115000900782001d180516400360140480414a1102426048550f0a03003000b040715598400480001c42e04805c1080c80300f210b000d0b0b8050110303420540b101404a072151522401b860740103101301103d5070f03030102c0e44581c091a1206200410044527 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 607126888 1250 607125638 607125647
    0x30c0c0512150604180303050a06050a090e0f03090a050d170703080f0c1c0902040e010507092301080105120a05011107111f0513030614091501030c0504020a 69
    0x9421454021101141e00e211801002880060040c00c0307600382611600d5440500043e41d00d0110301c01c114034651405980021320036480a544544c480740005001d1f501c910005250410907030140f0000b07902c91448000403207090001d244501c1400c802546031003003880205421014904c1030f688542a150701400501c00c981c1400b0b04a80c40c4c1c5c0550990f21002450050400502540c8582c1c006c8040f00c009014418208101c8107400000f5800c0340d20100081310040140031101c604a130026200d1101c03400c5001c1c03d02034640544941c0d10341d0064541400c0e050308100440d80010358104881024440440e60883c071054152030095800c0b044581400054a1410700d40c0e9100400b2580b07041405803003101603102814031b09100c1e80c1e0410301c243c190f5041003920480c4402d10310b0b44060b4a450248064064801000d072182c2e00a01503007015960b4a5480840e0441b0920104102e410000c2085c407400030320422010821441c0d20210079411901c1b1001e031034042d4040d950256600094150845014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 607128138 1250 607126888 607126913
    0x10201090204020f120c160803190606030f0c050306090a0e15091615082a04030c06090b040f05010e121c0f030e03030604150e04110316080604030c 65
    0x3400555448008205800c1142d00400031709010004a0000ca000c00191004551492000380c1407160340c004903480d40c1c54684d001130b200702003190300d030504140100420b0103490010081740c1c8000074a1091030b0011026900b0101d100d00030041c0030000c0000a60302c525040c1e800142a00c00000d500000744e0459290480e21b003100f031041e00c0d001041000c2c8c0f00c03002035042e2503002403030618400580d850024043c11640b40141070046a103002c0012440c0c7d038a681d00448061040c00001645103101c0d03100803080d030140d082541e0110103564248000c9403c41c80c0b410082c840415694078083c075100b030140d030030240c1c0e000e82810080303200a030024075502c0e903051390506054242900c00c5403e8501c480350b0701d142c0d0301400402048c824098049500d02902c600c840c0c400042c07000e180f031a9960700411008141e00c1032120000d01038a0320200d40d0050080c00381d48641d101d0220b0310340820700d48080520740940303001c10301c2000040b0b120503c000880801e2071034206905080111400b0741514000700308564 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 607129388 1250 607128138 607128143
    0xb0903090a030b09010f0e030d050402061b0705040b030a02100c0c0911180f030d0818071226072003011a04061202090708070203040812091003060f120201020109 71
    0x419140200034003040f4103269002d410020002c2007642c1d1516014805c4e07504481d401001a00284040d41c0325221036005a90301c14401040ca6107000d04040303902d0b60f10b110700e4140500c5a400020103000c54141031281c14400c41c0100e00610082c4181c0d40015a441c98400544007080303800d1a00034100b144000701d01024242845080c000c14000e003030bd20150341c11100c00c1001c1c01c0b281010301ea02d1030903d00e103040c100c1d24003d009869030340c0c00102e0a85101401910000602e21030300700640404009110800141c44070b00600840a2043e003005104a409001c00790a0207489041d0711600c4441c5034211861507a024090060104004240c074805c4070050001a415500b042c6441014040342d00049500c4001110100001c6440328110722480c3d061a0b4001c1d0000490400310302c0382401500c1d144d61103807080c07045a142c261a03041c65030800a03001704001c890100414000c03401c0c54070300c4603103030344000e1803808108452800f1489494070000c2d2207038100200c5103a040c03a040d64402c1d002100a0758 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 607130638 1250 607129388 607129399
    0x1050a2310080405150405030a05090d0c06020f0706022d0c0307030302061902030907030f050f010c0905010816140d060e1e0c030127090510050f0c070f0b090309 71
    0x10750308010b04510700448040f20305006244c204002070241c4a10103004070f412500a6082a80d442070588695100040700b075846000d5014000c0014a100b94541c0a0004d580c0036026400482000c0c1d4039014154210304150342100c605180c11404c00700c43e01c001c400c140c2d8a0000c120f0342d0304030500d040c50100f94005805000f90f0402009164000828174000c1c1c0580c01c00c001c080003d00c1e0810203c0c0415240002240c0145008002250b10078455080c41c0380110f0581d40c011080310001802c45962080040210328040c004004542e00211985d6104c40354a0b03c507661225903020007032511060f0440980480700c049100d0b81c0c0380d08203500c0500900013100c0e01c410941081402500581050240d502c628140b140015032483c1c03d000690b03040720110220401c0c05c50402e205020910366050240c24900e80c1c0b145030f4008101c08011500a1b003460550015582c00e1120311001151001030490058100410800c40041d203880005104103401c01881c45258440d020120b04620640c00c030f42d544403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 607131888 1250 607130638 607130659
    0x7170a0b1305070e010909020901020606100e0612150604031a0403031b050c01201209030d0212060a06030b0d200409050d17010608040f020d0605070201140f01050a23 73
    0x960708042940c400700001d80f03c04c0306c0107503540c000364160700c5542c600390300503080034000c1402410711185c0c01007134a4181c00e104641ca628a008520f0700e401c06101d94001c0e000c0e035004c0c010f10060400c0301c10842c0303000382e0700c3c2e0b4a42811603c406154140160292000341e0a0030005000d05100e980720a488200ca56a188155025001c00411541040d00074090f55441e044030703002c42c03001318115454034006920681d41400d000328440c0040d22001081c0d0100d0303020400c0748482c0300b1818401400040300340740c5e100c1e510b805d03c0304c02d001042d102900090240b501d080c130420100d03070380c1e00301d4001c205502030144a400f40ca00310100e03000458411885800904103143c540400a012812008074011030341c403881d0200c56110303140001c950030310a240108040c1c07408500464440140b8404040c0090b29144040c13119544680403110112000e0340182d41d036882400f103442240840680045400246241c0c03075050100242c4100c509104601d43c05043d080810011110760745400c4910400802d940360301d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 607133138 1250 607131888 607131901
    0x120406020706020606030303070f050f130605070303200d0b010905030d02060906090607081504150e0a1d0c040b0a03050d0f1e0905040b040f15080607170a0b1305 71
    0x9400c1d2602503200903000b00030000340c0500700002524030a070800c0c1e54028407411407150640d002c0d400381020610301c54041180070003560703681005000a1507c0d980d2540c3d02c5c880303820010100d588140700400340712000c0d039540c14075040c230070261081411000400102041201c0068504500170f40c8080d805000f00c240f00801c807034000c100ca52260603400c089e10701980e6208940c5032555001c555547c00b01e02c6038400b04800c2c21a2120290741b810000d000001c0900400c5011180801913070700405a141041081009856080c042d54a10782c200d5245001141c5886d100c1c1904e0714102900540550780d110060b050598a41c02054000d50300031050724000d514641c6c008091190462106020962081ca001e02540e41341d03245007280c010036500c151031141071804000103400c86488081e4065112140041c1c461900e02c00c69040c103802c40504062a8540000c040c180600180074800303200d26400e64000440240c0c00701c0b6070000ba14007001600c11031640000310055443e46905140302d05e40f5041154 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 607134388 1250 607133138 607133143
    0x1003020d110a021c02060f04020607051504060606180e060a0e07020a0501050610020d0f090f23010804020a03141f020901080f0106140c010b1807080f0f071112040602 73
    0x1054881e507013036400c9442196034804210695000f05001684444002400d1441a450568016200500a619010903521403a18055000d080c4051080c00042803000b0001940704240041041e410b10a004008000e10800540c06502c24000181c01c9000001c00c03541d00c0c105c0310400b92034052000c0c6028200314030020b40da41e0010f4011100c0350b2034400810014940852a0341c100010366004000110309a081100c8550800014400303100d1b5200021407007011090728000a02407250b05e105c0c0c0c03410a110040401c80300b2000304c5040c891801d00740300250311520070b40e0060348e40006102200c100048025840d02507525600b40740111f1512156001c00b010340c004200380c0c9000d0f42c03103507820380703c1940d15452800c082c82400b02152829150380205100c15014040d441201c20000601210075004254080b10810045425000303500402003640e40000c0302940084444400c5c1d5440c0c540103000c80e42c81440907110200b804400d1116400864017049001200191121203e8403a0380c0d482001e90b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 607135638 1250 607134388 607134397
    0xc122306150f2104020609040213050a1d0f09030a20030315190b180a0e040b07090b040312080408070204092904080d11070b100e090c0307051003020d11 67
    0x20007952516082240f18000303038442c507001e550010320300c500d04030528040000a5002c1d0441c2501c00500c4240091182d4549030000d0040440c400400c444425035030207400007610061070303003042614001c244014090004180c41101405040c04415040601031414404034690201c001900c00003040200203c145100320f102080709503000120346140d110303d001c00c2501c40c0a05030100c0400c0c00400b0703680010504441840e100580441c0210380c43c1d150344401a90100c5080c1c84815030358060040e86944611003c00038150991114101415503650360005140e0300482400c20940202060070320280700102d5101c1c51b4018000c00c85440c4601d000101c68900603103c0c001c0316040a0511030306080800e006200b90b84c0444220710301514020407400405c0e83d03602504074285d040c0508400542e07000e004da0b000c0c400c0350700c5190090b490107203c0d80b2000d000402542c0c3c21340014101c0d070981e0310300080c02029580210b800150403507051a08070000d0069000854a03103040c400c5001c042d414040040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 607136888 1250 607135638 607135657
    0x305120901020709111305031902130e06090105060a0e011a0f2a1c120509030913091101050a0503040605091216020a060c05030f0c030f0403060c122306150f 69
    0x460985547e07408040c1c68110403080781c0503028611000320010300d002d4507440d00e00702003d200090000614294a4504001110880352030781d920b000f03004661a00c200c05000030850f07060100d580d981410003141103031583c282e09884204000c0740e0030303440f00d840c007054030300041d50103840b0b104070305184089900c0c0a000035192a0a4001d26080405e8075445501c448603080300b0340c5952440103025411680140070080120b1114081070000140540da12542604603810341680400d070841c40d81040c1d00a22818a810b03030500c88200846600c458105c6c060300c0d4842e0704103600040070b59030070841a05040064000b01801d00000422005255981d80e880000303074002e462441507a41c86540c242c442580f600c1016001e980709020740030074403a0560082c00c0c20500792050b41d00707110041c0d55180b0710350016001150ba040c2c488001c620b0055100e40080064407401e1070620440e103407100d0000c2109a99080d80304070032072103000a042c54613000310519010702c8001500c0d6640e44042c00c864030329084418403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 607138138 1250 607136888 607136917
    0xf0209040e0c1905030706111518100506010813020a17031c05060616030509150405010e011e0e010c0f1b15050a0c1b0f050f0406030512090102070911 66
    0x600d00f00031664000206031080640101002c500749001607a500c050844c1c89406c4d849942112008144054045406500604584400000320072a46800c10b025000302e00805444c00042006c240e900511140c0c0003141092040d4080c0c0c00d50001c142202400d801ca2603000800d01b6802899420000080442030340580703250104030340d103903068400d031a0f066600c40e5014100f0712400e0450090703030f05003628040c46410305901d0420032130017041040c62440c005401403200424104000e5801403a0300024450920304010100c50900420401030320655544e0304103c5030034600c1056034000e8802d43c08254100481e9481c0f00300e103240c41110000030313283c00a500d07498220000743e100540c070807400c40440c0c561a02420403084200880c2c10855003042901d01c036036030019480d00700c031491070400042c0920060b00c6241500300018803000d841c441034041e01a030714103107003000880c0d00482c0483e40000a9040c860b03036003442000407445e01200d504103941603032502c2e08a00c104950b030b40c010081803840b0b204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 607139388 1250 607138138 607138159
    0xa0b07020d09030503070b07051b07050a121a0a180506090114010e04030806041b1205060609030a2003100603020f04061503110d020406170f04020d060f0209040e0c 72
    0x701110400010300c0014299407062105000041c0f032840312940c440c03135038507203036060040b03440c078001540b41402c110040c00c2e0410710040c065420403241000141c040d000700c20900800c15078940007a2242c0610500344c41c20050b0204076080f020340c1000340c48102100721980034070900e04004d510f070711060b29449042e40c40d0010362480c4820b054020742c100d414000820751969070b1b40e1004d0750282402062660302a5561a40d1055004043c1140d0000d40303d5603281c001c05629006880300311500a00440d2040382c00b4412170656a82c0040c640c401c0a03440902840c0805248404415610545815035854012110a4a11200e440c0d004408582c000c64520010101c9182404100c0c0e030140510414010004050105207007e41c120321703010f03e28020181c0c80c0101c540c8101040717802540150340041d0354202d04c02111600e50100d180c01c11002030000f1030904066000070114010454000c18460315440c49000302511507040d04c40014001e401840310180181c0429180e104004400e48a2401070b074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 607140638 1250 607139388 607139413
    0xc1d0619031b030504021c0c1d0a0b0a0807050103090807020429180114030703060606030605010905041a09100321030e01050601020615190915062f0f0a0b0702 70
    0x44c2038065500509100705600f001595003081038920b07401510303a010b03c0b6400181042a0000c103524182c0381d64442890750814510340001e69907038440c105e01c10351580805100c40240402d41c40c04a030310900f0001000c00300e520f050b80f00b038010690041e5026103017004001c0312176001c5d001144402c00303e40003411000d03c00c804000c068508110329030f8050b400b100050095103c001c1520f21865001001c5504080d56940e640054401c183c01410010761100000c01c61545c000c0743d0300002d008125424411456604032450b40380d034040030624810740740b40307000c100591001d1203014042d41c0c0003041c00c2d8408138044110380250000901c81c10002e450480c8402d2981d1061003054010701d0140d019100c50303184d04401005c0c210340403112951055074400030403251a075040e1214001c0aa40b60046181158101039855400c40c0750320001c01d110002803440035400c503071814105488004030100001c1d03a55000c1841c0380520f40300400e000c078480c2200e07105c1408200038140e442006140d003142e038a011180c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 607141888 1250 607140638 607140641
    0x30a0807090b09060c0a0b0903180d0f08090d080c0616030e15150d0b060f030303161b08030403090e09030906180f1f080a0c1d0619031b03 61
    0x348188502c800081c064801c2904d4910000d012a04100049800c40407403907c2d040301741d517000d840441031544001070000d00310704078010340e21000c0c0d0304849981a2102070380b101e94100f0f40c1442d0080600320006076140003aa00d00715100c206982207a800e0b521140000b00441d5145c1003500c218503502c1c1d141d40e1529085203c4d002d211541541c0501038420070100d0300c900300c074040010300201510100d04e442c0304407684a00c4204030500b4024a10016241032800610107015060382d075942c06504108204010200313027440192001280c6d203045403e050401d00e415a08030200c1070b0040140000000f800281035010804100350780e004444900240c42e10040d1a40d280b180c92406070300514240224018850002c03030701c0b2050f010141c0741c47d44000310040050411880400c00d01061848070340304030070b61648a60f0031b03a40418007400c104024485141c01801c590b112030450b1140d00b501d10300322480b50f101d813410f85a40619203a00c1d0000e800341c00307102401409410310401c0c034150269440d4030940340f00b0b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 607143138 1250 607141888 607141907
    0x100e0a0b0d02010f0207120b0610030e06010e15060703020f1e0a110d06050f070f0302040e04110312041203020114070801050d0c120f02010f0305281d030a0807 70
    0x1044000310741842d42c01074035030415842c01c0000b035004046002403034840a880144126200e120351200034601582000310302e03100300110108144c9406616010000001042c0e41501d060712240d91a950f81e40792451a1023000407121030b0070110200b86d03001050740006001e100c10144009646c4001c0080110307150507800c0464080107a0b08c001109070200e85485424007002d400540040100401612400291001501c080d950515040100690203502c00d081c0c20b1181254902507240500e00304070400c0661025201900c070710304e800e4050f11241e44c01c1060218401c5960101c90f241c80d91604003850384401f01030290003550900d182c010030310180307603180c0340710380e40c1601c0340c04959082c00c0a01003281c5148908568102611034045001c10706100480c1d0020310074812001814224800100b59140504207502407500380070a01c19110340e900c9000c00c1d40c6e514010a842c1d29070389040705002420b12403650961004d08078001e101103241c04001001e1440321a00ca0511644442000701c3d1603000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 607144388 1250 607143138 607143161
    0x2306011b0206040b0901050d061419050a05060903010e01050708090c01020f150408120103060f140f070806010e0a0e011a0414010c030504050913050c0103090b0606030603070b03100e0a 81
    0x1003000300b4404c1d80c80c40030203044112018034010381000a03c0c03404600b100c01c1c40e0000768040d01c406210f500c582c5400b185c00c0050100a0185409043c54500032403282d01307403800f54520030b003408030395a03600783c0742588040d07040784540707000b440241042c80d40034200a03000d0350448040e001d0f06070241615400012001081901e400017040a064400d29031070b10030710f016108a81c00381d400c10220702d148512002c840d020f540200300c000381c400c0000103000d084981c41d1100d00c1005d0000010448504400700c001a8499803c0c00c2180e201e50303880004071104500c01010940c007241901c00420403181d40000c03181611001c1c4050201c05440d2883d5101c9405184128852260030800561865110700d58120242d0712031b0802c0d07400c20343c99a000032400c1200316201c6540191050103107041c01000c01c1a141400c400b801c00304210212902e0344183c0b070900a003414041c00002021440170784007040030304001d00a901500303480c2d0800c11400b10450315103120701501403070f03550b022034980d01d09446210304455 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 607145638 1250 607144388 607144399
    0x3032312100f050d230f03040f0906140306070305071211030103110d0b1b070c0603051e06010c020d020a0e040506040b06090c0301060c03120c0309021813152306011b02 74
    0x340a6011698a0f140c40340c2143d104e002d0300a01c206591b900300094405405a4001441c50a0924402008592540c0d02020111151140d405103546000c0f0318682c0000b024940404c4560300d90605544031500407459045c0f6918140c130916050384554081c50689108140c56152202200200018200000805040001d400b0003007020744024508120031031481c82c46460800d00903031206c0d184400c65910450109440e0410442c045980403105203440c145003415031071606244000070300200b48042c000340147c0030f6200450039541c1d03043c2050014248002840c2c80c0d840c1515001d0b4030381506690850300610007201003035061422008003489a80882240c80c01c40e80380103401c94920408440076424842c1c171084408000c0d899001e0310042d070030349440c0400c0c50140351050103000d012040e8481d0034240b661060040800704004036680c0e10f034009102900400380400e23140000d012038000c101882c50501100c101400074550101d03c20380098864034111941003030175400c1001c0c0e5a10095109 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 607146888 1250 607145638 607145663
    0x1091e05090c13060c0f3201200903070b030403020c011805030c040207031803080309160e06010f110304030b25021507031e020712050403032312100f050d 68
    0x207102d803450100303076401a10705a10152040d12000d0303a0300300d200504541158201c4c0380951f041e401e00350b49840307006110001c10880c480680361000304600c0000c205000f00d030010b5200030075038041024a0103131050300e801d0355880c1003a00d80a50f8030400705640e607002c25110302c003110508100319410800c030380c00038014080c0311502c003081000961050f00c045041c085450700b048544200b52002c40041d41c400c043c0b140e80c90501c440c50300c0ca803c1c00c845041142ca48a01424806000c040345000d402000c20709046200400608059038407800c4608114098840840d0000074404054411806030902c590113115440c603869542546800241c1030340090303441080312241580400501c0c60f0700c90308514000400c26103034002c02c01601c2c500144107000d590089806070034407154000940300c056941c200300d072402e490350344c0c003904840c03801d0740580454582a026a9035807262904440d072000c050302030030301d1034906802c005055182e9801103441440d54100c002c00c1504200d110a86016002260501c07035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 607148138 1250 607146888 607146899
    0x1403071d0c13030f03020615041505091b0a0915030b030309090405100c020a020916020d030f0212090d08010929120d050d0c2c01091e05090c13 63
    0x1a038081c01503640704600c2c10340008003184001e5460410f143c42070780034020301c6c109615849015201c618040b48181d00d000429490050300000181c21508240d844411a0b41c5191002c000450310707003440d9107100e10014170700203d142d1109100081e1114204880ca4404403c0d0b0100c04a440d0200c6298040e8420801d20342540b0300510960b070300900c1003080725541188000810103075a040240c0001580c400d0035898110f1802c8018a58400743d0b581104940c140180f5009595015a82c020010301d590781203813022101c0190100c6642d049000c504400e1820200d054a075541e20449640d0002074581d070007c242c1c409503004101032014101400410002108852020030702e180d01460307840452010100701100040c00844a012020f4483d6500c803424880e9078400c3d602c2010840c400c0100e00300c00c5040300498050707104606c109080d00903510502550040c1c458091641184902d441010400504401c0e496a500e007510703000e55840440b5100c9098803c13860146800110580c2900ca505208 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 607149388 1250 607148138 607148161
    0xf0305071b060b031b150a17040f0c060504080610080309060c0c0a1d13030c11010309023102090307090902010c140a020f0d0c26071403071d 62
    0x51050142c1c00c005108898900028507044c0500540341c10700582620305a814600f1644109141203400c503050319211540070010208020303494940001c2180c1404a01441100980d040c030b0198820241c0b04034a440b894007400030b400521604105101d040009900c01200c8003000d422140078000440c02d08036240304205c01c5800c190000802d0744940340b00c03014903546480155000344030018044200400100c440040741e0307001840500c0092100b000307140000e52251441102582280641c182c981c00c03400103c0103060130742000703540036808941900c107081c0141d803030780c5034a240d0034050409400754014280c280d0140301845545a00508070400c004442070304001e1140d841490501c180f0f800950351002d0070210440e100782c1541c05078041c2000c40c28005031000c1061001c171142e08240303c0c15980e25041d01c81c54041c00311065030100c03e04100510041e800303866241c0c15000ea50f43d450325900a140106455210b4a00c644100000050341801d9800c0002242c96480e40c04880c50f03071041d00303452 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 607150638 1250 607149388 607149437
    0x708120a09030914061c09050f120906090f04050412020d0216050907021501090207050733031806150509160e1908030316052b0b030a030f0f030507 65
    0x2e412174010040300300340ca20908540344200c101501c00150081d90313070420514100060041c80040d03400800c8460780300364000d082e124100803c44216580da800000480c05010000e203049400605190600007041504000300400d0b145c1542115800384d00160f04a030340da10092440b5035030907003400d014080c504002c00110703409001401100e0f00041c14004280d02407400342c1c8240b44060b40421b0703080400c84180185801483c003802c034200c003204070084500c44004466100e2400f00900e00e020000c250003504181c03c01800448150011007450900c030003d07124106042042100600000c2561301c0e14190140c09058001c3c02070803043c03040754080d5066030003038501d0341e40905440800c5003020301440c25032000c2c1040e54091500d81c1040100100c0506440c1040014408203111001c00901047e00602c4501480004108494540c0840d20010226680d10a0b0103000d1000e82c0024103070028840071000e282a03440000062600d8400c50441d042034820700c4c0000c211808041000100c242d030704 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 607151888 1250 607150638 607150679
    0x1506031207060f0e0a080a020d02030307050a0e12070f031406130201050d1401030305070b10210201120f0203040c1d07030e10090b101a0405060307140708120a090309 73
    0x10f4001c40141d11300d19050414004440d0078100240c2040d245a051000000c1e990443c0015419420f01d12006090f50040800e104104a440003c80a035aa9283e1600e810421044180c0f0310258980c04840c3c0c018019000681d480a18940002002c08000441d10f00c81c1501c600c0340b4265448540c011a40f0f0751085610001c440e403180704c400c60043c0f040800a000f540b2035240c040d61501580380c10f01c01c900c001412411200140788042182c1001c0b54101c811205154528404407105c5100507103c4d190603030300340e010a80c40c0011110351b1110560047d40a035000d6000b1320010b565403440140343e07004a40c01d0a41460542c0c0c04201500e000b44c0000382401c080905580400811083d92404c4074058201543c141552505225016001e1081c240c09071401185010041d09030700d2010b105446684034081c01030310300100091140f0300c104100d40201141041c85640d038100c60400a10359082403900c0090000d682c2d01003003017180244503401d10180d140e15641c040f01e1a050700c500c0341c0200748201 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 607153138 1250 607151888 607151891
    0xc090307080708030a030b0f0d1b08010e01020d0605031b0d17030702070509010f2301050f040e01031101030209132c15090303010e0f040501020412051506031207060f 73
    0x10692001c180150006400c1da00300860325428103050040a84070070107201d50141c104d1b9031401d0300c135803100da0b0900b00c0b240c2c000301061184d00c2440791204480349142d0200010b940b03400280d1505d000190020900100564410f002c0c05031604101602c44642241b1242d0300c0b0383c200f0b000411410209000d1200b180100e5441e903240ca00500c01010a6108482c0c110050301f2440b428411460300394180da003d00184020304c17030721601f4528000349401c0f0381500d201e0400045082c01592b0703032144080360b62010308499542d07125a540d1032344540380c0034203000454500201c0114485503501c00d10980303d0074880244000200c0500814540050184001e5101030615010982c11210341002c030020002c0c3c15600241041c425900c401200c400c0c0207848150103410810041040c42c04070001590802d02c0d00c0503444840d160751421900912856115149840d01809954103014002c1260b2031106481700c10759016550b07042c10507031201c558902d0302d10005014010710b0046411940300794407842400c1030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 607154388 1250 607153138 607153153
    0x105060301060e060f0f070501111c022203030908010c030218120c041a0102060c0a020a120504030f0c14010215010b070c181e061409131209050301150302090c0903 72
    0x188130079943c0c40902c41000e0f6600016400c0c04001c0e00342b003072041e030b041114103860601000584400f0320304100328440c0031117038010134018090010a40d000c20020b0002300400f448070341d20b280c09005400c091142110551031f01903005c40c1c49010740200c6a0820301c1400f964440c80f840000c0105d0324013030301104442c520a80e01c0000b995100d07445600450404078401c0b19060070207030002454450000c0400e54066010301030b41c075030300c2c0e00080c401540d9607200008445864100c9401c0303410f030183e0390001d0040524400d048051100359640801950b052407901c00e0b413400c050006a03a264442507000036001c803104010007c040d440d00c050051180b2900047c0340d007a503245922a141d90008041d884032031368802d5002d444184403010003e462140c5203003030249902c0c000c990289074003900c2c100c1d03009002c560006400800c100904003800c2d940841c4856060301c2d5004000c100b694640520360080d8038000061150040300a01c54007165401040881d03203540c0e41040b84d076030b9000103036025014400e011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 607155638 1250 607154388 607154407
    0xc0206180309131805010b0f0406050609060a05070f0c0311060306180a0605060d0f1811090a09060c030c0f141801170408070b150f010e120a0b010314060105060301060e06 75
    0x1080d0804e0707005200105040204008001080420b05240352049181110421540d15039000703442c030320441118811341714001c56a003070300d40b80300c0c3e8240102070308050300c400404c001c040b041250940380a1403400e100851442c00f484014842a6200c6d83d000300c0c09040c02c0c880385801c4283c90750102c142080814803540d241c0105003290007815074818502e46980040c181c5101d80e1003001c51100000f80038042890094884c0403284180c0c510250041200e100001c0ea0408250094032046a03c01c0c000c01c10891801c50080003409540c04001c0040d0303085041101c1e0a00c201e0349c3d00b000c1041c0345002841c1c41d450702d4041c018031901e8091a41030100c50000ca0301808001071100b48141d0007110426a078076064034243c8a4a14002c114544c001e05c1041c15100039101e820304000841020b00b081c08001d48a0b60002d600903407613800d032102c584542e081d0302d02000080aa01812603116000b200c08032030794950919200c0c1000d0045940001b401e0004100d05c07441140903c8d110070019080600c1d000c05003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 607156888 1250 607155638 607155671
    0x111905100201021b030f220b030a0b0a090209130b0d0206030c0a0207050d080a0503100e07020a0302060906041e030c06110304110307061202090a08030d0c020618030913 74
    0x10040c503015035804100c0e03014803ea8455240540150440170b07500d06a00072211108a008174076210300950307801c114901001c00940044400780c0b00345254203032a81703400044c43d0040c02a05a00310701440701c1040005070700080d4002d442c00b95030000c01507046a0108460500280744220345180d2003101c5c1030f02c02c0090307203c0c3c200440c00b0b410b050244503504e40f0400406031a10f4945d80c85a4000c52070180940c0104108000396210808039280841e90b0303803921400ea90608409402c000f17030801444c401d00003425000078201074554826000d41d880c07551a02195030301c4a5040b140a82091521440d990000e516010040300c149d00c642468641c4041a44441048682088202c075242c0000800c1c003090201420f105080300d042200104069405c200d030003040c5103000e41440301c1046d0013040400700360340c1e0b80c1c858070094101c61007100d440340b4800a00c4d0010341281445c840150103030034041400000b41c200c201c5481ea03c0c400042d440c2c41505810310009903c00c4160469040d520140a460203404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 607158138 1250 607156888 607156909
    0x915040f090c03050f06070c060506010c060e011a09150d030210061412062403120c0105010f08160509070c050109031110140a0926130b0403111905 65
    0x103881c8961040d8110300e001417030503d9035010303288079612a07420800c19644c041a0f117801564400c2c000300751512201c0040e00c103074084490041070b4904012480401c1001540041c0c2c01e8080341f0411081805207009003e80440269442c1407907141000c9101d4441c01d0054525242501c60310443d5400140c070869802240c1980d04105203801141c880d0344030341d00c0d204c0080c20004814001030080c6003170a8041e281d09908612001c100d41d1400c0f229003140395001e002041013104d07141c40c019030b100c0040c1002802400240610200842c00d03410200e00c42c8030005c4e2090050854401c0803a2044c206000c00009041c020640000c101400c1c0c1318a0018500b03000340700059100340c03a03030100c1c3d6a41c00321150070402c0404052501a15010b41da5441907c0c0d60b0720341b40c0007840a500069160040d007441804c1204094041505225466520849941410040223280e00b1000349500258035022a0845441103100281141213100702e202024944220010300ea10055800d16110315610000b05000d00c0c070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 607159388 1250 607158138 607158143
    0xa090e0717150604110a030506010e18090105150924040903020307030f0f02150402030313080f0111030403140c01380405060d0b09010e03040b04080d0c020915040f09 73
    0x15904034941c10b8030341e507605500540115818001c141c1da0314410007540c064042820201b50b2901d02080041c1d02540c3c210540d00c001510030300300c0d02040002920140f40076642c03120f4641ca060005040000d8101d1485501c400c028100c00c1c3c00c1d1521525804800185000c0400740002d6002602150b07884e0f00c101c41d0301074425005540c4850035810054204480d4078003010610550203070300881035a021803c0d42000c00101043c180310749590000c2461130250030f100c1440c43d011110080b6407180d002440d1895815088020710004180c0e01d102e034000d0005507401008100310300340d88011070390a01c000c1c000b6507100d403000044861150071071022098198400c1407002299150215014541007064010031006990a00071410400c01081025060540291080d180603000c035540c0380c0207402c2851001c44000c00c032900c41e234540d42203a40742d07801880390041c6840303a0030701b6080f5603014403076402203160020102505940c80e1003819a40e014904000c0350b0160740d8240c00c09409001c1e00c44c441c4d1340f03030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 607160638 1250 607159388 607159393
    0x7030308090610050a060f051201090b09010b0a0e060307120c051b010b06030406050601090e040c05100f090b0c0304081605040b1206041101030b060d0c030b06090a090e0717 76
    0x141a01d8590038800041c2c0010110303061a1020700998564103e48802c9803030710b2501428411112108444601400f500c000c012010a0b000184a404c40d401050075500c2c203c489280303607640c451100d0340c20310844442d20003241c1c2c0407641854900d071a0f405154041020304042c5140d07410070300351004450724809801d011610104080300e003040148580447d681005008202c041ca6000000300d4a0000800c0286940c4c0c4030800102c080c8d10074403010008010a00c141640b6080c40c1c540725801111b2401a18046c222023441111901d2003a10340854101e1940c58140c1d4250500c560745c8900e0f44210165a003030710082200045403c420881e0310181d038400000e00c0baa4078100410002a06e4811242c030788184d5459039650743c1600301094550b0890f40c000c0e990104644e030b41c40140c0c054031020798400c2d40b141e0082070890403600c290f0041036000030965000c000002c003d00c200005405491004c0d50030007548501070020074196407003ca8140114001c840f4001d980e230000440320b0114003009c00154 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 607161888 1250 607160638 607160641
    0xb2806060324090f0216080c19030c110a17100605060307021b03070306050106030209090601021204061809110703030501080d0c240203090c01020c030c01020d2007030308 75
    0x40d545072140381601068005561800200c45840002031101d60007071882c0c06a0316690310464918aa04842c00b1000742003100e9822001800c1501d0b032504264019030550042829591407202d900140a0203542c0c151a9410f5514094850000801e8144241e5421641654000c580c1070780d40b1800d42c40d5012803074003d01030b0588050020303050b44c400d6031060780101818010310160703c0c0c02185910400d03404003d003101138412680043d00c2c03c412980040c180e28900000400d42c103505800400c0d1035201a541c0c00d2864646000499460a00411000c81881d05001c1030008a106244002113220590307246104941c5642d00e080441e100204a44140c40e4002941800c05401d0300a1600420300071000c2c1055040000001e0514640c13500010a051468802c001a000042c1d861281402c200c1e078045440e450562402c0d5900c0582c01030781400b41c40783c1ca450340394601e40000c1ea080c00e106c06a02401d480d000840c8103840c10701c150350191061445101880007156400c010710001580240d03502d041030b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 607163138 1250 607161888 607161899
    0x1080109140d050a1202070602040b0403110d030f120603050105100312020f0c100203120403090515190f0912060c0306060239040501030f020a0e130b2806 68
    0x2204680c103101c10741041040342506030b000816221140030f0744c2000e004480700c04500e00002d11451070000d050318800b16012809a1504004d001500d1140c125240d801024904000c003028014500900088048090306d0881e441518500c0100c24505008038a0644039503c85094803000c941059400d41940d8082007444424982e1900103000760000d418071032144142d81d0b84908900e0701c801c1c09040a03109502c0b60510804c120340707a20310344c281d40123040c0c20302d4a8018044142c0d80b20705031044000712055501c12090030110b80c8030369458038103070380e1070031201d042a98282086628002841815500025141e406040a0b4510b601c1480001454400745002134100c030015001b02c000c65016010720004102103015081d000142142d08068402e8103504211002d82e9542c41d10360010f0070400000100700101103040c6400f0310032101400030940721101640c400600301d0384481000075104500f408950007030b8500c1e421018460796800d4100c10300c1d040d481c42c5c490489051007100d0350340100b000b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 607164388 1250 607163138 607163153
    0x912061618031208060d2f0402040b041208070f11011d060a08090f011107050613031b06180f0309050909030a03020309010e150106022107080901030b03030301080109 73
    0x403022259000c007654070309503111414001070701e003803140a00200002148042d5108041d00c05c0c00d56000d8241c55001071034219000ca02071820060b03102101d0783d500302000e545400e000341c8041d1101c0c140d0b0103060610b40100540d802420b4003040e1000b440810001001c1140d6038200449030f4022200c0880c0d1100c0340740010a02c0d5911000501901a08130328001140d42d070307800729180e42c010ba1034940b0507501ca40504c0d904104914403880003c2d8a04510791040848040240007218010000c0d030748241e8480c18a0703000c6a04a1400034005040040c1c2d507503007108000504a00c1901640b000194404000080c5005440c41102902e100702c0c0b50403007108041e84070003d1805054195103821380c40c1090007049540b40500d041d59010705802000085e0383d00c00940c03010444140d01c01c00c54201c52040c448000228800713014110041c000d00040b0501000310200b9038080c902d003010326514000052b100c0c01c41c541c0190004604150b00c1e0030500c9601d1b5810809180038040003030000540800c0c506d010790 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 607165638 1250 607164388 607164407
    0x3080f0109020901090b03100f0f05041b02060c070609150203040203010e120d0e120d060806010b13030f020105161101021b06030112081b01061a07110609120616 71
    0x2454503004104803450341e644080d0000484000e206c0c156100d45600c10254120441a044032142c040051000a0900b0700503010804a55065804021610384d030701c070382080c45e91001095000760b8040d2000c280b0b49a00390000740314407401410001000c00040d1303a01d019480103d02c610140540100511080d03207030a1042c40d2880c240e01004218004400300b0004e5a805410b2507070062a942d800c015009000501c07072034118901c408165985e80390310710300c003200405140c01104001c1c801d50001150300d8109004a400d02d64501d841119031515640d1401c141038008042241002401c0c411036602c03413003940e84c804000c0d12444c4020090702c45040020720303000c2020f491034041445d0321055496505c0d03490840b815610790f12648414030702a4100704c0058460b00f400071124a1140840018240c410340c4240c0030b4441d8803092015490700440c0c200200e002d4004050a590440010103030340b807822400803c201034003e81003002401c145400e05080201c203c54240d000081541c07402e1245074486150f6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 607166888 1250 607165638 607165649
    0x14014205071202010e0604020f03010f05040803040b060a060e061c050709090b0a060c020d0305070503120f06180a050603071a0c010b04021306050309011107051b090915060409080703080f01 83
    0x20090601c5030005c031640c800018001070b029441c000395151762038400f074101d007003900c5401c1c005010b10300341442c094680d80e00c1154159084290360b00820040e00d03060784054110340a56603000c10000e8410304002040e0701425104030401d01d500c00180e08204540901485408a070311340c442c0040c50101e20100b5038a0300d0a15a00c9200c49031014030180d6001480403007a650160f035100549501e41c50280c0d01480380c944060554400807603006a4080340400d0796205814040440104c2d490b40b400744122a0085030b42552251a003034005000e00016500c41c0394481701c000d003250030166580c0d0000b030307103541c0002000600590008030400303041424007035022402420340c2c0452500b0000b03143c0365130031080740c0212420424004041120140c094001c0651110f14401d001c1e6070f84079030715003580d460000121001ea02211200c2900c160316045130030a104070302e07050141c056203e08041c000c00b001801444030303501a0740e4403861030124800700701403c07155120340c0340d07402c040c103102c1518407250034140c0c0030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 607168138 1250 607166888 607166891
    0x10203340807021212180a0807031410090305180d120203070c0e13020d080906040e07170c09280b090108090a0804090207151109041401420507120201 66
    0x703454083c51050072900c8419240211030b040050502c006490307c80e066201c40300500c0780301c4000c010300002d82e40781030034980001c00b100c0328243c284030f0717404c280d0740006809400320301c0c248044003c010b11025070401c40100200310305801a40340c0e4a06092100d42c10381100140d0001c03c0031010483c0718040b180140c80e00301009202490824410080700c6843c41c0028090f50780c881c2c0b1b510421040209a600060008015a031641c0d210956242c0049040704c0c1e050000340d010f107642032400313000a501401002001c00c1c4911780036020041c80150031042d50415400210700000150203804000400090004001401d680d502903000040000001501c0d11701176400a401010015070003804036005c55030746000c00360b141c2500b41400c040c83c0e14003104101c3c6650814a5050382580c3d4040141038200301254100407080c810843c200381d41c80c09004004244c201c7c4c3c41c503000d0714038840da00400c1c1d00031741000c1e44103c0302c040b00044868034140448a03010800100390f200030442c814440c0700190303429200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 607169388 1250 607168138 607168153
    0x1b06060a1223070e010b070308070806130b06160f020909070806160e10030c03051320040b10020703020307060804032c030f0a1b050102033408070212 66
    0x4400c070251074030340c902400c003182c200402c2100581c207003d100014403a001c0050130300e603034920540c021a4080e090803000078140070005013181d409a4030031401224094894403540a40f6803540c0014026450080da00103414481359042c24800e50b4615034480c459130002c0c4030a070f15441800084040542a80d0f00e980119000b8802d00d000012419400640c0440007808900040401d0f503000d82c7e880b96640c2c201c00360404041d4850f030160025490b18410ba5810002562044000c2100e4600307440010320f100c801c110600c8a0f04180703811a002c03030310300030030019030b69100a00240b0184c40e0b1030743c14805a006601c0400035490180503c1009000b01c3c14061002e2400340d40040020202d10603860184880c000da0a916500081d407203080150050220741003414131140d8240e9802900508641c8100c90310700503000240c1540c03480b02101c0041e0000c40c00d1a0b288003c481d403080d1141c002c1c0d4981c0040c00000c04d0300c0701c024030005640ca400765001555601590060004205180c9449810755200f00c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 607170638 1250 607169388 607169393
    0x60201020c10020310030c06020a050f01020313020d08040b03090610060806090610180801020408160b0304150f050a020903100e07290f131d0103171b06060a12 70
    0x50342c400d0790006a800603900e64070f1710050b20003182242c02c01741282c101a00003151060f000191213008070f000d03000304c1c1d080a01100c0d80300c3c00e03880112540c000c1d28021a50280050a2031a1006091480b035980c03a4185078883c04c6001d202d800468441b0002d80c0140c040c8030744451058181405072105191802036072074400c01281903144c0c0070342201c1c0160b002c52000b00450f8420605c03401400d0ba403803204030850b541c0d0648a4040d4005020300c03070490090007445208241c192500c0411903d2039a54a0306540c0c03107446908110301102c2c880c244140c1c075091046403840c01c0c1d12440380300f144c80d03000041c0c4070803010342490300d0601c1c664040c1d0034461074a120352900b19000501da0048642007520625030304d5451200c0707403103940038001036440c1802c04a1a00119108100501001040900d03080f05044e90f61612200d1200c25400d040c0005540000510208260070078012068400c1c20206140c035011000c540701ea1040b80454211580002040c0803142c81c000309001e00421000789104000b00c501d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 607171888 1250 607170638 607170643
    0x30405041109010f02190803040f020d0302030a0f050c070e1801060e0411040905060c0c01180b220809040f0603020907020606041a0102120706140c09010807140315040f06060c0606060201020c 84
    0x43c03202400e002c7c80400020200407504081c1c40e8041e03400f0386640c501d0421841c020f0f540e500004c1550303012503078070728501d40d40c64840d9003607403030034051040107202c12850005910500d0201600201c1c03841c00c02c0c41040002902406410005d20b1282c0c50004c0516044c2046241e40e80404100ca2096040000982c086a00001c00682059414411950314068540301038010300340603070046584130030a0008810301c00c0d41c2404070b00c0707004046510340381c00030038503c5032103800030b002d200030030083c01400784401c103043c142d101c942803140c081c84c000360a40c0c890700050707180c14044506900580c44602042094142802800803015003803080068001c1180000707034540d2600700d20b131400040d020a03000280019a044940352140c0100c0c002030604140c40b9024160b0712006c10940840c1e50f51011615540c4240440309040814130501400d41c0c41c0c80c599170041c0c0c6c0807c040e140d409600da010810326280c207031003200010992510f40c012890001c2c5019016a01e0a40c80b440569105111110000300c02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 607173138 1250 607171888 607171933
    0x60b091305092406040501140d140c1f030b030d0c0206090a0504020318120405090f04031103040909020a08010204060807080a0e0703031106060a0f0b0705030405041109010f02 77
    0x6811001c80c25039200d000c0c40e0b20b00310074020710406032002141e110f15010500e20b142406a03006640c144010b82c2c071100700c01d010100303100702590400951032410b40420f036800d0400e0401e4220f0707426201c4606182e80003500c440c03014825030401509034000c503454550035101d01244ca0f2821350240211480700000500032181c0380c00064002c20300014000c2103942ca214000d030151100800440d281c0c24042e00c440031011218120503018403441c00d1240401204d041034908880f4000d000c2501903646c1c1400d00b103044000343c0101c0030311018284000e03841006002800103000c3d5a4000a649000d41c010028030b50041c2d03120721980c0e441000140580da51050201c0c0c0d21503c60b05000d180c50b02c03400660b1005240940000042d4050301001101b095031250449800101c07400c1200c41d140c840404008400440d8410140e18107105141008a03d07aa40040c0c03080a0190007524207082e076440101d401e82e1514030f10706a031014009640482d560300085031120705e00c0540700404c0010000040050414407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 607174388 1250 607173138 607173169
    0x901030209010b0a0c06181704211406040b0702070b030f07030b0a18020a091413110c0105090a03020706050301060206041b0510030605040c0c1a04060605060403030c0303060b09 78
    0x8005560200f40e400740c401c082c44a944080200070b042c40c047d031343c605494412902110340c5501c01803940041c0c410700c0c082ea4241c03604c403a07800a02c410b42294a5503100501d0307400311200003154108250901c020301200e07204900a036000401c900d07100c0300080c1060700d40c2e0080d41c280d0405006104404410590180c0d001c09a42400039000365000c0000700e00d40304a600442881c100400c007a11446403c2e00138100100083e00c03041182c07503d550154000125140401d074012240428550000c1e42d10380081820750511550741d46007100401145003551400c450707810040c1d01c81001601050342c100300180061440e480c1060855041c0380c002525204d01801c003410501841040503450080c0d1080d0704010721000700010005016048007030701078441c51080500c500d281c9030f00c0c1c03d10903000d84a000e05260b030000c0400c01c504000f12a0003420100500199201542c13590080b51369254a00140003550180e241d1b041c1a803045e150060641c1c03245d4000504911044c0594039080e111169130140160 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 607175638 1250 607174388 607174409
    0x10906020d09141f030c03050a0902132f0c06060102150f0a0f0507030e071a0714010207020a06050c010f091703040311060712061a070b1005090708090c090103020901 73
    0x10301d0f240000c3c0406101c00e502454490200c004a41d42540542c0001e510102d0344c6c40500095440042444c11110400070194011403a1841100081c0a6034086100d6103818402c00302c107104820010500c55184003008000800001100e0701ca8001c200100e6502070400d100031722550444c00d0001158a501038403502c070582c0d004001c15455213181d0021074420000d0344040051b4030f401c1034010301420029007902000e0040c04c80c0411021032070754964405104001906240222558580d01c038010b419a60b6902d41d5800d116801c016035603118000c0007484590344903a12801c04090070741c2160020b15403c03104070310308400500040d0204c90701c03106103448204000d449944500b01500c03040b601c20700620641c010b2008000710f142d003005485203a0003100008000c450707100c1d43c2e1101e0354044c003000d5035800f030302c01d01c41c04001030703202c0e801c4607840240c0f03c405401c05a40d810200391032140540e115404280003000b005003072001000240104a002c032000350303595143d5000300c0c52145041c002e50b001c09 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 607176888 1250 607175638 607175669
    0xc01050a0615050724061401110601060e0a0806091e030a0e01110a05011b0216050a0911040f0b07021224060d02191d10090b1302070c05010906020d09 66
    0x390404421409404514001504450b185050041c00c1a0184c10203174464014410540e5109040310305003909209c004011507428902e0540d00814103546095000e001000c0101d1074282c02d020880c09410034100070080800d410605821441c854030500b0300981c41030010b00303440303940400aa2400301c02801c1c409180307000c480c40281080c400000c0030b0550346c240623100c41120800e05e4040104205e41d820340d0010310b50b1f500281901c20091180d990b0007402070b4410301c030340072075580180c2103400c20541c028989690390524854801c2541e10031a4040008503049041d81003d4012103084030100c80541102312182d00f030100f01d200c2d18a407105190124000043d950740b03500160f49031180d0020008458561000d9039040400014002d031610b4054183c410300b0351128401d10341e03004860815685075028244800b40d0b00400c24a0b01309030384002c040c030403401001941d1005217405405000400c0c41c65080400142c21154a603100c00210340c48843d4610b02c0c0303070303000c8a25030580700c4219406055 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 607178138 1250 607176888 607176893
    0x703050f030604111204142b170c0310120201020d03050c0408011802120c1c08360609010c0206090f0303030c0406091e14030a06110c01050a06150507 66
    0x3044c44030001050b544000800c3d543e1401c5010f100c520903442036a013202181c00901005854419002c0301c401801200f0118110b01080d000140740800803900c0c000c0000c1424440510306e90009491000031140f000084c0b081e0780110342880005080b0500410054034001d60001750b40b0344152043c81d040541d00e80100d05900403c1c8211002014850003d000c40260305440048552898100305e12468125600800d072041c0880c4210900200410002200c100c04000c00c05440c01400111000c481c10012205007100b181e50f148081050b96200d4035410011600c2020500075882d04035200c1d890510661066a07440514807003602c0d410b9580c0c0da1644009804126100d107040c213515414007000c4204078104d04054003500440f00641d0724410a01d0b60740d950f40c021001034002e02c410005000505012a43c00071190201483c0302400700c0c2c500d800280c0340d9004841c5200d00c42b02c03118000003101c60142030240039064028164880400c0281e02c0c3c042c03250b40c1ca550f100f450318203010707010807084103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 607179388 1250 607178138 607178141
    0xd020a090510030c0809150c0a05090915010210060b0a03090501021c090c15080402060a020f060a02041e080a0212150103111f02300d0518030703050f030604 69
    0x100000381100d80303070448022016003e48548010070340010400e80028440c4600040d00d411600907c0015064984901103860301551281c401e080502004108580f400c6e02c0e52440e40380324001d0740540f01c41c1c501c8268002828600140c01311044641025010700901c1c184004484200d42541000120410316203020350283c02070b0303120500c030a66007080714030740303c0586d030040c0c00300030720030b6000001a80c1c82c1c54440e805000030510060000e00c0c0c940010300107050890060024407814012120300c1003084900a241c24000c5610502482d000700f01000a901d0f6048141c0f100f444843d08803c816042c00e50341d0369540b41c2960042d210359104206429140401e01805a580e1052100c601c0b00e50385a040c4070000541c00204e413806071030901101c280300b040ca0644060b0000c02540900040c00070000d842941110301c01c08462100010101c2c158440f007140c1c0140620b412010340131416160240c50003000700040400d01c10647c004206540020754090200c031910751103003103100d03269114400403a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 607180638 1250 607179388 607179407
    0xc09130501050f0402010f05180d020d0b0a09031d0102150c091002010c0e15090405070905061218030403020307030b0a060906030f1b0f05091e01030c0311150d020a 72
    0x18800e510b40b0050100c90010b00388014481d9000782c9480700521850300c03003110301e440b48012022080101300ba24020a240080300c0d0150503000800d070110304006600c44d0354003c00182c0340750303e582e070f903032145081059003201003009912480086403042d814800b00203911152080405455201400001412291f8444c01d850a42c400036001070010700c15680c0190090030f8002c03420000c43c044440890440c54840c96048050f1102c81c045800d01c1400c105000c040e18000d808041440392020000c500c60b112440074144805540c4811415401d11268a02410941c3d05002d503250304104028005602c00041140490b6444442d001c26035841c1108400208560b80008095074248980041400030310b1b040c0c1c013103560194a0041c0c8410400c1c14140c00e444031886000d090711070545040203e85804074800d640034802107043c44209401584031080d10714240c00850300c180c0c51510034001c0c84048480006000000c4d50204e5101d054115448280c1c00380540807015190000350324020306100c0d00031070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 607181888 1250 607180638 607180643
    0x20313021909050c030a060b03100303050903010908160c2903040c0503070f0602012a12020f0403260c100c020f10051504020f07030c031103030108071401110c0913 72
    0x300103609040c0d008020685c02500c0c031546083c281a0040f031481e40d2038040317078040c01101d0301440915142d6030b000d607900d40205003030b203902d550b0303880c02480402c031114020f00416201d0220648001070915199000382e40365084071a425032084c200c0711082d18403010040200614140b03031900ca0f0354031700e84201c3c08030050300400d8150285480c00110b0000010400d01a0341c10390300244400c10109800510711081c0040c000050540040440070080c010140407a9550301e4203409031a1061070090346520364000d0340102c4003259a00201c40c07001005007290024115442d6205140035103031031328170307545015100d1113000c41a9030706241000f880c02004110400f00020f01030310305190f110f4007030000502d02112600f580b140b00301c3d9400354500d000d200b1a41000c466000707049c103010094400320b40c60003035a00c007103040c800e0301d00095816800c20000765000f4103064008003809800c0c200b04110000254200c1c034184607014090140c101000b041c40c1009050a0710b010159a69082c960035103c0b00c7c48002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 607183138 1250 607181888 607181891
    0xc14010608061e0610030507050d0207080c010b030d0e1e0405151230160b0106020d0c080703210608010603050f0a030503070e010c0b1f09020313021909 67
    0x21100300c0840c99900c503001800020382c1c0030400091101070341e04210b90302a4041d5417044818415030080d8803407500034140c5d2501600302071048600204990150300161115074000c140b01c403000d0024091244402c000381d000d04558005940060221050107901c14800d0a00d98503985250200d100c01142440d0001c109100300e00381890a0614601002c6010f80140003030165403001446c00140c050b4608003c0038030a05900710411201d010b01b01403510107019000420030000d4001c1c64506900c0a00e02885100c3d015500d018000b034940403c1d15000000e02c1541c1903e0004940e050090711007035901400d0034180803028250502c5003680c0c1003c600d40161401c0e6000c900c5190544c0600c003500d01c14801c980b03407110341d030500c21b43c2e4550752480140041d00030030000350403d2013036143d4000c0100c103042449510020355150740442504443c001c401200703950030403540c40c00011985000704600702086107581421a52400000c0070050068024505110f080c40300001c04108036005104440c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 607184388 1250 607183138 607183151
    0x30b060f1204110a060e0d060e240906011206180b0901090c0b1201031b0302030601060e09072a020d080d02030f09160317120916080703120c1401 64
    0x480100040c03054409540402c004807845443d07040c030b54840c00c15100b171601c1c2e0642c0d903900380c410031801d40446c15003200d10607196031074007140312810000b86c58403481c01c1b4898403101c10074903810000e00c14001c0164905502140040000840c84c421450300b0540080d0045a450403019100b862000200c50086c009c00b004c02c100030307010034198000c0010741d11545401e00e135980e49210600706030060030800c04402a2050042000840010300404514900d00030807190990305c0e00083e060201c241c0c0588082003070152844220315040c10010b82c0420b160801c0c8018012180001010710200304042010041081c060340c2555078400b20f0080056010300c40f03503075031000481140301940090750722141c04600340d004902014008a980202103406012030408145141c44a4280400c0c6528804001200300a1501c5600c80302c941c80380f05401105c000c0800e242203500f034409484c01544660802d802c410410710000c0c0e541080442ca1710707041d1034120142001400c0c500910504a0313548035030341d0701c1c0c0030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 607185638 1250 607184388 607184407
    0xf0c0308070c032c0f0406030b0610110a11040507050307140c0c06040b070201030507170a0504020105090402070c0303140403030e1207081507090b03040b16031d150a110406030b060f 80
    0x200e020b500308054038903005100c107a85c1440290b5855000c001c000320039001c009002400c0408000031314417018030f000444e01c008004000e00703080c044a01075400400c0410510681d0405000c0e541d005011480c10500d9460700c544010000c60b50708511f203a0b001d0001501d0500603408006011086070010310703040c1e84541c0d510b048101584a00f100301c1c04207041c00c0000b00f2a5000e0074410800043c3c240b208040f03a554043c0603002010b005204074140101404001d41507240c0741302511035540700341c0d019010b0b282981170280682c101c100740080551420442400060350000652030030200030303581d400000801007017a03403c0c200f00f40c000320300324415110016440050070002a015051a8480b902c0345502d8100030b462903c0b04440152840340410041000c2d0711604968500000b21442c0c0043c05020507403070f40340320507458192858103a00c0408264445c03140000b815800814220040080c00050081038195009034800d140505a954800e000c4640b90881201c101d003a52a05c59503640442a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 607186888 1250 607185638 607185707
    0x512040801090605070825170f1801050c180a05040c020d030e0114010b03130203010606031a09060918011b030e010e0c031f062102010f0c0308070c03 66
    0x110b400d40303105007440045144030340240c5015004140400000c10105200c6d000d000805040c0c0e600301c010000d8191850320704401c0d44541c54019030203410803140c18100f1300c4a240c025044030000d101241d1501c0c0a1060099040c021140203140079482d28070505540030004211a0259000d00d4000b400d24610800440d4041030081c4c0380051a2810003044d08607401d10b5080300c80c0e290002904142ca032005020640f106c0c070140d03134850080d081100041c3c00c25804a03082d92816400b06001c203440f0f0b90669a040b100460303240b12500d040e541032a135403614400264850710013820010300c01072400400c0780c820b00203402201c0984041c035810340c0e40b800c040300c0050083c10000503401541d40b9024814540721404202c0000c0c0c000014014292151507a05030380540c0e4110f1720f000e90159540302d000648203081c1000c8045010074240e498041d006a0001400a07c49e182c07107a8200640500b2260000350410145034000b80b0601d4121252213452800b03651202c88144045e9200c41342c03c55551224518 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 607188138 1250 607186888 607186901
    0x405120303060907090b071709130c1b08030a09051207030207051314060f030c04090609031707050d051e10090f0228030b06040f030218010506160512040801 69
    0xc0d10343c90800c1d5140c0e101100ca88003107010380444040c04003c4400807440c449564a420a88210501d02d403c0002000849007035050f850081074940b203e0307007600780a81120b901d18000c890b0760044400d0070749955941e8080d210040030f41d64200da841341b4900074080100105101c10f060107040310341e200401c0c100030b980c800310340c0704007481040e5500c50480c007086c0c01c1c003401c03020902d0100f0300b096a440d25400c0004034408084900e40500c04d5007010301c51a0382d14003e505001d4001d000020303880360607090041207411140d08400c1050860002d00170000e81c00b03c100c0308144207800001601c1d80307858500c0400303035590800e10004103d881c41170202102a070040e40d03041341c513142010401e4a6900c9800c2d0180e010f00b80003a12403251010f50591501c240c5038018280490a2400180305c240440000c0c0954105801c007044103603422200f4001c40c2812a6442c3ca40100e000004030a1362421000074402d10400380d0041c980ac5000d0394050801c1010440b8407400401c00d20030035100c1e919080014001c0c0780 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 607189388 1250 607188138 607188151
    0x6031505091c0c14030903070b03090622030503130605010b0a021507090308090406080d081006020a0818150a111902030303010e2208040e07141e0405120303 69
    0x141d988029601c840c1c84880e07400080d0315258041e00240d25141e102d0402c44d111a004101d0008000c10a4956018401380c0c001c3e00303428030100d880f030408000c6c40b0718001c001070146001a2458110106a4011001140015615240c229a13030381d0743d9a4002c410a070b2101e4024007a83c20000049964241c0e44080e001c40106982203035081d44a03072003400345c1228156040301c0440c44008051010603203400041001e20009000805e42642c0c0b100c0c071501d040c220390324402c00036482000f40102000d4608601d0000c0500344000c1c814580c2d81d888203240c0d44504100d1403070046008c03191042940790381c14128000404081c480752142c1c00020054406400481664407600900070392481c136144100348000240c1c0c000d002182984c1c2041804601410041c0c69042001200892135214a0011008448152003004034584075480c040c505910780c8400b8240310280102080b8904e054810300003501c00c03c1c0070a400b1440310040c0ca24a84049203c3d9800c51508003442d02581d640d4800000001c45c01030b0f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 607190638 1250 607189388 607189393
    0x150b03011d0c0910050f1602090c0403200d050105070201020301060905090112030f05072a0602030307120b0d060929040519230604050106050d0203031b010603150509 73
    0x4079060140c07008003101c592141ca001440418030b5402c00700558184164141080e620f440701c1b001012915070000400f030f040c07400050340f4840446c1001d564140d080107240601c9820642155914150340044c4035201105481a100c0d216650f83d03840001140745800c075000b0015800c0400f4024081d5109010701c0d404100c142000142a003410300381c841c100d500b5080100740441055030112901c0c5d5203003100f0800c2000030701603580803504407186d2000d00311202e40c03090140340d6451b1012501d50919484081550018000c0008903900404140240c81507044002048008a00003d20340e6090030800f620f103500e0701c80410100508642c0d21291500d108410b03055107030264800704000e9404607030090498003d5114007504140d500c0c082c0c00e083e44160150b030100000c1441004e101c2e001c06c04140e8041c0d00140521046c13100a106400150106a0f0020340940c61600807903564458118585403d406a9100c901d40520030340c0f140c400746902c003070b0b00350102c8103030f81c80b050191030145c64010050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 607191888 1250 607190638 607190669
    0x2160501142a0c10020c06090f060c0319030207020d030c061b02060a0f020a0c0b040c03150203070905040b06040522050108030d0e0105011a070201090509070909060e04032001150b0301 81
    0x1e1401c5080780c0001d44040d0b001b40780255815043c031000381c00a60441c1c0d0005101e820b2000242d40d1381000d032110448000003191591080c008403c99a009000041e09062042048102688a01641410b5aa090309241100d5511440e000c2c0080030502240c0130f5852180c202054440c1c2e010402c02e005001812041c041040340140c078030124840d00e41d81502103001c00b49000d00083d078400c505980301d40103c1002000b55039980702c81224a1810400001b460760004c00c021702c84e078004541102610007a9070401000440601007200741c401c82c008c003841004161080382040049019030500d903000b03c03a09000b10359485029642e01c0d0045151018601e080407840c0c40310100500c1a05d04a500006100d240c103400c108032181541c0c07180b1020303810004803690209540d202d407811240100c189590701c050a0349017400d00c9044491a822104c066030b031400500c404643c1c084100061034110f50301c2911070070820380405006080724180350460700720200000400c08030110145048690b48441c0d210079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 607193138 1250 607191888 607191913
    0xd0c0914090d0801061b0602041d0f060f0f0303091008040b0a050c07020114070203010501170708060f04081312050105070806010203070309090c030609111902160501142a 75
    0x3129204002c2400103040b500c01003001134401c204c02d510140c00c002004100540540f81c501c1680d1103600418141c1c85140341c01c022a040c2882125880f0065821580880c10004001141c0580d2031007402d02c07a0309000b0800e08995410300440d0640400101040c0d1580c0942c0303805800c401c2d04440c00c3d190240c20100140079100c603801454402c1d1302f33942c3c0d41480d0a41c613a0064800b60042c07112280409420700c020b4005032024480c0601070049094841610f10b484014285006000d405c504825040351081c031403089a60005c075500264400f950310f07115628140025440741d07a40c0c1c406c402c1c0284003030b195401d0000650101e8090a05a0f4034080141d91f01401641e892081c090000c0c0010320b044010042985a82d1040c3e48000040c60080b6600750f0700c803042d200352604c0600720300200d08000740403140a4101d440300d11888600340068441031581405c00c1249aa41c1e00c81e46042c4080300c400d105c0c07401c000b98200d803038440340d07926001c1c4400301c244040d00c40501c81e034000c0c00140c4245070343c40b0030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 607194244 1106 607193138 607193143
    0x804020d03122a0e0d020603042924030a020904170a030b0a0905061302070f06020f0c010e030336010c020303090d0912020402090d0c091409 62
    0x140140c0020750002c00b280003410b020203004000010b43c1842c2c685d018001d1146070120b0390325032666a941819280c0005100094007420709c202d0202e00e03a844044416406050610240c611084110190701e40812147d01d2240c2c6c964080c0100000515240c04940d502c82e101d0a5041011141c021400c0e40a4000329000004640c440900214500b040801034004100b80f440900150500ba0049200e84100321808540c6540000d14401030151003880300f50440d900c00002c41d0f8455680078109400c0d00001c068180d83e50809109805011000082c0ca0040c8560b92807050484c2c414035042014804800500f4840e007482e40c0404600c00d820700c0f6600f006901034010715981d180c0b42618a040c1107495050740c081c0115000244400450f80415644990781500c006a0b1210310400066072590300000040012492050104e88410290071401441c800c100311a1100c3c2c40300c4603403d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 607014388 607194244 := by
  have h0 := BRFrame.cov_init 607014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 607014388 ≤ n) (h2 : n < 607194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
