-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5111
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:46:56.937995+00:00
-- url     : https://prove2.me/submissions/cd1e5611-f61e-4baf-a219-2d87288c8bd8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 919064748 ≤ n < 919244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 919065998 1250 919064748 919064753
    0x62304080303070903060e0f1b0d0c0f030b0c071106070602130806070e031f0b060c01050a020d390903020409080d0e06330d110f010e060f13052713 65
    0x140c003240c0d0030710500e4030880360a6040019542d0103c8020003481195480000100300030590302140448ec0500b405110999400110080a01c20f03002d00404000c000300440e400780c40c00f007000e040d1075402600018144183c81382c048811403d141c0000030a98444410020450f51103081450048004d030054845111100d2040e512048005030000e4007035202c3c6041e81c02c81e2144020b030713110100050f0003440f450400006690017940111307180300ca564180003021091f12075400d8080f01700d01400c42d0702c1d04450000106050ba960b16100c1d0b050400c82403d00000240c0c1c2c03540124004d690140b401280d44280b00c0000c1c42c11202c1142c8052101d8026204110f002035a440400c02282c50014400c0030180240005100c840000c2c00038a502501c40e15400e01400303040407405e0381900302942c030851141200d000660700c0c848810090350380410204034403124802540b01500350180c0038545405601d440b03900140c0105d0700c1d42c600800b0011400321b1500306000e00321002e0781000d084150a02d0048058 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 919067248 1250 919065998 919066003
    0x100f0b031e1c11120f0706091e15051012080706060f0e0a0b0f030d030905070e0c070c05010c0206040e09070b0a030b0901050406062304080303070903060e0f 69
    0xa0700d00300c900314000c038050105180a1000c200c0d2590005009010900c0d21007001e4404040a40790b10300c148a0f948210008000501c211602e4990010711a800c10560755141006040c4400c1c0444851544403050390f0910600c800203400c0d140b154213030b02c4000220318111800ca030381c010030501c4418240002080311644015418103010342200d0030a030380e08041d0400902030081580402c0c060050008001409c0d8041140103002c0c00d452841800011000c000704444805a415140c2d803541001b141e6001650290f800004400d204500795204141e50307688198060b08125030b5803001c0480040d0100801c054401ca841c041d20090034034025202098001c00c0d0180600d0041551014920001c40d940da40d040040d4002000d0a401443d80d4403001c50006014058005186018012520010695161901607038058640a42d03903102c1032080c0c0743d51042941c01c004d140d50001541040081100c09e0b06100030b51154500781c541d80c86a03071841c904101120601c10407011603800c00d80da00d85d61090003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 919068498 1250 919067248 919067263
    0x60d020906090a2c0c01020f070513060b0f04050a09051005011412010605090301110306030309100c0f030305061005070b0610030b06121e0903040b1614100f0b03 71
    0x5a03000012036550305040350040c0311418000c4610000720f41a01a11032034034210613015105074060341d11542c1d8100040e039035084180112031640d08625411300003401c095160840c010841200810341d603980b510f00240b280c1c88241083d04000e0000750074462801c207810b8802c020026500308110b586000e0040300c041e102140070f16410811818501c88210220a054800046c0305807402202543c0d80c5d013018140f40c1c4140d0640c1e00a500340448021030b074080c0d8003503c2c842c0b50003401451404c402d00d02044070484031140d00800f44007207507142001040c40c84001c100782d903103c0d460014884c01d1110400218072004d040c0181040010001c0f040000c1000c0010b40c1c0080007547d040e00052541e6009a01030031200204c1500b10002044640200090036400d90007400b1002401405910b21650311014a404840d005103a61080108000b41c2c8540e400500558901082a410760302071603071485021101c0300c2d104056503200303000544001d03282c1c0c070030b00010f509003090411103071814001290701c0e80d45 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 919069748 1250 919068498 919068511
    0x31b0203250503030f04021005070b010509070908030a08061906050a08040804051c1a01060207031202031c09060501050913060f060504020a02070e060105070c0b0c250905060d0209 79
    0x40c22419007607030010000041c0295600406580c0ca1340340544c0c0c0310100100c115010f901c070301c08010424205a0040e0700302c1c0e40c1b440e00301040b5056682401c0c184140c601d405469401000060000040d840400784058a02c001c680e9803014190b003482810442c1e8030721418011080340c1d013060300401c221031b0460101e0346010f45d0350401c00d8090b46c071420000003501455021640010f20203c071444030682c4041581e160302d11400c2c00c030319510426080c140d0310050034020030015911006c010710101c1c0a40014080e806054070440e880c0c040500c1c100641180360011802d1087d803240e026400304121170190302d02505c8192800700b598640584400c904e220505400303070a05076900c0e100582c031030032600850301522001c2c3c006e550311010307082c00960b00e8400c1e11619100080c0d44000c607d056214004540e07000d42c11020365000345081400d00c048076440070000000520440d540080300c4000490781088100b85450380b00c13003107450a41040156480105410310400f60b0300b8041005070b0710385136425001003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 919070998 1250 919069748 919069777
    0x1201090504020a0e0703090317040203120d0f140601031a01021207020409020301051f08070515090d0203060f10090b060406110a1718031b041a060d020901031b0203 72
    0x31207500104606071100e800040c01c64804104010b4070f1905500f040c050141300e6030f5640c446400300249400d0740e0400b924001c2d4150040440f01c4001150580a8010041c80400000d0303034070030b00801a0201d44c44140d52400d2041e04000300f02640d81c240c0f00380d0280c40c0c50021415101c1601d6030001792654184a46440300d0342c00403030b40109540343c9a21401c2c141e1341c007038020840340c01c00203100100e00c440307862900c547d11507541020954240c040fa0f20400c0300e001502640304204810f007210400c2d04114000303600000500d5440e40981d8003084910300603486074a1030107050074102d01d4000d114005070403000c40d141c10308190000948076601160122211890003501c2500f250f0522801c2c5443c5140c003920b8148081d01c00364088041c90300800d103402204003e5107100050509160301c0e03152100e149420800100540122814260410412094884074490040d242d04c000504960070081d801044158089916001c550b0144500e0525840801c0720001455508a00030360b0383c410b800315200c82d031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 919072248 1250 919070998 919071001
    0x21f0f0e01170f1905091c0c0f021c0605130b01080c030a080f190e090115170a0f0c12180c1403030d0e03030a0501091116020f100c0309060512010905 66
    0x40c0d9132003401024506040c0103108074105401c000e5a6024080d050140400012640890185c007806241c3c03109940000044661303141d6030208400f403d040182c00c000c0d06003409403880054410b2103054422654081c0000040b0124101610000d805801c00c550981c07100c11140c0c0c441d50001100c0d801c4e507501500b0107a50f1406101d00b0401030040b0700c11040c4072021202d00f00c4e08540c02626060b050041a2a1502c0716a03031030007861a0f234040c4610420100f040090801043c500b50900aa440241d403072020a810300107014010841c0d071014030030390003d49030b61f01d2450340001c1801000b075070f421014407824070300e19262560910f1075480c0c802c3d5161040d40000e06081c42c0c5040c0152208140c1c2c2d55402c000380f4003415280c0c0e4495008841c0305201d00d203010004594035450b4401c6030441d0b400f9003070440c18280901364800050107210000c2c2d0f481040a1041003250b070380c0c51090581142c00c5d0744ca0f0801c4515502d0054211200c4c0e40280040c854140003215903904120210742c1159015500401d09 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 919073498 1250 919072248 919072261
    0x3100e0c04050a170105090712110f060d0b0a0905070f0f0903020603010e0138090103180c0302090702030c0a030807110a05062a030a020304021f0f0e01170f 69
    0xca00c1164021500243c500c1d20018000300445402440e40c8401c100a1001c2d50342c40e84e08544a07841401411075912100413400b0124481c2080804d900304050014000c202c85000064120307005101c0f290a0355803280400d00c00783c10820845070080840c602c0030707c110b04004901401310240f2551042c02c21000c41a100c105510808402004503009031200340d40e941c44001498180409004809990418130624400744040c0b5060020120142c400d00c82c006021300040030740b079800422100e0415488158507100c18a10700c560340c6c2040d01ca104600001071a51040c040e83c1d60000300020107542080c00450344800300402c0010840d6403500e09030707150340d031210019207c0d03141d1980501c01c1d92040c08105003c010b40014032600513001d0b44070440c03100181c1d08107400300010186507034081e03400c00e0000c82c8003034003030303801135500310340f00030828019204079180c1070085400c45041000005e4080c2002501c3d16002000a100d201c400e207040309400d0340001c104505200041e001d0f50168040b0b0000482 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 919074748 1250 919073498 919073521
    0x11808040e040213060b0a0923040c0e0307140301111c020d020d05090d08010f030206071115070507030b010e240102160e160302032514070609150203100e 68
    0x3a01c0d0b0000b0020240c41b01003800c01c43d000040000e021486443c0042140c20454401c03900180d0150102090701d100b445c1800090046c04064409120000100309507030b540134040310014201803410204400214410507080d85d00c0145100e800203c1080500d00b0391100044030b441e5103102500140e80c83c1082d02e0414024410403d43d10005803404060150001000c581d2001d468a203981d6800e2598070741140c480510202c0c813000354040410481400018881c038180c4640e03030070040132000c40451806440c034150740242002c0f100d079000f82500f4804c0000c0410098058a401800e0703a15a03c0d01015001442515409008034990040c0303150907075a20030024000f02d0400303015102c5907584e8403070801d11700ca4400d98020390440e00d1150481d240f0391092098030311508050744c07510303040014003030304100150302089a4010812011031120562800500031b10a503881101c0000750041c1178101001c520714400c0c1c114654600402c240452028403000ba0001d41e11103c00030b02ca10703200c1c42000385 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 919075998 1250 919074748 919074769
    0x50901050426010506060f1204110a06020319030207031b060603020415050306130b0106140c011b021908090f04060509010b0c120c0604030f030f061403011808040e0402 74
    0x20403100400e9242d041011031809109104480329009015a84961342080464001e400e100c0d035680e8400d00810b0f840d404034181c0305030054060740d0b480c014a001c05011400c00030300d9030007600160740300182c6403809900d041180c442c80101464114202452960b005019501920302e0140d0b24014000d0001841082c0c0d000b0801142d00410070080d01c0c001c1c1c589503075514001c0c807849109015860001c0c002070980c0a11030145544140d10f022541c0c02c2400031b54042100e6a2221800e0701c0034008100e6a010274420324208160310703503100c032803501b81c410004d01d003200000c2c0c41c00720b0300d00c0b01e481100000d2401e410394051540807552100d101c038101020030003e040710b82c0950751151341440001a04107130200189082c41c5600c00f80c5071810000002020030f0701c035807030118185911110009000c05d128490380c0e00c031030a20745804181e000301c07042a541681e507180c0080002c0c070960000401103140900c60481100e4074050401c0f600c08050319051624000c5110f0301800044c1c04000904554a052002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 919077248 1250 919075998 919076009
    0x105070303111605010b100c0f020d0c0e07020a060c0f12020a02012702040b0d2609060703111c120e150f0103030e0901051c0201030b0d0f05100506010504060509010504 74
    0xc01800f4504009002e403c4a2000500600c5608007443d80b00c2c1c401d50140c55190f41041030038110400d0741e030034440040780749902980d02e203d0100020a01e8140c1e21810b80c020880381d4001d10300e820380340c2003810880310f40e1200704080c00a02141107848982007511030480400010005880b00c441c03420680c0035110f410100e040140008034020280b05030309481c03001c154003d607802c101920b8604140000c4020004014040e800030030000700b955914038111031480d82500402e24181102840860140e4205590840c0403507122038440c00703803c40400c001821200041d500302895101060081d03c80a6070705078062044c0d440c2d042e1000389800402511484415030070004000340380000200242c105d0a000880000382c9000701c1d000075242042205058880c01000d00c81c281c40748200c8445505501e5400f21b040c1925241090180c2e500c2c0c0030801290340c000c6d501a5281d8825160490074500c941403d80845440c19041c04104d2360701c08291030585a40d8109551340750407030340041c0c40b28041d40e03004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 919078498 1250 919077248 919077277
    0xb0a350a080c01180305040b16020406030f1115070615080a3012180503030705040914160c08071509030e0a03021c0c0905010608091b010507030311 65
    0x120400c01001d0001481c0815020000300310f00030712113544408030141050040e0000d002803106120b080c5105004107000e0f0011001812042c3c1340350301040507980e982d40700351002c1060000c10000d02551040c5c0100005088907000c00c0c400000500604a00541c01c0141001340c0e10079415038100740a1490101030300010044030f00d820b401e454824184075100d20700c11020300072040e00a0451020007512001000141c51310340500042004840c0141041c0c11030442d280e10b501c22800c00309030b0901c02180a0381166492941d0349090480c5141036070401d114940c02c5800100401020903040b82900c070500020b483c081c0280f00d05410030a03041d0188a030301030040d681513038040341810629405400702034426200c810800041d1010403803041c41a00c03002c0d4200b00c944503040f680f51008104151410f00c2650404081034882c8084d4080b280240c200501040980b014002e608400308101814007041050904030700401e240020701c5801510401014151610502d02c000000d8500b921700f001101d658 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 919079748 1250 919078498 919078513
    0x315020d110c0d0212030f0a050a020d2a05030f0112140615121c210f0b04112809170c01091d0115020109020613090b0a35 54
    0x4040d520340c03210303c00d120090311a6941606070080c0200a503440344c0111100c0003115502d02c0c0144014040003060b08101c250300f0070002a880c0c0e00c9116050498a00054490982c081e42e0340ba00042180c0311030035402e2100910400c41d8442c11680f0b02819103843c41940c00078a500c3d840d0000795440801d4240807107000d8102001401845034841c044516401c807084011600061207454a50012440803220000101c2111134130740d004040f040080c28400c2c503000040e8602800708401c075100901d60205454441d554a60036107480d004d400c080054070500316103054120401008070b600c821841c4100201044070074010203005210000060147c031041c816001e0465800341d840b14080310100b80401c0080e04045814803206040da01e1500482c074002d4000d900f0400440c100e040164003940444d921604400010380315903000d400b49464600c103201b0700e281010b01d20004c1d82c10a004080c06400114410050b01c0910f08c0400709003441056560608901d000c1c1c20110121a80d142c111984110305 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 919080998 1250 919079748 919079767
    0x110411040b0c0106050d02031b0111010e0705191212050d090819050c210403050708060103150c0525020301020a0f020118020d390905060108010315020d11 68
    0x20001d11405200350b00070407038070340c4500c01c002d4030450141000e50950700c40f141a803491000b074907060451080504010b10300380c004603880c0f420b54900c0000c1030b500d508504070410045c24014820000c08201192030b9400f14240502d80c091801a10006041c00c801d0030000011540500c0880e0f41c2e502c80000e080c00b421500e0b04104090f9031107030352a001003000038400820214451000e5a4105102c90f0280841e042c030154054035902c491000f520002c0c2d010400040003807410806840240182c2c00901425071450600184c10140d0410704d03e070031420000d0386049141d200040740e114104200c01c041040619600f801550011000300035055031000a03040d00301074006400d0f20f40b00c00598000c0c005a0b0121000c00700000344080000d401010f4207001c1e00c0050f03a0803800c403040c03402d5845945621480d054074030ba5100402030000340d424401d90403d0002d6a200c1c080c80d9804036007820310035580e525558a003050201c0045074064007682c00b055034120808240c0101c0d0010040d54040e9031600b030042d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 919082248 1250 919080998 919081019
    0x703030309050c01170114120f0f060108030403032a050703030e0406080c091b12010e10080303060f061c1a10110a020d021804050706080a0608030711041104 69
    0x400c240d03203920812080d83e5456124406800001c141c40031203c0c00c3c0d074038009010490b04034000a41e0303484240d202004040d07440401840d030f0303010006c0d0001c1c54041959a403441c00c000701a0001d18031740d00204002d1000c240c00802d030b8600340c85400c01080c442d00102881b1559a00c500c5001400c171b02a1100000038940e0115440056007400c560400070140d80d40f1142d0f0340d680010541e02d80001e40000041c0764410800c801c0c50004440f0250b080c504001c0c400c4000c0074010036040311042e41d1514040c05583d50101483c0d80240608400940c0f031420011f000600340641041e03024458500001c00c40c00c0d5405072085891000c044580601061800081c41c0d07400110000784a4011030685550401407441200100103410b190b0003d40945080c42d024080c49260441003680c0003c000304490030504440c007601446503001d00302412070141020002420044007070100c00e20f0034284003051000010100440f100035a001c400c201e4280c8101c40440c01504034041c0c40780a40704003140020b40c0d038519 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 919083498 1250 919082248 919082261
    0x140910030b0f03190f1106040906090510140d05100e060103020f0102030f040b071110030516030e0717101d0708010c080f1008010c0c05070e162007030303 68
    0x1ca400b0341c50784540100303140d900c000050001d04000710012000b40401c80d1900c541c228503001d2080410807008590114840350b105038400c0001c10b55039003041180001c54402c158104d81080c16069542d440e14100030019621003000c6880356031120059010807201f0800da2401c9000e42c0c10a00c41201501441da403105401d1200341e01a011151010540c0d45c070100813900c4400a4405090910342458224030040c3c1098408582280c2211191105a0b86402e0b40c8942100642c1c1c02080e580303861a0348110505912100d00c0505041c007800401307051010030724100742c0381000620410086564411440c00c00f540d4603240081f07183c0600c1c2c4211503404c00c1d001202c420b41500b01c644443e9520080f5080303070b100c9003c0c840044c0184000c10154144102410f4104000f130140303888041d100c20110342111444c001107030220f52080303030b81c0d41089020310000c4002d000ca800200c6840c50030030114440c40742e40c2c8803030300104442c0403208514825410307071813407020030304004440c80c0544030324010300180390303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 919084748 1250 919083498 919083521
    0x50f060309011e0603110306072001060302300c0f010c0524041202032502030c1302090a1a030c0927010603060905070c020f1c0b0114030303090d14091003 68
    0x3900504106e0381000124107005010b07a9a40c040f004102008051380e50040c072030303900515501c4900c0000583e031041e165040641e01041030308200c4401a10f4090482c01e88403111015420040c41d2401039035843c0c1e010a0401e10a0030420444542864814103141c101d0901074080ea0721030094404000313210b04850302c00c80c4207481e06012098044000e0342e40307010b400304281200e0b858007200c0c0c86405c201355220310270b1840502200d071b40f00102000580c10481c4801220140d56002c5980ca11714584070031048014602c510b030008907800c92842c0c050f81e0b0701c00100710500c0483e00044081c03450300c5034600700c03812411000c600d0b05030000f44c0a050300703020800c2c8a0400003078180700011030091a58894140502141e0300e51201e403183e40c0e400c0c00401228240c0d007952003903d00302c50b0601c0c4d00305202903030036091044080c15007960500b09603000700495500514007035403060003001f88006001400d8000c1601368140a442242c40d40400ca0161060380c114641007280c4490020005405802201c505007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 919085998 1250 919084748 919084763
    0x325050f1c1e150606180f030f030507050312190902010206010b0c0c0a0605090405013c05060f2101271d060720121c020406080916050f060309011e0603 67
    0x4400c4d0b000c054401b4810b00400c03c1034501e00c4401c20001c1da1003071001d85014400e041003410408291a0b0b1421a00712541611030044800d0401855804038104120494440c4508001c2d000d001c0c0c00003941c45105016005040d00300003011012840108040c014400008140c01201c0d5100e11009103203401416040d802181480c0003c0740e103061854242003201c51004103100c0c080440b500000e0440c640c00b10b00c10005850840c0490103840b0f2400514004440d400869903d14034a458100f000641d20f260b4424050010018040d058814401b410b40407003e040340c800c00c9a0300c0e00600c00811150003030801285c035901d001000c0c006c001c21150701c200303440d80740c40b07162103400102182140d40c0c0c000c144003107420651258005440c0c07580648054142010341002441c4001780c14400ca0f80103070014004551036608001d9118030401902c9104446000c2c01070440b403034031000c5140700d001c10710f4040c41800080009060014254802c1176034100b000b0b0540313042d00655401c00002c00780783c0001e58000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 919087248 1250 919085998 919086017
    0x7140f2d13090b0d06021803011112090d0206010b282007060f030e0f15040b010603020403081902161403010e0313060e0325050f1c1e150606 62
    0x1e02d00e114a40381c10f18041d005242608040c0c0d075060096220b165542c0301011191200c40d82900d00748602204901d183d10865a00c0340b4031000c800e400e080040c45002540c0c040d4843c4200281c0c01b007500c50460704182a620b85030007001c09420782c41c0005413820a1000d03040c002c0c5810040d0b020014103614440d1030701207848848030080098503501180607801c0440c091001c2202c0f114800d80c03003581e820300640d055421242d004082e441c1030195008014100b07988100911013404018070042e030041c545400e08501e03080c51582c520300280031740010f501c60001360030820f2500a0080c04209a040c4035914102801500c4103a204c041c44d11035403115009600c0d041d00d064800f0000021509283c3d0080c881c0d544161400d0800c0740c0519000000e1900b500880c40c5030796211294410120242c605007603a282d04a043c02c0600000d0360390510400d00c24100d50307600e010034181c90082e40f100aa048400030100c004040180c214481e41c89100070003210216200c882050042d9010109844886ea01c1c01e0340f0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 919088498 1250 919087248 919087259
    0xf070303031b080403050903010e010f02070c08161512020307030c12020a081f0308070c030528060b0f1e150306090a050402040921020607140f2d13 65
    0x465040a120100350340c0d40128005c2030080c40601300240c030082c00410580120403c80342075a0700b146149a00b107801003481c00802c000b2092010141c600d01c00140105403c010590503416114800c40e080d81c24941e5101c2030315841390750032180d4408c00c8901503689003080038004005160181ca4600089c8140c8021580e0700c100e80202c4101204a5680130030310b8481d00c40c15544800d02c00d800c003105941e048000400202818040c200a034060002010f43c00e1650404c542080c98480c8100150180c00d811030000d00007040c013030f40c00d0301c1c0c219100052101c443d00101c0c0402c3c0d69140885e5000481016285860807075441c0c034084c0200c103071010442ea0007039010b901c2d401d000c1650300603405041d00000411840d4142d201c03c4e40507000410118007003046841e40e030041e03220440b40144007420103401d019656010000707a47c111107140f43c4910b9541100c0e010740014051000c407410014400600f00750346140160f2118074000d400d2255426080c6440c2c45181d4903804403260300300f1b082042100181 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 919089748 1250 919088498 919088531
    0x20904060627080309131506050417061e04020a030c0f0f0e27030f0d0c020105070809030a11120c151303020a020f130504050d0e060301050a120804080f07030303 71
    0x102c801950044d800c1141314400c1000700c164602e20524001d69410300c51204101107078078a0000c1100d601d80656035420b01c000702c0100c0ca203109060300d041c0c2c000024090b1030141d8890a2007041c0d5483c500c001e0903211480003680340f042d141d04c041c01d0134610b80c0b404540c1507045003240045889102000140c1513540a0a80348814200c0f6a00008101524850b44003410805500309021940741624540840031001d140c0607009026061101a90382203042180d82d02482840e402c15802e00f00891586403042d6100e541e441801c8818013000100c00c1c2082d13400340100407003032403072020485a0340c03142c0940344829661101d816601141d940340b10080741000107100303201000341e5010390240203480d100707400b40490044044c20080d0041d1500301080030003074051280c3c4c0c0c00707280b05002800c117141180c2070080655030103a003e540700b610200b004110b80d41ea040d5070201201c200b0450940280c0c81810800e000c0e018551080e451802821580d542c035803000703ea090f081d07a109071801c01c00c0e5100304020300e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 919090998 1250 919089748 919089827
    0x30516050118261c0f08100306023603010b0613060305060d0218040303050a18171603030504020a12030e0d0203030c010c0306170c09041103010209040606 68
    0x1141c4001440c1c0510405034500761001c0c0075198980e08071002c0080300300320781c0713002140440d50001c40e2151180d000e082e54020103603011241d580ca48401281050b035104600080d0a210007801c603540019140160480211450111800c07041404801c01d91038009000b4240c0280105119500e004502407e6103003660544400e00d080d00c0710000480d080003c143e00515001d000b0f5680400d40c0501c00d07005a807001d0714006100d602444e82c15550526180180a03a00701414544019080401c0b404082019085841c8003d800100703000280030a24043e2000f807041481718018281015004014503030150412409641f0a4540c8040315540d1000380b81c0d502408100140001c054822185d20744c541b07002070009280c002401c0d00d00d4003104c0c40300c0c2402c6510a004101c0441d44511003040503845445143d0700307a035848006051414031201c001540800e00400080151100e207041c19031585095040d034011003805030040254039110500a03021004c00e42000044214030140000011001034100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 919092248 1250 919090998 919091027
    0x507170d050c072106151206020702061b0318060a1e02100e0706020f03043002040f0e010b0d0b01211b030309080d080117160305160501 60
    0x10400e95403040c00890741a481480500800c0c803c0b60004501003a41c13124055000c1000303040c0b01100c005525100c81600e000c005410444080b145e820014100002100304d4070b60b91060005980d0401c61000a18a008240520b6a1021b18001040380010000010302906100702404640c96071200104030107807250007800000902d4407082c020002c0034140070040d1005441c01581d0b1201502e0940704201e50130314400a00690000304204060341d0184100f25440060001075031a00f0306003121614540c0f0205010b00d0490051002c800c1140b5000c1d41c0516041c0e8020005c7c02aa64082103920140030b02c04103c0e80154600403001c1074918001030701051031076021401500e40d80c60b2014040300c030006021903141070034410f1220800150300030036003121030741c01e09151000c1c02e0850a00406104450f0428600d039800003c01c58040c0750441c908c50304491811540c0703541d19001e501810300b4400c0b0044052080007421401100300035022400380081140700b080c90181c1591200110351422111b00c5a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 919093498 1250 919092248 919092253
    0x30c030312051311060d0e01021305121c02100e0615121e0c0303070605041a09030418020d0e010f050a060f030206070606080f0607030501060f0e042403030903050717 73
    0x12070f400280328500302c08003880e00a2007075040c00d400c0e040c08000c3c6d46000b44514102c2c0d500265081d0032103042e0321040d01801003a16248007011006011039515400b00c1100c40c01440c0c000702c0200400d108104800610b10a810300b88070082d07451815031342d1035009851030101c0c61201103003400c09041000142c2e010098190040c00b01801e00040d581100c0b9101c0e10075940b40c02080d000311101d8808100a004541c401d910001d0700c2d1030b160521031800342c6440d00010402281d0024810318400000c151015209079240a1303042d2854828090024070610362044121401c1100743e4181c04010f41c0040b011180c2c1403000e000c0c556425000c40c02b2100f290061020b800440002440581050740241c065a44503280000c1e503141c45403001e81c500766040b034504446a0002040205181d414007416005018504000090b10031481c0c024028564501300e6a006a0b907075031103100e066841c942c03900c500d19a504030300082c3d03039100d04004118005900060b541880756080004580d5081c929400c03049505001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 919094748 1250 919093498 919093531
    0x60906180f062d05060613120210030c120b131e201206060405090c0c0d0203090f011209061505040b0906241e0a0e0306040b0c0a1701030c03031205 65
    0xf2594000c10025002c0754103d502401004a018003000c45240508444e9002c00782c25501441001044800042c51000709810102810305054002c29055801c1d210400080355a459035008144501e18071505610401d00b00401c4549400d910540001d1060b142c41040c0b00700d052181c03181d1142c2c400c210102141c0c000400c0040d001504d0100721540060b0000e242038642799440c00002d507143c10a503400c01c0b54090001e080701c0380020806c100805210389001070741c10321084a0009000025011a20381400350132140700803011102d40c00504d8055000d4010421201da1240d1903518150500070700e03006518003652202186804007500d48101c100901d451014404440348080d10300cac82850681b00c1c048203100070402d03000301c01400300c207060340071031403d8480d04c04001c001e104180c034002860080c2c001b03805000101c1c0801110782d5000a40c070245554954207150100e031039802040380308000243c81400407040003001005101185d0007a602d01d0020a8000036900c00c43e5801c0c0c8500745450700600c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 919095998 1250 919094748 919094831
    0x108060a0b160501060605031f0f260a0b10270e070803040b0702041b020d1107030605010803041a03010b180103020c060708040506070507020d060906180f06 69
    0x1002090101c02d28480c0e4003585503203599150a44201d50001004201d0204c2000b03da044c04022402204079111480315190346050060380c441c141030700031b00710540c4000c060080d2003d00d80066044200d2418115420070390b040c14010304402c0d003030312035010680c1a400c0001721034450410f100d41107030114102c1d801420144c400400109201a241c550034001c52a0014040b2024009400180410555076030b1701c1d0424410002140c8101d402c41c124081010001300300341c2e80c00200030713204941900703054030040c0058070554174029299000501c910f0528001217031845001c0013800c03c85045800c200d04c6400d110200c440203000c24002d80810003400e1010029038009500c2c800801c1e141814010b01d012811504542803c03012580e40c0f01064034901401b041103020007460303510000c1c84c070f4a6420700d0307819030004101d80d10040001c3c20464503106a00b062204603800a040060b062078104255121032070002c4403004006015102c040c41c203903c00d4940c0c140d462060300001d5151680340e84c0d102448 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 919097248 1250 919095998 919096019
    0x1e010905060f07020712030806030120072a060905031006051e0d060608010b240f1804020301060206040615060e010c0312050720010c0c15090f060203090c0108060a 72
    0x1040c2c6021417081080002da0b4481603103480100394002d030380f8008603141c00c0c0145030030360744240350314100c0c01e114880020103a140304003500e0030183c0c0913480840481c060a05000d9841c442412141740d02010b0200140c003d4000f403481080300d0007981560142d44e0380c0b41008084440c84e1103526000022035511820300c40401108440b070f901c00500d081c0d5005c801361241001c440d0305800c91407041e951196090311a10704400d6447c01070322400b003080e100e8107110020081602603808241d41c01c040100703004a03080780c440c0342c049079428041c104540f80c1d82d41c2e40c0300035903409d029a0140c1d401e618000100c002403180b50003134420303100c481d119107900e240301000444003400c0020b0243c0070080c090390500400d00050007501c0c044e000698500305401884d01d030796005149450043e001d160b01d059a00c03220350343c010507500b22075a004001c501c80250103102080103040c10880040c581903101144104019a660182d80541c09240441d0a072545250042d100b510b001d0791541e030302000121041118104c01e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 919098498 1250 919097248 919097251
    0xe0718020906161a07031d1c0509010c14161202030c0d02061216090e130f140601240e030c13090203030c060714040f06030504030e121e010905060f 65
    0x1070041c140c000e9082c111000c025081c1500c444000a44035075148808091881d0142c4040b0310f6500030704040c0c0d644114201d48c52014490941c00d006000c184800e01d680507070640403220341c000c0109080c4042070a0702a840f81c4030030055001c41c400d50000407030540d070705140303c0d2103650f406401016030b40c0c01201004040e00d6600700c1264081c800700b00c01e40309a030348040701070700419076013418400c014000103018090f860650003162980c40c2400070440012004000b4203c2142c210401c4008103841c2d0a00008481940031a802c1c10301c07441c4c00005d040740c120003480c4101401e5004011550041d40011101d11450070160740d45640103003480d200300e25045407003411254504900203150040c9a000ca42550800c510080554200308204a2604c2c0c20800786c40c01140000c1760140781c07505090240010218900035407040581d11000501014002e1003a643c1c2c07100d000780185001e070210b000d12540c4100740300140c1e5500d507400c01c10b090301d1041401480300c10359000024080c291798035107960801810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 919099748 1250 919098498 919098503
    0x11030f030408030a060302060d0b040507020a0314030601140a050a02010c0c03050d0e030c0714090609070c0609050111030405010902040c0e01050d0b04090b07020304080111030112060b030a05010e071802090616 92
    0x1e40380c0e030006c01070f51800000d114410311401e000c0391805600c001c1104851009014006541000074400c0001e58007041000c00d65202c4c90f0899100d0304c0380300040310540704004559402c0100020303170035003858006c07014090290aa0780244040500c80d40100da10300007800340200401c41c14400c0e00d000112540000419808402c201c82c20f24244092039480c080559225a4202500c02039214060a02d02c810f036602503416101702045042c1000018000108604050b1001ea502c400d01c40800c0001e4101d0010304c04040c001c1ca03164182403c0c0381d8001e00d1115801c030702c140c0ca4038030000030709030140450a0340c2c000b05845050030b1550170301c10280541614030880340e006661300810000030f00c403144058010400d41d4000c603260b604000e001400c4440f005105846280c050004000081100d41c041e010180c0c46000070604800c2c0f140403074508008560010843c1d42060180c5d03843c11400030301e050440d031500c0003401c00403102c46105001c07845004611030b0041d00c00c100810140700c00003007003480c01c0d2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 919100998 1250 919099748 919099751
    0x180c050318010e0d0e040f0c0c0b07050723011523030c0a030309170703020d110d050d110d0306080d05210a1415130b060f0f090111030f030408030a 65
    0x10760042c0f90f9801c02a14000403000f1a00440340c1d000d6600f00391040b960b142501c0714040014100c5e05502030103028880304020407449101c000500124414015910981d500a540390006d40a40d242d800d601c0c03042ca510101150f1030181502c0307903069201198030840e2030380340c0c02005e58071001000c400c18054081d4116098803421910360003d4859240d0700c801103029650f0f50700d5945c01c01040340d10072294103603105091b501caa901440540d80d8000e140c12103a40c4060b910411680300800b040000014040c0036111b4014100784800440d0003e090030341d042c91034419500d00c0e01c4240c106408480e101c0c040d110050717100d4400044041d01840c024032800100040c01e051410036004980150725080700e1300034045844c0e81907a011403e841d900140c0040c00044850502441c1402040e040da094070000e010701a1600000d1006495590803110108192000c290341d0318034203203004985500011006000403840144600c0340070000c004d80d188011021886440c548540c0c41d07004640d0805000da4040302d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 919102248 1250 919100998 919101011
    0x172a0304260c06031b18030d0c020102010b0102070b120915040614060411120a02300106050c0a0b1504020c0f1b0f1e0402030907180c05031801 63
    0x741d103405044808400d00c03501c80c41040000e48a5070500b05401c0e0801e004560500901a07928010303203900305d101d6810000b0a031202c01e1414400740c502e05034800c503030301409150b0701c1414213a4008500190036000f80c009006600c5131100480e6605480c0c481c0e00c002041c1030010702841c400425000c0c1c0c0040329182122009000390380c041c0d05a050907582103e046589030313814198802c441c203903540d1200044400304203d07140c00305502c11912401c0c482011669510001030388192107a070503518a00c030840448000c01072503c019101c51078880c0184040011260300000351503215104481c21108400040d0200413115503079254610405001002034540c0350081000365201c03031001c0c3c00d20070103a0004252440c81000c0c4c0c1030070303c8110258020014142d4074021800c0e02c41e103814481d295410750700250700d5640a030600d030566240c8030744294418000010701c03c0080b03001650b801650440c02c4802c40398016000a0022920010114008103806100003001c400c20107840a031445050310010904 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 919103498 1250 919102248 919102259
    0x307020901060f080108062707210606050409050c0d030306080a0c090f0b060f07060f020301080a0236070210092003010b0303090d0201090f12172a0304 67
    0x40260071902c0015002d44105015035800014140140b41c24005803005061214980140c0410204050a888200ca0020000070000c200110082c200081d4240c12222520302d44404841702c440191002410804082001d02c1c040c40b0760980942d1001c000e00100710082d00b44995002103210642c24150389900000782c81c2c000380f140c032901c1c620607880c1c0e100003402e05007210125044401c15644440c81c0c0340008403562551412100600c070340341d400507210311482c50070101a010b688a2819014000b00000820b00000120401c1d40c620031606c070048041502610551610009840c1c106400403861007000c80e400307600b44940202007841540c00100603003210400f61241001e080300e4940701003030001507110031507665070114202100288000c03400c0c00c0010f980e0b8064283c440b44542d1034025410700f1a070203545800300a007189850700308443d6907114400e0703107a03000c81020f5849241c0400c5602d4140b80d40c1048170075001440d104140c001c40c0a007030b8000f40d01c00e2100545050310042101091 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 919104748 1250 919103498 919103509
    0x2b14150919021c0e150403030519020f0406030605031b06160209090706020111040501080c03060f0d030c020103111c050613060e010f05030619020c010b060f03340e03030702 76
    0x90140301d0031080440d4070b1910401101d11103a0348004c5078200c180d801401c0711404075241e0304990580740c089416202d8244441c0d100c2ca082c514100da89100081404110321803c02900844c1c0e0a51002c000140d0760302c0c18940c8410440d0046140d21507c000c50b20900d14000c00505a40e06a001800b54075810603804141c0e44401910715101c03036480103c0400466034240140f100d03006060207524202440c0c803002910125003d02a5102c3c40e0011002945d552190586404020b100510f0410000c840c0d040c00b420074104c0391011380c0020f0a120200405c8801e110440b21108580b1500032014488060703018002d00010340215406511a030104044204500800019001c11645081c15514107007603d01464040e03440700e030198104000b00141000741d040c1c0e405002010300005030780c0c1c140c80d903076490051251040203940310341c02089080040071840c018501c9000703040340040c1c44181110b903811a41c000b0011865281000d070341c401c0c246c00d20921608001c100060100c0b400e10549900051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 919105998 1250 919104748 919104757
    0x919020f0d0e0c0a050d03031a0306040812090a08070f0303060e09070f30210f020c011d1306030c0e0417071a07052b1415091902 57
    0x1d940ca501ca07400116071010a00c10300f0301d180011641da042e5036240002140080c1c056031800760034541d50700e41d03040381500b42101c0390150034002010340d0389a01c1d080c54500321039000421000d10104c007800c0001c0c08104002003400c4032980140c0e41601f40715142d502d000c10807903055012000c0546808000a8050704040c40b1806404000c0150a030799051181000e0030046035800326400c035113910490b00a001c0d200c07031003031a80c141151622700c072209581081c00300383e80300c0b00340907102c2c164504040f0040c45d1701040860305454151300340c411081170b107401102c11700017804407259048110f0080001070320b044004107400c501d2040000c02c6c2103070f40351a11480c4400d2540b101c03940020703290070001000704134007826044404041d402d0b41056001d8480e10080416080901c0e0002c1800000c24040c17030254060b1022400c4584081c040941c14044a40f40f0502207641507101a0804d1002c08031464200d840ca8030400700c145828038940b070303402e08020b80c440000d017280d402a0410300342c81c2441c440500082 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 919107248 1250 919105998 919106017
    0x82a0d09260d0b0d02090109091406040c051005031e15041a03070f0f150309060e07080715020c09150d08120f01030201050306010f020123190b0919020f 67
    0x19203403030b03a20320900240d905100c5660b00c50707a030040012005981e094013090544001030000248815a0325068040503896040203001c1d206240c104810090707200c606509489081d5480325055645000c00d460b9804152050018192107500a59000207000412580861243c051a02c00c40d18040072600302c40d00e4050103140001034040b000c0980c00c0c1008004001c3c400b10080120746440e0006041c41d00d106030250580e030b400180c01c1150403070301c2038004a101c250003620800800b89000342d601d603507040078480d50000d400380340400a5040756441c180040d111094025028020350724041000708080101640da2100d4803074038010080d191520701410491095461701e6884d03562407c80511058000e02080440d41c100f40180b0050368001c05032070b0040e0007801d24000510100307409074058510822107900d405a01e64001344504e8050300c5507405000f040c5400c031500039421f0000300607140c038511210f400c0480080130555000c0740c0035a100c000741500d1001030030040c981c034034481d140d403040540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 919108498 1250 919107248 919107323
    0xf1c03090f0b0a02070306020715021204112b0f05010e03040e060a031505042f180601020601030b09030415050306040c020a031d0619082a0d09 63
    0x74000c20510740c401901425030149034606041000d94025074950050200500598010500608120308000c034400d110f1b1600c03100307540340d11004803040801f0b0700444043d90070034a0407001303c0250802c900d030b1980e00550003103002090060343d0506560104120011072744051072104c42070105400703104900d07208034500085d6682d586407130f455000c120742c094000c0b8420f885030310040001400204a03041c030f48080b41004a400d5aa030308003d02d0302c1100c826442c0b0316401c280c28034221140141101d0b5640c003001c07185600320802d00d0149503c41242101d140e030250b030000c00107001040b50b44e08107541c409000000c0301e103002c3e1244214000a503410440802064021082c0022480c060050070ba480c0f915200030081c501168070010b00c1c0701d4480c9141c4000c3c686141c070100b00c9840d15412034021600b40782c960813251201d0040244031010454a00c5102d00254a4100854544101d0320510f03129148400d41403458079014140103048201c1c04890382090300c49000404c4c00303042c026400c1505003a10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 919109748 1250 919108498 919108517
    0x1c03050912010b1813170c1e0d080c0306090c1b0106030b0123090705040317070b010506031e100e090a0c0603020a140c241906060203090f1c03 63
    0x1d000031035032100d032080c0c204c549607002c000080402d01180d40340507800200140d40034213207201e07103010751064070002030840c000c46803190103002034403120522000015040f50120032140c041112840d000703a5140e0000c600410128603113103420b10901d60001c140d4864a4580308401400c180000140501800b0594443c1410000c0c400b8804101d070060200817480102650285000d0316000e1150711504d100b43c0a100200750010b1180040ea409103a0103202c020041d00c060744140e026801050040302d002c0f06000c004a0142484400d40340290030716480c1852040ba40320000751030318001080031124005404002404000e062421406100600082c100707001890400e00314001e11900560141801040340310600c5a12104100502c40c134903141ca0b0b120074421820905203100d2080d0f0030b116264140c1d00f240f01c90108613003580114807200780e20442808500c0801d09884440c800c0c90003680080c084d419140c14450b9140101100040c03c0020080e43c107045000000c140c544290002a80c400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 919110998 1250 919109748 919109771
    0xb040e010f0515070b04110a0609051e030d0f030f0615030e010b10110a06140a060501080c04033203090a0801090209012612090f0405061c0305091201 66
    0x4880501030564200d9100c086201000e44035204135500240b14080c91400075051140c07401c803030141800020414900c00d42d58950043c4180c40c2405660300c43d0341c40000a800810000100e880030b006c019000d041281e0303001c4016511060800d0414080c140c1f2814014101e007050309c1800040c0145507100c106075240c031200103044407105840c4050716854903901c4002030f91034152514524503a480e0002c1100d040c040300a00f800182e0200038613050505e000001120504480b80f441070540304c0d400c000d91581d590044809860030307945d0002d00001080244041050100c4480c00a00708182ca00281c51f44002446400408150169030315000401c049085140016801d8028100100240a0700360503400107850b4207818450612207011003040c1001c114803016003108096070300700984000e140c1c1c141070b004c0aa808448003900c04c0481d000a60490726003481450b0264001034480000d240c4002c9941000d89915201a01802001d00002c0078655030951030001d61f2008078008107001c042c4a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 919112248 1250 919110998 919111019
    0x702030706110c011d2b1103060c030f070c02180115030e0a0c050f030f07080c0901090216140a0c030807020405180312150904060911060429040b040e01 67
    0xf040307514104510080424188603c50421003801d40c41140c01a018880d81003a0b440100e07200384500d6010303c6807a40c1041808503101204410074015030a507000f030341e201e6011414501c0304480c4642d103681c82c00049900d0030710819030704515601c0074050442050b001c82200d6503043c5c0036030103681c1c00c00c030090b810281140e140c0690940400c0c0b000080440319005c0e915020901007a0080c640905d404480c07444081d0f408101e555040e841c0202500c0720b058540c040503884e581d01e0b807071540c003882081c0c00001ea211503610031203c2ca000540c0304424520255a00c1d500b405401600a0381a44503101281c0c000c9191040c60800542c0f050790a56a00c000320700c1800305030384008040384200540040b803400000b81c040708550080002c444031291700d5803000104041111850720498000045404000130070403650300080940780540450708801c120312041050610680c02646000107a0802c0041c881c0307100130040c17003110b808800090801d81c4500c80c050207a0003580c0034254015121004002c01c1c00345 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 919113498 1250 919112248 919112263
    0x5180708270d0e01020f1005072a0b0f0f19110a020106090c02061e04080409020705101505030c09190203100303140412120903210314130b07020102070203070611 71
    0x20300246c8078640041080c40c0d255240c4c1d19080c41b9942c6ca440021314a103204036000040c0c41d4032050701c44945003070b04070b500002d50f581d480c044640203804400300f9818007800c52064400d2405010f0408650349035032250b10501c400901c520060b9880700110f52031501c43c0c001604440200340c0c00000c81c2480c256000007030392040140f03030b800d640004060140c0030101048005072101480a145000d0b211441c1c4401c0c14891907000385d096500c045030690401c8000301d4000840c0200040a02c40a41c0518040500b21034502c6440c1d8158400c60400340c144c14a994030940c4405004085241900e1070603154090360710880300c1120700e4101c04024401c0540044000809041e0815143d0600e07047c424107050174100c01750042c0040c44407194050500e03206180701009180d020309900440c0c0304000d4501c0c40b0f5050b058059000c00d0800008030420359055030158400c4401e60200180f00000c0d807640e6148c10b0000e403410085540800540c0003586007003141e100200080d5840003501c039a03806402d8103113504c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 919114748 1250 919113498 919113527
    0x1a09010b040b0a050c0709110919060e1210050103110a0e06090103110310110405100503161b080f12060409020315061c0c050a05180708270d 62
    0x1007400103201e0790106005403032071a42e150a2503580d03480240303c410b1401c8156488400007d0078a01010030340c0354500d01030142d809040e5002038640300d12000700100e48049000b4140003d24030403155681d8a8030161044801f0910025208450383c91580642501c0d801d8000340d5002088043c1c43c4424100318021000511003241d5035034190510f2400651110b1041c4409000000350344900460303994217105040d10480c4ca104108004070740c1c0c15241c000b0f6003051244030b1291513071101101e01540510f0440c2e2141004200110342d81c0b031400c4050740e2045070040484440320000007a0b0002407540e0000f81035640305d1200003605c0304080c00076502c1d43c4a000300303480d000380e09040c22100143c4000510b191200194009080030b9075075000032540c45a00c00c040c4039621560f0b18503d40522210f9182102601c800f0f50303504010380e45079414814180540c040d10b5915119a000081225104071900350300514103410008074500c4103000320310200080c40d81070340c4503002055068119604031000a61825 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 919115998 1250 919114748 919114769
    0x90302030f211201050f040608060f06130c05040314030415110c1002060708190f0b030c042c03041502032107020d0e060d110a0f0302070809040b040f1a0901 69
    0x2211444203d50020b410f120702c0307010390082d03c0180c07040d07070710341d0000703000346c002602152190302d40440300f410440b070300343d84c21b0f0f014803000e9100c490700c00c5441c06201000f10702902e81a14003451a9202c91001c1e00008042c800340c0828840420410688182c00c0715074211350755611170249480c134803607040500401802c0e208100208206c40c0890300030030b000d0741c4500342d4102221256a414110000030706490b042d2107401d46020f61045000190b540941049142503003103c502150960a00c01110b5400300ea10340e5500c04c0d081b4403041842460b07034400b0f465081d01c065a040ca0741d00c0312002e80142c829186000540c0010034100400c400c400c0340c60204045280380e410990030041406174035001e00c10280800c02c070040b0018440c0d901c83d0f41c1202d40c03d111895041000380c031009150040c1380c000d20104d0001440880a907210340d8401c0c000e40b1000e80d0041040c51800c0000d508200040c008840e00e6600152204601d0021800c3c511960f00b03e407100c0d1100030203401d528020014140016000240703c807 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 919117248 1250 919115998 919116007
    0x503120906281d220c1e051e0c0a0206070f05060f0a0e0a080d0f1104080a031107030c05040b0d060908041d090a0209101518240f090302030f21 63
    0x4150b010030b040d903160724141340010300d46841c250880c4c50b80c003c1c054a844080c800c50001d80050741c440b00801c2c0c0003110701d00c40c43d846000c4454080442c403440d14a1040780e481141e50740d0140c03400301d00a010b003e10900c1030b10712040c1c0540e52103051910840d194044000c2e001d0411101c1d41c81ca004003000700700364202510340c0015a42c1d2381520342c0914944100042e5807454580c8070034a0b00e9110103280000342c28040d4580e9a01c0e02c00b0740d594035045108030f00040717221055007441000050404281c90b40100400c0806040c0310a100050030065400f5a01c085803003403050125080d441440a094001d211003582d450910502401c0450f6200781c1c1915107400c4410800c00850228000030ba0950460700b000a545400121429102183d0085001000003403d40c1480302d400085101041489503001c4000541c1e4050039202c61080c03446600c80c481001c812441d80d60710032217131000b401040b41440300c0c0460300c030340101e0716080e5100ca0200e200d91000c1c413405030410010700d89072032000a944805151 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 919118498 1250 919117248 919117279
    0x304140a12030f1e020307090609140126151002070302010801050f0402040308130515040305060f0a0f060306140a09080a05030403140703180503120906281d 69
    0x4002001070190070966944400c840c843c070541c11549846880e07002c91079059400840c480020f520a580240104488030300008000c1e0055400f1821281c0c1d0003002e43c0303055040801907481a104451007901d84250000025151080201d428046c004004007070111504e040184090840d0040911003598010402040142e0303000d42d04506480301130f1048080f50f40f4410100f40a0b00a070342008041e030101150300c40200e000c5049032812520100c800c0d400c6161f82202c203614503c1180006042a0071160003d0f030589104500039420a0070722100150302c01c00201c000c2c1c1164015001141c0d0703d503d4074000d4211b1141451003507081840c4400400200c400b69803604864881c9450400074400084001014180103c024034642c601c1140c41d1642d46810345801440c00b225032513601d5614401700703404030312810005a0108044e200c0140181740c4a0310070b04010b05504103d0310440091019485482880050004802039008030348810009202c00190420044542e2000600980741044980c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 919119748 1250 919118498 919118513
    0x51e0105101a070c031b120201080a092423060607170d06030f061805070620070b120c0909010504050402040b040e06070210091a07050c120304140a 65
    0x31201100342800c184204550300820500981e5001360551610742000000d1100340408055004503035000c2d5a6141c3e16854080320b55004c140d07001e030014644400054840d1040d6010166490080c441d001c0c1450384064102c0d0b60b022000ca4a040a980703a0503d40000285404070143d011650b40c10720304586421000709916002c0c10001401c0d42c00060000d03150422100304031940c21004400500140742c903424040c4000442d1101282d000c1e103003445030384240660122400905a01c500513180d41464000c00700c8151001c5c00801c001d1500c44020701c00750a4040001c00e00411009880c241c492000d5543c8000c1c44000800128820b1020000b07016596500b00c4010b0544500722000035080c2c440e0b0000c20010700341c9039541030b00645010490300b4400c6001442c0c40c401c2c81e040d82100c4c02503900754007204c2510007254004102d214035010106d064072508103150782c0100c003468050705010395610014940410b2500540c5403940010a200c18842503c0e8140d0245050100610318280c8603500c814 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 919120998 1250 919119748 919119781
    0x503010e03030c0a090b040b071208100b0307050d1b030c020607050f1b030c10061a04141807110d030c020d0e01030e01090614012705130b04051e0105 66
    0x2c94080c0020352044d6144c042d103003041c041e03c4a0409513480729200c4501c0d0065a000c0b0405903001c0015009500c23115200b126858490400000b5040710b0910300310100c42c050300b0181502d400e020301448880064415071103058500607064071580f400341003c000180c216021072a000045410100c10007280d15088411640040c3e8084401c680d41c042d0150700c62020b80c0c451030b50300e4880c04005070f1510301c030000041e0028020041f08041044036902c0850260130050019500c07031070202030004012002c0420040c0b402ca400c090090310f80c003000414411407501c8200c5040d40406c0714180f03c04c020324010090141000000e0034200818105101c1c0a50f171650740742d0059040203040200d40034164030940003810701e180e04c02c0091041c20501d14084c0041e0203a2190301008094040000842654400d030b000e5428245504110740003016500746030107084010300c00904101c0d0181c02100185d0003900503880b80d4011400b8004000c02140e91460500c0070804034856071b8100014007890b11034896048 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 919122248 1250 919120998 919121011
    0x141905011203110c1003050712060501090303030203130b1303120b0a031e061505011803020a150927051003051f0906020a02030a1211070305070609060603030e0a0503010e0303 77
    0xc543e500b22500b19501d08030003429400e400c1843c3c95112000c554241e0442030040884d5180c001200ca60442c2407c1102c501c8c0c0710b0701d400200c0c452402c10111380030341d00854000302203070019401040c0f03036112086a01c105607903040100102110f407406050740f12880c104410043c18041c001309800d00e000440c0d00da0940405030038403d038031142d40c0540c2c0b2194211014947c0c00318040c4100242c04008007508901449100c3c00b0032030141038454940b0012303402e04281e81c0c1c020190401a424510110741d8814591140e6082c409d001c503002c544401c0d122800603243c00b54030b010320f002003409000b8805542c40500700345c4182d6000d60b014000180080340d4020905030061500464a0a0034021f001614201c00040c10041c40000c43d000010740c040010058401242c6500780b601c0b540c02c0f0f5440440f080e094007050440c4c014020782002034032a0008089041c0281d1011480b036059440d40011500d15600842c007145488900c030034141094084070009220440080004180711014540c0b81d20005005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 919123498 1250 919122248 919122257
    0x10914010314010905010518010b06031003060506011115040215130308090612010905040c0e090c0f0117270a05190203010207141f0c0e0121141905011203 68
    0x10344800c41d030b00b50700210b0750540100090210f428102c3c1c90303481d0f010b0740c04408034055080100c2c1c3c00d030714180700c0100d07030083e12081341c012062440c5489003002024064022810004824a88002e255003084a00c8280d503c0018840ca28103091042180d1070040e03e09040d20100180248006460070014080c1140d402145c2c5c680d5800c10400010218401c034061200c0c0c054180300007140d40c4209a010510840c07151039285c42403a16100c0180600104a403040305540c040e2400540509280c80c210201c2c05040c1451021041240c8000c0c90640d41194580901c17038400056038010b01c03400f011042c86100100c041c1100b0541900c4071a00c0b036401c3c007a29128a0051890034045440950480300341640045035080c50201c281c65103600c1d03040151034001c44d40702c81c2507000d52190151150b00309601d00794407005004880c82006590703008040c08440030500300c1d000c001c100a005401515408100e8040701c3d2540d2800640040d6128200501c3c00042450b01d00180300d40030b0200e00c200041c603050f080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 919124748 1250 919123498 919123523
    0x10807090c360b12040b0c0f0d1503020604030b0702120a02030d09080c060c04081203010e070c14060a020904150501080402061b120a02010f0902011b1112150109140103 74
    0xb01851a40d40080c005400005000c03408440c0403840601883c03184030385102545543c0020a040d020311104d40100501c01c000b44000304460b607000e019030450b107280124003941d480d000035032107410661055561600c000c1c2001416075041c81145110704800c0460703418001b0000c402981d90040300ea41c1010035075221903450900156909442d030051294089851a20b454054200720b9001407040040d50311a89019000c00408003040e01e0694801904e175880d66680e20303004445201e0103800580b84c2c12080000100c01d410144121440b55100420242e0f46605200a000456590710203451b40402141401d2045a0740100d21607001501207512603181c051154a0080607640b4280e1112076100780c8000d013588010102c0501001032258000300507842020414009441c20550024000703483c000c074400040303c2c1804200c648500401e0000c1c002c00c030703000c04111000c2010700110865400f6072840c0300303400f02d1035270654054810110144880d01c1007013040102e0b48010702004041180030700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 919125998 1250 919124748 919124837
    0x20f2a040207051006050907090b0d050c0c0f0c010f0201021e071e0b011403010e0c10090f0b22140114070b1509060427020a0806010807090c 62
    0x4054030b04098201d01038a101041600b4220700a160078030415010b400d0100018450b41d00400c80201150000760085282580c4070701c81d407000386002000240c1c0e4010901034590500b001b00110072900450500510700003801000140c44040040d13428021a070040152502d00f40e12000340d5241c200c02d03c2d5103180c642242d4a0701003000401140b8440035a86000020020301c0031484200f41220301030a540800584050249030a0b11165080d00780c4135404081c84200030304240703070520310078403080c40e00b000da884d20341d01c850f40508400d50011100c9240820301441999002d200c0041d012030005003082903d28006016010908400c2c1ca5414001894102800c500082003100c01456121840a4440ca000503c2e00521168842d205000d04480000990182400c1c41200d00d0308411003101c050342c0309003800c09a0102c840c4c05040340c1002c0d4091002622780300410615001c1c0010340050036205081040304411516230b24080c10800c000c1c00d4002030084201441140d04402d518184c042946041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 919127248 1250 919125998 919126001
    0x9111c14030705030c0105070810120f0201030e070306020c060601020c0117040c031a1006050a0207140607080f0a02010f06140402071a0c0706050c040614030712090f0201020f2a04 79
    0x1194083d1060000142948001c403041d802980b00380801d0301d40001c151141011820410403a00401b44480c1c440500f90303010440c00c1803d403200c0c503c140750103d003d0548600c0e050426819038422684c0940206003034003151010302003994000000c0c07000b06072420001c0002410b01100c14044242605500040b07801d00c40b461074020302440d04850402004049000607140c0490b044078295148020b0700404146544140100c8251580550003804c0042c142000f0300d400680c0c02000390f51086c0200300040c00503200710081c12107840d200c0310079500e13090090006800e56004070b200c01021071501a01340082204500d490306018010380d80180c443c0c1d070b00e15201d404601b0480c1345240c402000c02c00c20050481110050045500c1880b050110341c940004030032845c0943c0c050440440d03072030324a0b256120400805160300101529001d1008614840c3ca0021228180c0c5e06543c500c0e440b01001c401c1d540c0400ca00b440140750f040040c08812200fa05003014416281301e501c07181d9183e441e246190ba81c44c1d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 919128498 1250 919127248 919127257
    0x30f07050d0b030319170106050a110c0409030302091f0c060203060f18010602010606030510060302070503040b040e15010f0e061303020a1805010803030103152d09111c1403 76
    0x42e0842e5074600c1da00301407000089103400d0170380c0041c003014840030422011030784040c129003454642c0b07400c141c604a01030310b40003944070300c0d10681e2099440b907100710b6a42c0d004520045000303442c01a62102c41d1814030240c0100d0446404403101080c490810715580850200621500f045c401a00c0780c0f2028009101d1002c0c80318001d9005444a002c5011111518000340c1202e8041d0000c02002d81d40d03200075003ea4104a480955407440700700c0400c14280aa0010f200080c0301c0e801f40e078541903c80e4250011a00250089005400c20800b08160490303034549030303500308009007400c1c2c8500326002e00003002e1240741c0780141c3c0250700104064151042e0f09003004060b650041641601589030741d8981c06c51008074683c1c86d8960304003c0001104103011040300d0581c0d030400034800318503402d00070202c0904202c02442c10502015203116041400d8140030910b20690240003003000072440c02c140c5100391081e520280f04081c03824486070f00480700405105c05503840040d039041030090f404554154000e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 919129748 1250 919128498 919128521
    0xb0118020c0a11090604060303090b130b1603180e060d0212010e0c040f0c080403050f040b04060f021606091404024b070308100f1d0c030f07050d 64
    0x1941c1c2080341000b103607500f504080c1d1002e85080007269120010881a40d64910018011401c5000e085c040240d8500040403020741505283d010a940c1e4800c1e24a264404400c65401c1d4002c1d5030104200341d0b00c014007103024048052024801c41c100417004610060140034144250207844196003151240008604e82c81d1420000308920003448200585071071121114078402e915040141d000307800076101d0101107000664a5000a9440340d80584103a40100c0d46244111000d000000b2100920b10080002e0551036403580c100070001d80300a03240503d04901e210404407001e1003480b602e98404000e10441d40316151000b0f2402c4a0004a002841840d802c0c03508411070110156010006604000c1626071410354020140c0f0002c0c540e10380984c2c40000c1074015201004240042807240038481d411042d016801c0146031b03582c00b0041304040455208039198141a40b0b42c081008085200a038041d2040000524501d002c03051030300c85110041810040c8074000c12142e2080d600e69000f00c80110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 919130998 1250 919129748 919129753
    0x1b1e03020c100f09080609060105190e04030c030314011503020a110a11031b060d09031b0506310303051009230108030a09050108090c0301050109020d0b0105070b0118020c 75
    0x1502c8000c010103038182d9100b103202051a1020020b62018000395640c41580c2080203441141d00308801c001d80e400181000100c89680c0310f2000c2100740e60f0905c09030140b441b030344078101004058607010301a5544008000c01000007880104103482c02003051240c00c44070f51500503907071414000b054855001e00840d200d442d01c9200088020001a1010007048a404804036883c0030032100842000e450920310f03090700308005200e02c1c1040c0303a4580115242c24400e08002401c10030445450324a00403e00f4251a1903026600707000e00d114074449009401b09100d1100f501015a44081407010a0242d0004040540d9800040c24810711a000c46014001c0c070a4117000390300e541031040340030840b00386d49100202d41c820700000c0c40010005c1182c1500585844050316185800015140340c14000c000c00018050210307500d40b203560a04c60680a801054401a211101d0f4111441142c3c5450510390501a081010310041034150f44030a044410843d0080c1005601940c914003900844007125002e2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 919132248 1250 919130998 919131019
    0xe0111030d0f09051507020c06180d0321060501080f0a140403050a0207050a320d0b0a110702150f1323270405120c0703031b1e03020c 59
    0xb940d0380c01c08440a4015000c0310810540c480d051034040c4400c0d00d020740541d100c0b99820400741040f41c05040801240e5025080d0100342c0c5001c03580009031070400303c0010300880c00c82c030b6114900744941803261009620070440d81d814800041d0801d8809802004204640c2d40020780c0308a840c0c0146100940c40c100c401c195052600d409403e60b0004d00b20b020141c001c1d820046154100400b455045800c091003c002803d0b0341c200c0300f88481c40800070341c00b2103510a40302d2540f980743e06a818050301c0c8502c02001d05464415030030b000321035000102181948082144d04003580e03035400c110f0340c0c034004414025602c1143c0000070b0128071800c0404200301c0c1080d000090200100c0307001c09007200d07001078507603540445041006010028080412204090200710703000d00b0200c0b003100b0b03a12911401c00c41d54006c0b1900c40410841e0000601103069512000042c001c2582c090070744000b0002040c1d08481004072035031140c4090903c2003074100180080194903040c1442001034501100380500f240044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 919133498 1250 919132248 919132271
    0x405030705060c28200d060b0d051212010807121202011b080106020c09010f1505120406061a131703070b010f15020c03120f070501020408010203040b090c010e0111030d 74
    0xa144040c0c151110101714500e1030010f03181803440a00c244004002e460000f0031555906d0041c4403240170300c1d402041c8550250000b56041004902001ca566001c43d202c1c110756020700c04440b0144c000440640207400f080249210384006800446d612080303e01500c031440c9812030040c407002042d00400071400070107004881d08203140740d0507102190f00380c80140a288051144500081c451241c0406000004020081c51084040b0300000340b8a01075141101d50090400300f030100b541d0070344040c2d5a4902c20440e694400000085560000412508000c0041c4400c00a950b0320310030800742c0502030040c0c1180749401c2c011612084d03481007034400a56155002caa071a652103014a071141000341c00c02105642c0000b40030410610f00800070101000a6002c0d40351b80c3c0c011038103c091400f001d102003000190700780054000781c85424001138480ca014148004100c270003a10660081c0c00841a604c860b903484944031903420001c3c20000c15120451060600d50300c0707040e05500304585040c1c8280070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 919134748 1250 919133498 919133563
    0x50d211b12050907060f0908060901060608100b160c150f0906300e0a080c1002041d22050c030c090c1b010b090403080402040e01020405030705060c 65
    0x40640155619000301018600c0310040390380c10b5407244030f0f40e40302c0c08040115520035101c0c907141aa8918100f41e0b4140d07030349415403501e0300503900e0905507512142e052006503408240c8a5121007101c103007503005031620514120a01c0340c40c1d010b410350442d142c88030052100b8032150b035005044244198101c50902c060043c401e008400b542000648814000a482c5200e40b41c4182408400c425110000c18001000402d154190154555680d211070f4030410310b003828051810647e0023442102e03618000000c003a41072030b92040180c4000c1d0700c140030600c0403c0140203103034182a0040601e078041d8a660b801000c2c0010584080d101019220018508002012802c1e1060000c01e4003214071402c1540c0030003045140c100c0e5400b00100041c0b180ca00c0c01d400c00e11000c0100001c00380001039851a80c3d020800004080b21b0940101c0c105500303000c1181882c0c4542c004080244008504260030030b4002038481076144580e84c401c04001c224440074810500614420032441d00c945040e42005640601c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 919135998 1250 919134748 919134791
    0x2120723070f150c050f03040c1509090c05030705190c061b020f0606010206040b100e0a0b090a060e010b0a0e060a0c020310020403030828060618080a050d21 69
    0x5480303244500c800c580c88403ca00882c0b01d10310964480c20300380608811402e0503500010400d40f91894200710000f1800000144050540f055a032850045030a0201d1007060301c0d1001108ad0402c0010010403110590080513501aa9040f1202e84140003604000b101c1610000c44080d0609140000000c40402c200c1c6807a50026203d4003030b645000c400c0f800d030311b803514401c440701170268120500242c0000c3c0301c00011a4820403a6803154910781e02c40480c0f4030042800c80b0072600c0d181e950900c0c1c24461a00352086640480046800e0011909122040c1c400394012b10811001c1c1d680810144240c600600004080c910058041d544030224034000400f0345031001d1b402c1e0701074000c0c000303424601c8100e8000c03102641d8142c0c851180f15114903c0101021140c00744215a403504031001c00c16001c014024000245151b650b05c0500741104064407480014503444516550b00c1004448009103000c980461001071908000e19802118405048201c0000c800181c1862400c3e2000105003180703007004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 919137248 1250 919135998 919136003
    0x20c032401120813181512080705070902130e0c190e03010207021201020909060d11060d1e0506010f0908071e0f060801140a030f060f0f0e1f02120723070f 68
    0x2401007546d014000007450350a80100800c18a4498140012075030540040800038450404c03999050b40d40c1c8002c2080760880100c044861034046010030000306100300e00c58201590210701031030b00c81c0c00c17001c0d040081d905041401c2403140e00a104080b956080d03050714103213034018040b003040641c1c201c4524001d5002c001d5152107028031074049150390a049500031078041e0710072080f110040c043e004005103900280689841c40307881790f2109a00d114203084507011003000034400b003481d040000000d011003d07080c1040c2d04110307920307100304040d501c005004000c4036110501c03040c10407014094040d600002e82c010300d05104010100090641d4030074400d6049031103101d0382c890301500385401c00102030f0b8103103c00380010b600d85840c2c2d4041070103548002500d010501c000180092280c001c0e00559019810b11400c58101250040c01050840001e003102e0021080c1140380ca9280650f88480e940d0141002007008500440500b04070540c04444101c0100c000120341c0ba00420700e004c00e0000c1c89003e08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 919138498 1250 919137248 919137251
    0x50303090f071508060321030f010e07120e03090307240e0105090438010212030402031e0a170a0f020c011b06090b07020c03240112081318 61
    0x81410000c003003208020380392180a00c244401403070004071503204c4090416a414043c05844624254a2080c0680030405044a8586070314041c586040318040507071100581c0d120300400c00030065440300c800c1045540c40600082c62504403480e2a1841c0943c01c3d0b803a8040c801c0c0e88010440c880d906110141c580205103000391006810b4800f180c0420030f00c1e41035404a182440303985441e29081e04084010340c44c40c1c2000d055083c900501c0c001201c040f8000c8803054424400080c0156414000c2d141030401c885140381c9141404d9010030b80d900c150004d010004007604101d0681048244800e035807045d040100c4e03190040400c02c015500d0703801440300e07201050141c1c3e10b01101e940082225101d5800c141c46151120007100c0001400e2007200c0400c4401c1070f5901c0700030b000100c01c0d0315132a02840480d4000c20b0009806000d143c60011009066100d804201146041d084222694107046d540480e403d20010149890081d456003d00c1c0c0000640b010544e401040e10000b00000000c00d001e80c400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 919139748 1250 919138498 919138513
    0x1e05030c1923160608190b030d0f050d020706140601030c14030c040306090506060418080712120507080f010915030204090201090b2b0b0918071205030309 68
    0x1c2404401c4480c0014520b0b0300e1001800141182001d1026050100d041039580428a180300400c55401c55000040030a01200c2405003280c13103080c1c62030402d040744c80104130108200e00041d944102154643c0b0801200c6608403110130b12400a840f2855010310b0155203a1a03949803040c00303020b11400c0788005040c61800101c00d90304c28000d0313007089040d507260b9414a8186c000c0811259100511505907184200030000c0080c100c0d211b081080b80c00355014054030300f000c0303040200351115490007002d24081c00c0c0401c0046904001150391040c0d00070074000101c42204019150f00802400c0c41c22014682010815066004001030b8884c01d06413100d25006d80c0c13140e840c4001c131026107200c81c150100d50007061006062650013004034500505001014554406500700e0380d6224480c0640e1402089500030140140c0d0315034040021030540090148203a1f03000814003003003006000750600480070841081c000030a01034100544001a1700d101e40c40c0441c145195250b005403501c0c580c0744141351 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 919140998 1250 919139748 919139773
    0x60b2b060b0114030601081515030a0b0f0a0e150a120303110313080d020d0e030c010e0319080402150d02280f0f020f0a0309050405060d0c050d1e05030c 67
    0x21003a007209034030020f03ea070460301d811700110f80e07401000704200b4440904400c2c01f04e403aa5451400c060300100b80940c00d40c1d034580700244005076070f80c90000c3c0e8018040c2c401411203559604196106889902e0b045271900d0b0303603c1d02142141034440c814140c015031549408902c60810302258140203000352001c0c020b0008048100304144070403241d4034007030355403031040342c0009a8460045c0004a01d203030000d4184a14a52140111101c010303500b203142e0b0000440f1200c03d28280134000010b10904051410080004403030109415001144030400610400103811965440c401001c8410540c40c1c3d03e0315541c410200324000e50102001810102c1e10301c28000a1603442c1c04010b40c40a1a0f0740c552000354101c50b402d07200c00a02c074040e072081d400740b6051030120303000400418155a0090344c0d82103201e40740c102840102c0703401a18450140110041e170401041c0b892142400b291002e9455110242560034040102e08100c041d005c907600912401c1360501200102520008594105951a500401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 919142248 1250 919140998 919141007
    0x22050d06051e22110316050a06050309030d020912070b0d0e070b370c120806031e0f0604060b030105010b030906040201120603050d0f022107060b2b060b01 68
    0x2140c04008100b00088042001c1100c40203060a442c85044e04609050501c40042d04007040320381030352000500b0f40403c000d649020a00b41000308118101103166050419071940c9a11507111030302e09981d00051030203115200c08080000c503251f408180c4816071b407241c80c11089a4041c120801c4442e0401d01d82261214001c18440e0480d000a08041d20748911802601e41c1a40103e402503044445618023240e15820200a640304441d65076501c4091030292600b407014203180e414071400c0003c89010030803181c5000940046050b50040413030560002541308d14905031030145960114010001804100009134005003d000c2c411402407085a8030307484240b01500040783c11600e19440040460090b5004808400e4000e4500c44042003a90720307a00c45c140b410f450001d4100000b140c207111794001c10742c144202c11151801d801d100c0e9800f018028280b0b0076018041d0082d1100d580c414498840d80d0398680c65100c10140f4840580300d854030719a903410a0041c11009a4949040034010b00803503215 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 919143498 1250 919142248 919142251
    0x100203040609030609060204150c03021606020d0e03030c030406020a0515070c03180504050f061008060d201906030606020102090a0e130519020f100522050d06051e 72
    0x102d54070403a44a14503141c400280c60300a0702500d0300756080002080030001c034002c1c0e041540242d01e5840c0d2026143c0342c028500003500b0440e4000340711035071003402902c1e40410507040800c0280303014010340b205640081d0030340c4503030201c440c668400020001012030300442c0602195004006a07442c00890309501c0307000c1d60b01140c02034001a80f003400240000c1c09221800145440814400e02e059216408101101c00030b5440301d040c2d900314005c000c00c42c039080300c81d102070f60f5a0b890300340328a0402e50007040340c540031034400034904d4105003055066020719034905070356810b00030075602506c4401c112040104445024030f0001904142021580e030780140200c1e035414801a202509551804086400c100405054040d0001d41c4600000c04100704003c80000f1441c81d5214481c0030030f640c0304000d800b48490085601422030310703014500c41074214090752940e420324607494a490380c041681c5060414503410040c0d021703410403850b005102c03040e03000c83c0c45410800441414801d40f4245040c40c3c900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 919144748 1250 919143498 919143509
    0x1112011d010e0f071505182706120d030906021210030c060801080703080a030b13050604060f050d0204050618040303020a08240111100204150e01050f030a0c09030501150510020304 79
    0x2070179510440b42071040000340b4454102c4032850002020410001e43c81e0303000d95020800100700050b00207440c0011049490f00410701312288680404c1901c4c171039468040c4a0001014559031b14880c00901801c0c0d0106c50025030003c03004003452500221000314103180d40026200e05500100200d0340c0da02404040e410707522010010041e20b85955600f100c1640098003501c101521030544c0d05035030f100c1544601a1844000012803180341400038071017203481d01d83c0b08806102c0244010442511b801d640154241e40695010880e9512075020442d00c16600002c6403031150350b48104020700d40d05501070001c02c846941c465442d51500c8044420b00c4100484446c2c0c80541103000852541c000e002847c084203c9400b621405c202500100d0304a81040e48008229802110b07407250640d4001d19080d1403207003d08000e4101039a00d5582c90040c0002400300942a50344d0317140c8484030b40519101e01c011a030120003803200f201401200d40c2503404510070640151861894240d040c2e0012085e2025542c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 919145998 1250 919144748 919144769
    0x1c02030304031407060f0f0b04150e0f130821011202031e0c061804050105060403170a0504210b01080601290f07030507050c0a031112011d010e0f07 65
    0x41d405820310f9a400014203e808507a00c41a404401c1c469016003d80e18284038000142c03011114140002d84030400c05403031510320848014401c01280c01e0403030307800002529009042d0b90711520340b4a13420713002140140910700041842c1084582418031a1141312110b402c5054603641e80c0390f4400500000d00001b5495003008160311800c85c0f00070b50f03440c0e0307204520301215019881a4081020380e405203515248421105051020905250041c54010101503031028503240c919256844035101900104022a0b400117007500003e00c240107480290140c107004041c2000c2c1100429840c086d03030482111410403020000844100201d5142c0c103e40030315540840042403550030041807842218031002e031143c01d1003001e01c00b5195002815032107109072140c0360f03244d4a40c00e0283c5400d10300350000f03120b1001003c081c400500103d0741d1250000042d102c14020942c0c610081d0702400614595000404441420b5131005205410002d484034079071080d2840111f00181c51500c0c1c1140e409084c2c42e01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 919147248 1250 919145998 919146017
    0x1a0a03060b03040c060c050a0219080f210c0312070905031c1e180b0705061315020a270f061d0d02061b03030a0f02090a1401030603080c1c0203030403 66
    0x107034016000c0c6c9003600d2181c4141d8140381e403a40d00007807035410043d074101e4290103903900c24020307001d00f00301d500d0024003c880109250060040d460b002c440e1003049950342c0d500085660103168030108180c4182030400c07003a0030214608014001c000e1001c51062521074402e030321074415146008040000040120f95906601015550b020040b41c0c00070500390081000f605108500c1280c0030445a014000d00160559520700d03908100f4540070019000311404011495400c0c0005c00c580038519660503003400c00741c0c03501c1a007002910807440801200d9400e040000340540c45107a180700c142c0c16205540c0d04d1030b5000740c5030701d41220600a00140da00c00d0b040c0c803854612542c600704210890b0309200415a07031410030065140380c070010744074031601d00691001c4203104c903140c240d004181440603030322011424400f040e400115481c007244640000b1041c240381d289016403107504080b003e1908824803c0c0e4501440303035a1f5544400c1022440120038811607001c040b2407020045034083d03600740e034070b00310030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 919148498 1250 919147248 919147259
    0x2011d101103040308031305012304120e190f09021309020d090206160309060804052d010c26040b0c0d020910110c03010219050906041a0a03060b03040c 67
    0x400d540c100074803032548000e200000c00540725030000c2d031088a4000a0f4103c800c440c3c9011401d542e0405205864400c0030202ca1010034103042c4ea4590258100e100400d07442100300701510411503260b2b005400810b200c95840c10410031407035050485903a01c0c5403880d01507907800007004a0081403041c200b95011100304210003404e40d00688602880c100c0f00042c03158580d80000d0080c0d202c000e40441094980b403c071411b06402800c207000410b005e080c0100d60340303802d0f590030b80c64000f0207075200c49288407501e000a00b50388814120b03547c051000020081c0c0c2c060510007070000c5400c5007000118800040402d5022440000402e00565100b04442d9143d142c02c3c0711041150070032505004c000e80d007030190610980d40d4000da00c5448601d602d40041c0030f4104061981403c0e0f40ba100301380260700401c607502400302e805502d503c41102a103400c603102d510307071300018402c3c1c86162b00c03050300400c4032070084a009a00c10000d203051034044e1001c001250362500c0d0103065002c03c0741c0140420344c00c00c004118 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 919149748 1250 919148498 919148507
    0x6030b0c13080115030f02190e040b0a020306010c1e081c0b0f1516020a0e0103050d0e0108181207050114011508070c0602090306010602060a0e0109050d14071a0402011d10 75
    0x348014440360921403140d80b24035234000c1740d900078007036292000280030030300103004206078001082407015880c500e000c1700080c0900750ba41c4002003920003004240a0215003880f88000102e0340318561541d16078603010b007100f0409403180344c44035440c07078032104d405e06142144c2070319009a4050840c10b28100c611031004469006012a0b003003442d20850711030f0069071340900342c3c406800403286403000755045041243c604030580b2840d01c1804122046000310b0303038211700c446a00c00c92003800303400c2c01d01c0121545414000b20304810b040050000c21301c0400c02c07406400943c01180614545200c3da07070b84264101050303000d100e0301000b0500e0311000c40c0c2c0003442000040c032814011440507142440b50b0002c6840c0038800da00c00001070b00803000380310f00c40c9010301178410f621040000900c14100981c850a44a90b4404002014030000070003079190403107100f00b42d80045420452464000038803142034004400101c804a000558004107260042c0407a0341ea918000c001510141c1c07a075298441c280c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 919150998 1250 919149748 919149773
    0x20a17040221070f06020a15140c180d050601060f05040f0b0904110c0d091a040e090a0c080607080708011d0c040b04060504030c05120312060406030b0c1308011503 72
    0x10b642c0d0080701c50124a0283c0c20358020010101076004101014090404001490715a0008640384e801d00f00c031002c54180454400340c04c410700201e000d958040301c1890351340c03404140b00c030a134103c000401008240030300420302d141296170a46402e000141c071501c1c01c541c94840c0703000b640352003101280c05001c5901d18201038040f0a07409000000c030740b002c0203542130741074010a66000040d805140c0c100200703a8806a08001083c0280c0c480e607100050f403903030248502840c00380d03002241541e0002025030508010380006640c201e402540360035203401a0940340e0004854400208801c2c001140980d4455080141258101180300303c414010780e5006414400141c410307148604103000220b110208400180300412940e1500e50f0b03103d25501e003c1c0c942510700c0e44658440c100040c900b098070980441222035030440d482040d4070a07900d240c005001800e598102512040c103180c2040652000880280060410b8600c064206a5a0706800d42610710091195000390046481000018545104003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 919152248 1250 919150998 919151059
    0x905030a110a0315050412030b060906071707080406091a2a030c0717030928030606030b2e0b0901231315300609020a170402 55
    0x350b03581e0f50307403606210903c1c040d41c20040503a80b0424003040060603116070064650f1800c0a012002800b40041c0c040d00440102500501000500a04000c90450f0b0b41d088600b10001154039192a414030140315042030003850f01080d40c580300440d842455064074628600000421450103e01042c0480325158560b0400d8410000d00c3e2148414a81030020741380080d420001001c2c981e150030700c0520314076041c00b1206030a420402420543c0e86800c0159007103508104c0b006151501490791080b8003404e90b900192509107045004020400c51716081c1d405030804007100c2c02d0192000740586110b024481c1e2240114520440030440000102e028061940d07050508441410341a5180c64441c2c1601214400c503240002c0c0004208641c0381d078107001781ca4418449406d00070b2091029004520101c1a01d41d82d040088079501c0c2c0748501103d054204016180034441e01c2c0da1100c204000c1d411034400203002c1100c0c0344055206001590116100d5500148040c001001d040c94440f40800104d084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 919153498 1250 919152248 919152259
    0x50109021302130e040b040803130c15080a050609041101051c0e070f0305060f0c040504020a08190905100c0201021303111e060a140c0d030207060b010905030a11 71
    0x1500169481e2010307070016020518016075500351550760b418008881e9000459102000410302001c200032890046d0701581c408200781e6281c8400c119005d00450001000300b041c0d000c0e01f0003040450340e0801d03981c007010740303a01d034400c144d1142d103981c000f690000c40340e03e030f0040811400540400c4080c0e901154010040c1813180c50305d002c50202d452007081040340710800c00c0d01e901031008520400c001d00c2e0020150390850104c41fa00350380e152a12100003030203511120800c1e202040300000b840342103400034030008104543d10b02d520480501540317022030b44071081003030128404061082d5401031000341a400310281014800307000c0804002c2603000102801c5643c284540112100c04040d06009103010307048450f0403003600c00412004d03410368926140000743c0030750280101c2c0c584c41c06075070900081c1d040c540407100c0e81640c038400c9402000408421032149201c401031854142c0d0080c100980a25420300540701c0c2034006507250750451007407076055407001c0b56100104034141390501605500802 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 919154748 1250 919153498 919153511
    0xb271504021809130b040b040c050a180c05041a0f1b0604050606030a030e0607062018040e1e07030b04060e0d0c0201020c01120f15031509080904090501 67
    0x100d0120307001100c84000c02c22490310701d80201c2c9081e0204541c844803928001034010100d81e0340d0340d2000030141c0010410444480490300b00061100d82202130f10300030b403c8d803042541d21031303c2c1c5581185200350643d1041c030b42082114003510500461b010b4940054020308041ca100550f107060b0b40c03105240d480340c003500344008080c88450350301203c000c0044030000e00d85400d0034100175003894400780c08140300354041d41d05007001079004549068000c81c1226100d480fa40c160a1800203004007030880502c0c4259143c0c00b81d84081402c010301070380240c00c844103055141c000180012150740314204011940040f038520020552600d51141c4481c0600a0b00c00b02642c9558540452000783d804440c001c3e194850314104071000c20205220711560314141c0449061b50300003039140d0000f51a0241040a46410080d45592640081075100401e0f00204010001d911400c14000800c1c0030460f480c00f0f030700341d18198002e406c1c000c5d04039140e00b01c21150301e070004000402c801060800b030101c0707481d503c400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 919155998 1250 919154748 919154791
    0x10603080a020d080f061c0302030d090b07090902180f2107180b210a050604300f05160503030f04060605100e0409020414010603060303030b27 63
    0x202070400441560002d00fa10307a0041c2001e814078a00a00010540c800d2008204c2c0725500c0d00c800d0040d0400050055181240d0781c10201d003184070341a0610100c50500310342c003003007040b0010300398822145a61010607903a00c0f0354010381603110315004200745e060045d03508080c03481c02480318511400001d01281c1e0441c3d8485509084000b500203001864010740c900700321420155551080440d00080f041003017400040000e045046510f500e803076003401c2200700c1c0002c400204006010241c1140440d1030710300c2c03d443c1c49a504162043c41e0310b10b43e82109480022136148110381c4615103426120764684040040c07086441d6082400b100e114200c9049007030001c2041031009500a034501c0720880d40d980b0b80b80c1810300564005a104900601d100186606c5c4643e00c419424062107040306c01140d1001030f0700020f4090700c502a119096404c01c007000140d01c1e50103501c05812203100b03450034040220b0b450200010724107214051800030f24030012403519030007031030070b1990300180003005136050f58041d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 919157248 1250 919155998 919156013
    0xd0e090a0b061905090310111207091a0405030f060709060804051501080f0f06131b050306011229010e37060e01050f0618061c0e0d090b090102010603 66
    0x10003804001c5540010b49001c241024040c0741c40e01c4500d00c03000e08c44d0a09295868240d40f08d11480102c1381a03460300440e0705144200040e000600c00a030313115520125000c00f584166100744a12446449180710401d004d0101240383d07441001c80ea21800d645500d010380941c0e131504003c0c402c035645c2c0a80249081c1c162030300c4440030b002e02055001020003d112511aa04d4a04840c14020345540300c1e008100464081e5550f0603031440d032040b03401d80f0410ba1055041d468410913000582c0c10b000d840c00120702c00e15905020101540150300c5285100004000c1040403100d601045010388030400041c0420513803500c030b868105419010b070141005610001b40200c0004008104c03503908462000000c0c00c5030b501690000e0920003141000c40d5251000240400c00071122140c00385501040284024211040001a4000103010a507454000b419914400440c001007180280d1901c050003001c40400240d043e109061a2a4040e80310708015241c4981c2d001030304841d045640b900c03808000150413 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 919158498 1250 919157248 919157287
    0xc090603070e0d061d150a09050313090b090a060510050703021603050d1202120a110403150605100e0102060402130b06040b0703030e16060f051b060402030d0e090a0b06 74
    0x4000c00901d0605c5040d101c00c40c1a040000c401c81907204104e07418844052402d81c9400680c040750020790f0200d20f03d041411401084085032101d0300160000407841c60a400c002c1c1d505900301c5401c05603950380d421721000c603030b02406104d4000602c1142c000644c1d00070002080c03646c3c021700484000900b221032015162103180c0084a160700040c03011007c25800000c1c00c0081e1600e1079043d414038000201d00461020002d007a08521601c0c2e00100c8000b048503002c45014541280c41e5095419240386514064031481c407501e405110040503007110b451040b031b03444140000580c05480191900d03020804101c40301c4020b0b0407200e641b071031000030720355690004000820001403804c1e107803601400c02504a07003180903141c92940152003c1400c103801d884a03403054400c40d0404a103001c0d1020702c115518014030000101c140c81190940340140c1000810a100b28403c404803800d920058034126004840501d441d504070b8080c01c0130952501d0203070044049d03840d0280c00300d401c0030081e4030520400040d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 919159748 1250 919158498 919158503
    0x61707140c0a0c210521070c08061b04030f031d0d2a050604030f03120608031201090c050d0902310e0d0801090506040b04020a0e0112050c090603070e0d 67
    0x200080204901c00010700741c1080701c2d62000050781c1690003502e80d16201c1e00f85140325060840c041c1d840942008084060f1842c1981190310002401d8888140f20381d0380ac0c0039179540c0040f6900c2089030800c80c100d0006c440c241c0343d00c50500c1201d40f1069030241c400703018180e00d000304494180c441200a481c0c148401e15450b0080310f03d9959804100e1000f51608236810003c0d4188410b580d060040e91520422101100d81c010034801c10070f03890717080403038500400b09841540282000800109241c000000d044144101501181141d0340d5000f0358040700c84001c230840c041001030280060b9a5000e601c105c0c0e13000d001500041d420b8401295038002ca000f00c40e50203d1003050307000d039030141d03070080e1042130088401d141c020b0070fa0200b040710283c0045414815108881c0d02e4800152468640341c002d0400f005014000359240d02d44030001406126600310700c00d00040d03210780c4a110700801401010b008145901d0010300d0462440b060104580c0000d0260341801041100704549031514089503c2c12070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 919160998 1250 919159748 919159763
    0x30c121109091c0f1b0b1b09040c080103120306140f0310090b010812041208070203010e070608090c060405060906030601090b0d1b020c0315130209090d0801061707140c0a 75
    0x10f095039025111044061185e405551005800c1e40058000c04680d600314410400d4083c0f0500e660b00301054610840203200d0300241002c440840280e0400300c440c2c10781b40b041c00030282019040004800720b80140c0305603900040c01016455407800c00c02d28110b03403000080c054883d0403034011101e00907280706010031507a1030140001000500410b00c42d00440c440641a600d2504c5d1910440c8808403901000141a041c80080d049085507425400404598a448251554180c0d84c4601401c0714404480480c01801100da1141151030040308407416541e006050310300b00301d00c0500b44020790300000d0000307040c480651004200a01c0c26000703403202004403040410244440c0b103c0502d01c2c0c190521503000e5602c031034030b4072119136804a0360f4240c0949200045000c1d40e525040c10100b005888800794010720060b0038401e107580041448104070300b00e912001a140d903039800856050103801c603000301d000b4400b004240307413900c20075056480c2100c2040442c01e180f529511241400f840582c02c0702c0c41e2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 919162248 1250 919160998 919161017
    0x90612020102010b0d030e0411120f0708011403060a09060b030f0d0207050d1509051908090906090f041b180e0c040506030c150d15030c121109091c 65
    0x542e03090003502084213055981080502c1c02da94041e00c4154000c042c103100b19203a01c80d040203a035501055903070409012146001c20709008401008400c0c06452500000c0c440380f001140101050070201000c11010b001030600d50381c1e00041d84014454514115402c503180c40c41d10860380d8042000403403c40e01e00340900342400811001918201a0358030060099070320924180100d50f80e0070f035121030000e10b0300000c2002121442e041d42030004d20300c4074440000c103400a4505024000300136100d041800d95004d012622820104029000708130741c5174140e003a000b000180000c0f0011000f40da944113410344403a0705511400741c561665854124070b54207a56915a1180058040009245503030003607501b0132490600741c012035102d80a042840c0d0244200ca40c04621451541c0b044a146081010b0704010500e1403842c0403d0100151006440e5086107400229605040d9001136201d141d014007030001002d000ca0520461b80c20040c100c246c2d602804590140c0c031b40318074110019100b4280c0d00c0b00d102 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 919163498 1250 919162248 919162253
    0x6030c08030c0f0c1309050708070902070605010801021e2b0903030b09060a17031209010e0d031e0c0507120509040e0c1503040c030503040e0402040b01022d07090612 73
    0x1402400340301c000c40b6030f00c80c000155150300d0b80303910042054110603002c0781106c00b03030038030601d001c103141d04c407403000c1c8200240001c00a0455000d40f01c00e500c81c00090281381d03601d2081500340d00038005103074502c40754007006401d002c04510007440c24000302000094403403e003031045c003c6604101c45100d401600d0340307001ca08155040c41812920b000c2150f90306a2800d00c4404210012407600420114203000901c084920300b040085d14036155001d07405210750f242007a07103d4040c1c500002c2c0c20600d440746407940a1a00d0285c000c5010900070920365140300d80b84460b00f40c018045603101142444401c001c0f8801060035003c0917240402da41d02c0d0f2590350790354502480300301c50210f07481d101503411440040c0e8640d40ca503c085405180b242e240700c1d03201d46890620a407208216800107040340300004001600c000705100d150310a80c000c440401c0306e1016003005989510030b0940c030207604580c18581c2c07142c00148084420354045d03060b040710402c980390b924250841c0d01e0f0b81c015a0746141c407540000e04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 919164748 1250 919163498 919163503
    0x190306050f071d060c0709090507080f06041a0403090305010c18060c050303010b030c0f1818060303031306111b0705100912031403011202011206080c0607050106030c08030c 76
    0x30440040c2c58000c0c10f1040080e4202040e1079480c0e8018400d850015400c40110001c000d00e90180c6036442081014000c0da1030020f980e03803014465030f511406800c96a01c688580403410511440e0040c0307060007884040c410000310300c2c400a1080f002d00c2410305011020450900c2500c0d14103800e0f80324141009000c5204401191403507114408110f120600000081c5012050340d04407122017142c0c5880b5100c07142c240c906405207854904007071038003203140303c00d80300100d1544e196000c041d81d00d1790600080c10900107191204443c100d0305035004001040001d103d07110050340050240000003003d9040c00d01082940d031004800d907140e1004400060001c8005100380710051008039000b40a04204446c060280d0b00180f14282c04a009152582c0615002d92043e41c0d10304030062000e542c0750784030008440400303001c15059000038a00081c2d41c4140c0d18078412007003031394201c07401820280c1c256020803146900243d0122619503e9000000004003506510300150100401950300c808100c240d691 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 919165998 1250 919164748 919164751
    0xc07021c030e030c030d02030a05180919060e011214160b0403020a080d0c030c0503090306070f08060d02060306040c03061502060708161d0d0b070201020901030f111206190306050f 79
    0x1803180c6c21514403030300b403550000116040285203041a644809200041c041c1085046000c290403003004c4007000189110000800e0650305240030401607140c940e003c1c0d84104000f40284881040051255001709902d0111007020717001c100101e95001c0c17602c3e82120186551903100c1503403902d0200b41030003185444090b8101404000005080c0703440f0b07120005011b08090100038051010002c007800074400203004231040e600010f41101d80c1814501401007440300c0025010000800e8100070a00920b4503034809601d4980080c1910b0031030300d501040000074004803003400140b50b035074000055031703070703e5480301407011407403500508007e1910a5015100030710003001c1402c0c2c04080300510036030903003022443c0c1201c1c00c0b00b6401e2900c1da1a403008140030f006642d00c003030208115002007110302c2d64150014500b044d000c0c2d90610280b0248100203081e955182b401000c1c0800500070440354072a880d80c501e45c4000004c0c10750803c288002c0755a402d462607508180ea2136502c407010428640d00018145 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 919167248 1250 919165998 919166023
    0x102a200111030a020703051209060103020418150f02130803030103290123040e060403020d0c031d010324030201080c0702061206061e0712030507080c07021c030e03 72
    0x910803081c1e05101900948802807600c011280e01007107007000d2512a806850300000c20910720703072280c2030040c0d40f07660360142440102d12070b50a0102e60807441c0b690490a25981da0301020268814490721100b6001d030400c1c00b00011821350070f005180910400c841d80343c005001001c00b0310b550b54110b04000e0b0b4050000007502410340c1c12400100d4240e005070840a04540d507074807554250030040040c080f2501c440c0b08559030b105003400d0000302c4514000c540306d40241c0c404e400b120129001c5c60001d641425242c0b0002d00414140040150780c001c0803448e55854920525000451100031950210b00740a4401031445456240400f4021540c0000405410480301440a820003c0560010b0120300c20000d400e0000c0382c10002281036601d9440540740100910203004241d06d0344502042840d07002400c042d140703140403601c96802540280700d218002c2c01690340c1c0d10015540e142d4483e41651000c0001c07070308862012640f0403100c00c04170004518500c0781da1244240c01aa40815240c6010400720 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 919168498 1250 919167248 919167251
    0x12020d12020304060605040609020a0f0f0203120c0714030a020f011118150f0c0631030504090515190e0112050c030a05011b0f02102a2001 61
    0x51410603411008500000504680c096920ba5413854920054400c40c0c2c000e98111f801c2c200007050000254028280c6c0c0e00403030391200043c15190a00716a209140c0c1036410244c0c000304608032513040054411135120609a40e006d251001e42d907214010400f203030030484516080070603540340341d9138140505000454404001d000200c94542d040d092845018503144000303c0080d9113110380c0e16184501040f100c00307460391988034110420000c95070742c401c410020390ba000c2c00c0700042d902084ca800e007880c60452002c0c000080b00301c544040e00c4131200c4800035803c1c000203000000303003000d9174001d1a1292118031010020603150320280500481003148042034003407121018001c07040f00351201d504540100e00302d40c441a5150070a241880c1c07281a505405020306d880440c14040150410035401018003031103032050148080c01ca13100006403e1000061b0442102100700c80034a0300690080c03001c8000d4810010080700c0804008811081b460340843d5101100d450384800d40b1082100b1220070000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 919169748 1250 919168498 919168513
    0xd1202160e0a0515100f1407260c06071e1d2403130c050a081504060f05100509220807050c030a03120c030c0e042d05041202 55
    0x84945100500c1a200e455486000816504d0007900807100c01c88040c120840704d240b617210040c6105141c03001c81c00490001020020380a0020044400d2660132414124000c0e248030030380f2400f0440304030215130581c030900c0b00382d5008106100131401303550a03498440304804414481d00c880725041c03044206201030007803600c04a203098052400104802c84020102c00750015401c201c8140350b8200d801180c0d004010020700008440e8544841800b44074141b03003c17680e40040099400c1240941c0009400441050112011000a003174115100d00c4011a04003122020241290b070308489408070043d400108005508007043d01580000c58071000310280d032030500540c3c2d4102542d03580240b5a1100003059424490140326401d0200401810707100320510038100140314a401c152081031482c688501c11400720301a01c20b5a681981c6500c03010b20005080c0300f040018400300030088903d68464203c500d0303139001d950400303400101500c00080c0031704140c1040c100302c100b00400b40066500825 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 919170998 1250 919169748 919169759
    0x3200607140a2f15060f04090515040f0602070f0303111905030c0f0301081b01020a020a0b130905070c0507050a0e0f0406060905180d030b2206050d120216 68
    0x85410004603a420060095107909400114100c807641d20501c81d50240c03003204844c0c52000703c644c030b010b590112003e030081c050300410041104c1080700c005040e9489203540020108108254550060003004480e030a4001500c0c0c6038181c1c0d001c41406c80d404500c000c40a4101a014811141030040d400012402d102000000c0c0c0c5200c00414120002d202c03001c0006240003c25000701d60544a1000c1c031180c80c4d586d105021503940541440582e50850460340341401540300150701807083c0d4000b0050312a07540381503980d1302c041d40005440382d9660480e02c40460100c140c1c1c0900c0f8040c1c03020340d44e100c00b4281541001c034200441c5403c0280302c1c00001030204054a44a020203400c4400850815031a03141c40c030740000103085a510441219042c0b400704585c8070140103c40100840740400d0720a400c490784011012100f00000304c55100300030603920380f08422199084503400303d01100015400740c80f000002c00745180d001d4101e0304026281040261954144002e511008106030444842420b00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 919172248 1250 919170998 919171007
    0xb040605071d01110c03100912050c1504050c040903020303010504060b0c0a0201080705041a070209151f120f06050a0b16060209010c120809060c040f1203200607140a 73
    0x2007641504002c00714140d820200014011704481c18001011109000120a070050150480560566101200039040243d0790700031001c8032000403075400908a502509140003402e9103025105464a2060400354000d5444900c1500c11050107030f00155120340c508810001031b41d191703400280f1005014000003503045400203020451540c242045078180e0b4a010040b5164025030740711212400e003d004440c980241c0500a03c240c500a94101000fa41e03426050400422404005504521441042d2211042482c0d401000710300030b29100d81d180ca0324141c00750a803801081a02201a0f44031020046071920079804070003000d070b00d441c6a0415803040550000c1e101c010002400742c0da00020101d0300e58ac801c0d0003c4a4a542c8200c080285400501c00200301d00300071214281c1e03511403280410440c04840050b98100d540c04940844a5030a1084950000304261800c5080c444110142c00e01c1000340c0780000c40b07019a8074018201e0789000740f4001d1501c5d1000030a415207500410100c481513500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 919173498 1250 919172248 919172297
    0x708010e01091503061a0a230402090d0f02010513060306080c0f1008150d031d0316180609051812090a0e2e0314160e0c070501090b04060507 62
    0x760008440c0b0103040e0381543c3c102c0b0a004c0395800402000c004c150161104140f04a020720743c59031fa00e088c00c104050004034454680c0807a8000402303039a1500040051440c17004c481d00c1031400c0c42c141072908500b0300c0c94900b140c02c1040401d07180c6406101381d00f03040090010f40e410071a40c0e000c4049201d40440c0f0140098071500041004420001e203406403050324907140980c014240000010040c100204581c500342078080e010041222100711a141c000b407501c440d00d0340180c01040c0d0514000324900c5400400030414662526850001000c12903880f40a01c11190000c0320100848140596420a1400c0c800c5116411040c004440651218507040701901e03500344060320b6030b0b101c861181010075250b0748030b1010007907001149469044050300745401c4900c01c01c401204000350922440d1503c40c2da00c2e0601c2c2c28035142900b001030402025a06420001d485441d502d4841d458542c182594905074083d2000500300040c002000742d5803040c1030740a0348510300b90000940c030046c000c0d00e0004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 919174748 1250 919173498 919173503
    0x30304090b2d13060b03011214070803031311040510050321040603020c0c0901231503041e1509140604030c110310020309100c05070807030f050c060708010e01091503 73
    0x844800307250f0700c003541c0010050505600140c1c2c80c0e41c2e40e02c560700c00e49071001c401203a81080e400000c442000b40012140180d410b00070143d410b5548000d4a030180300340310f070003e80e00c801d485800c1e51001c0c1c45511885005d036803c1d800e10b072000f030300700800d16140150644055400d2260030000010300003c0009032400e41d50107150141e55551000f4070345191110140340240e1044a080001600c0d00303080d242d03a100d680e0b404200d0108110b100c81000056a4490105900780408000103000030b044101c01001c0244201e442e80480c00c4035450701c0c0000b0107001d80c0c0d00c00043e51969007074284000c0700400a00b034081c4000070245072030550b8004002e075005a800605d8420090447c240702d54090013103d005a1441108640b80c0c540f8500981c5e4807406e1000c0c4182c000d1401400b42071151091081710000d0f81c114828600c0c0610756601160014005800c0b5000c006082c80152035800b014840c00340a40c0780b03980c0b001c0c1d055040c0040d1550280d8107070320a4404500d800124030b24502020545800c0320b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 919175998 1250 919174748 919174759
    0x20f0d08040f0201210c090b0c06010e09070305060106050706050a110912070504230109180b0c0f0a110c0306061809100c0815040b0d02040e0c030304090b2d 69
    0x40b620042e01c0700c9120142003280030000d0f80d0000302003105507028410749004c80e969014402c0d682c80419295101c1d013007064045400107001403002d100700140094100d42d5140895045556a0f11101e0030310300285c201900241000640c0e00c2844221300800b0341059074401c042080c0c00c14119034800903c0b07a00c41d0039020306038040c40d5086c01034052003640000c0801410910048241b0140004100c3c4980310048240c0f500c80004201c422031072060780c003000c014001c002d0081d0001d031035840c581000148854804c103810000d5025001e1060040d1150400584842040d2044060300320309285110515502950104042046540c1d44507540c0080d059444d140d03900d6070312640411070030420112030322030040c0c0c103021202c41001d500c030421500c0ba5886c400500040486481004140c440c1310b0015540070b412102140c0262501c0c0c0e0103000d0640801044440c0d0a0300480400c0c00d68205074800005d80c0d6130f0340403000082c2451000c035035005201d400310205d8100ca4a500d6075007280c03e02c0c3d03101d0054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 919177248 1250 919175998 919176023
    0x3061f141f090e0c0406020709050f13050307080d021c0c2f0a03020601030c060309030237150e0105041e0309092a0c0b040204051e04060606020f0d0804 67
    0xc0c0a80e0420b0050248101548041e00c0c0c039244209490b44240701e0400144201c40e03001903110f149126250081450042581c0c00e42c0301d55421220120440c00c00b59040d000800500c00050320100043c036103440700d04000f586a0000404000c0c1c0d400c0165a904980c0b4200410710710000d90000d0542354252a840b0540351340d5520b16100005a100070fa2500700b40e10990110405060b000185541240c0c86080f44c0c0411580310007044050b41c1c00b450008016911000c401610900c6400000c0c60501442400ca102c021200883c130541c0c20301c0003420344849030710241c0c0141c031101c81d003d0b442040c81403030f000b40201c0c1090f07964007000380064144c4e031940500c000c40450400d880b4044130b1000b0010b001090100c1c410400d810440f002c52242ca51000c00d5100f440117100c940610008124640c22101c40c5146a865409010182c90010070828110190b44900c0007040d181c0595103005602400d07000450704d080070300180c80c4c000018503903c0580d0100c048810156400111b4903442079000e074460b03406 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 919178498 1250 919177248 919177309
    0x50a03050c1905010506100906080105010f11060a0e0d02030a08010e04060605030a1b050d080d0e0f01180209100e0a0e01110c0a030f030203090709020f0903061f14 72
    0x1c081c1103004400042c610003100206002054000c0c5000340340480702d0105280c00d0540584100b0300501c1200046071104004000c40d600442880c80076003c5801d05d1280d07456241c2e089828100304a4440c10000e648054844081404008950281c11280001c5140130400c010181500905125400c16880b0b9072002604208132a0000001808064215041d446607450700300c1103481116002141c0400001d00040c20749090120b5001d099003256070300340340c1840000c029015040502d4040050310039690301000c0a0000d01c41c61407000d2142100f41c9642c0928410401c8000c2c01038801054040c0b404414804160012030b602d42040c0003c80000390007207191580c80c0508103084c960001c4081c0451304402652010504607274480c441d030358130602045541c07000e030101e0000780d81800c229400081e062100000c00d500a18400c00030106080c200302039000002d1500c4012604107440200040b840d007090451803080001428000c041c1101030580100812a24212003d02c002c040342d030850384040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 919179748 1250 919178498 919178503
    0x7020a0809060706020a0c05060603030304110402030601020106050a0906091812050c0a06051305010b09040c140303040e07020102040f08070b2a010905030901020d02060906150a09020c0109150207050a03050c 91
    0x940c0d006005545071b05510001400000294000b03440c54000c0700001041450f011080341d00c079980c172020307043c01001440300b484000e4000801c144d040d5980c5000205072a0380b1a01d83c10010320305181c0219196003805454810345d42e04929140220140142c102e0002d17500030f403411a0301c030a0b880d1071a290015090640d203001c41402024045c1031410042c454050401078100018900031402841451640402d010034020220340180c18990309407030034045090b11a22881c4460001000c417424640c40e0307107a800740c186058404a01503940080d040066403d0002c0400003002d0800190030103d02d0000481007600c2985c004840359061701407494000c02e54580c40c5004101d10000803c011016440d21650301ea2021500b03c2c094403c0e041c1d8030b200984001003461140d072200c0b0140ca11030b1244007182c1c4a10b030f502c080c4a0303030002a01d200840d044d01c082c4003503c07010f001c020004c0b03101155410030455260801801c150514010002d145c04500001640313841c103075140ca052503880f004900d201c0d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 919180998 1250 919179748 919179757
    0x60901030c12060b040f05090f0412030914031b03040b0a030b04061512050606040b0d0e030708031015050f0a0f030f060605040906090c020703060b0307051002030c120307020a080906 80
    0xb5011440d100c4085001800113016200b62488500340350803041d243d0007000303501501120b8083c00700d1070000c00280000c0503140e580c00101c50500300480d2050301d40e50761140d00401d0000810080e8404600380701942e090601d043e4000c080078001d90f207807600300040001e1038850310b00d07400281074aa0001c40b059483e290300c440c0003000c100c0c2100040d171102e0031b401482050700001500549003024040b076164076020089030b00702e854002d665860b0101d4159060042c0c403402c0b40500480c00144580030202d001c900042d881030a0085600120504003804002501180640e100400c41c0501624a42c1c038170309002c64074141203505281042e0f424410040740a800e0841040744454189180000c0f40c0d034101c406001a500d0b080004d10440c0d440311041c608458500e07070290010390100004102181d2903a0081d600020007038155814a900c410110740da40a88114500045e803002030740d2040480144810f486048402018074039500344900001d40d10392001e04054100e0100140a102d15a41d0100300c9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 919182248 1250 919180998 919181027
    0x15020a020715050315042d06030204020c03031006050702100806030a0210030f050603120301150c0c1202040c0903050c121509060106120b0310320711010506060901030c 74
    0x2030a40c03548034001041d80d0070543c2d19022180820620302521b1404e4042c840d61040054a00c2c01003040c0c80d00300030400c502c031001103007800b13580b80d01c04000340e196030008021a009110081d542c0307040014503000f40e0032503030f4007402c20403d05100701c10060b5160710740c003454100d1300e20b007000c8161a8400001c2c00e05c0e1304088000c1d4016000c1202c0001c40303405420403140e881c2281c03010440c9039104018140c46481c0f0f422007030070481c41000140709085003c10384808000280c9421104070030070b55100d4841450382d0b0090000e9217101e150b100118a400d000d503000c24502841c02c5c120a0386199941e030f40e2115540450342c420044200b01e20708403407082080322025070200c0100625030815400c45500c0c1e410a006031000110141251030b14216103000d2030326661009002006203004840f5400020140116110310b2508907089000d40c85402c00c442c1520b09220096000c0542002c0c20040c0660400c0d881c41c08160b41018200103032980c0704011b07909010030038200402c040c0d89400c4120703825540b03901c01c07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 919183498 1250 919182248 919182269
    0x30c14011b030f03060806250c0503071b0b1303080a0e060d0c1106090709090821151c290112061d03031b0433030915020a0207 56
    0x141d0a040d8410700c00a407500c03850700c082103050386440c1d089443d640c00f1148000b560420102d0800c10000c0c8008480c0c0c0c0841c1454590101d01080d52260b0a40d17004c80d078152070f02c142d503480d84200c2d600c860040710010040c03d03810303d01e00300e0280f940001c12400e0344805016420040359005045000e000d15120340c5c480207140c15030b151b50582d0031038020034144003c080051007541010641050001e02d45000d82c07840401440e0062620308404041c1a1145080724076003802e01854140d1b88010002c82003c0b0000c01815036540340000a002e102c1180360412482159a96241d1009210581440c08066000400c488130144501c4015242d6a0159603440900420400000b07411a40c5003d914400c0e01c40e09091103208400041c51180030b045101011790f9030420400304812002070000440b04844104141c1d05041d80d4043d441031503101208004210b000c00580014504000002e410981405040070007a40295460f4004d0865034204440c2a0960000d0a4600a8000c00240c0c0040817404070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 919184748 1250 919183498 919183547
    0xe0102010b040905060a0f0e0a120c060212070305061912060b0603071101050f04020a05090a060b0d0e0c090906040305031005061b06070e01021207031211070203060c0301030c1401 79
    0x10507964034403044a44240c0b03141f4068000000b8060303401117484100040780208074800d03040d200e060055040000080070301620322034100020300180090030703010f0030010704500c55240c41e07180501540c00c01440b82b4800c0c000039018050f003903802c0452200b82c030303c104450f070f100440c2480c20071300604000652030f40c006004802c112040707902404601c403000b5510028042c2d51120300310000500416907000794008000d5000784028105450b08035401100d00001064080d951400e541d429845040402e85458070396a03000c1111404200c142c15080060342e0111007407506031007898403104060801000c10000102144200400071a4040a00390080500303694100c2d180c3c9214042c41c3d01b403116101409100c0c0007815840c09001515014401a0042c2c00c0101c0c1049a01c2025884080200c00b4012904045242e03100213204800310107402c4266541d480c2081e0040614000004000303084c2c00000300700620001c0c0ba0000d03e481100c40790410a4000f41068006803241c02000d101c600418001e02d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 919185998 1250 919184748 919184753
    0x1030e16030201020d030902030601050d150f0e0d110304090c0c060e01050f010801020a080c1b0601120605100803041404060e15100309080f030a2a17011202010e0102010b0409 77
    0x603811000c0320300c01d0b0211081c0c94000d16081d82504d81e421006541904800010011400c064036100703c95441218840f05040c2c00301d45100071a0036459030403810a580311801d1320511000c00944c08402c8180c141074540c0c0c030a04075015605d200b40c2c020000c25a840b0018610980c3c02502101c00c01c55005506100201e14643d00c0350091204039200c030340c02c0d8881e800000f0413010601c2203410070803295542070880d99804e841000b4a82c08451104480800c050010100c00c805000d1503004e040201180304840c41075080c940250b4030098070b00032240e440c1a104004411000084030102c0300c25030441003518141c03000040080c0720550000c0020311580b410444900307001c2a5820080308101e5000d2640603101104404840001800516090f82002406012200c45001d15404440f500001c01d0f100c7c80040b1860003218205400e81c0e018510312340d840b44058010190150599070031b40a1031143d0700d01030b03055030380c1c3d03007040b41c042e0511005808001d0164402e4011402d80d2070042c10034001c2c42c1091 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 919187248 1250 919185998 919186033
    0x10608060f01050901021c0e0d080702030c0f1f140c03131a0409020702150c1c17010b0c1005010b0904051605030105060c010207060f021206010c021e01030e 69
    0x21510030780324805000c03903030703040b90b0103003060b41e0b407400040e4002c15150b16000303041c0114511403007040040c0001da0007899056030700c0c40c100040e4148120101615440284141480d102440a0041c0b1408130168550b80c59141c3d0010b00c002d81d0740c084150260100c20901c140c81c0d150080e06c0d51003200200050f80401008000001c01030070080e03281380301169548004c146840012101c004038032600811081168502d2f58020b0030f11980000c1030034020100000380224030390b00007156081d080d000341c80c105a4000100700241038599450502000d4084000076003d9a240140621a0741c0c54000c514a11400c10070081480d2111070007a04215650b100c56618200350040d14500d0302c82d0b418a8000b8920668844410f08141440c0e116a0308503401c1404008040c0c002d42c030b4424082d03600744413080105559001c1c244000c00000301c0140d41e1124a0303914507186800511003418048851411401030b1220020200c00115102c3c40580900916004030081e0071142801046845894410022038451 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 919188498 1250 919187248 919187251
    0xf0501020606221e020409150b03040f060e031b2a090a2007110a060c0213020a0c050601030c0608090607020a06050403050f07060c2a0f021503010608 66
    0x36000c9409982c0d80400b080b080318400341a01c0c510482110500036051416082041050302000700c00003141d12400c006002c90b08640e100c102c0d0a503d91440c00200201707441ea0101814043d04000d142d40341c141c56a0344001004040100380d1940d810603a030303d0b00c5080c4180d41880100c00c0282506020f2100c101d652109281030b50304026031040798079000c048500090f03420501014102440039034071a2003c07002444010116041c80b20501100030110303010b880141100ca1003401c086841c0c503448402d110000c003e582040d01403000e948180009070b9034025402080c06048400541d81d0a900002107d1040d22914001d207030348138070800070040089410800e01503c0b590ba507030120f01e980345c051142d603690054a61308050780001c1c564502152280d008160320030300a041403440c0840b04040306090342c0c0302c05819501c40d950f4050398070340c80b98014814041c44070340004044541c1c040c05030504195846500050407030031000f000c40c007191980076120074003004810510b03032290b07550700019009000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 919189748 1250 919188498 919188509
    0x9060c0306080c0613030b091c0503160905010516081c39050304051c440603010603060c18050303120103230d0e0a05090103240b0402040f 61
    0x1242c0a54580d41001c4003664200c405000c807103403203146140c0390b8441c011f0303001d0714019681c0100d0380b5411003a00440245060b0120b95640d80b966807914650210161504440c5103003002422001000300341e03400003c1e220020b0741c20440901c1c8490130700d00148284686035a6529140f400040c850700c40d1015840141502009400840c100d08646181189a500f0040506400c0101e042e040d212a01ca980610303441803285088a0003a01121a1101401c4022150341e00050345501190342c6507107a014020405a0094045018030522510b202d070014581040008080b41000010b0460b68003500498001c41d004102081021100c1c034005104443c82e8401903018443c110f4002854200001111460382d0884e500006507400d41d40c4d034420200d03405044224151581803503038500541030040c103005201d951151180d1081040c00e110b000440340c0c1c001885075160704010804500c00c40c8540c11150012140010340000b060540c500808441000ea0b4102e840886d020038000c000c040003400340c03071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 919190998 1250 919189748 919189753
    0x603060902030702030a2105130327050103020a03110a0503180601050d0308060f090c0408070f050f040e0304030f050303060a0801090f1e051203220f0206090409060c030608 76
    0x1a200d80c1280c050348000e403200401640704200d4940300901c00c40c1c2c6281058802c00c450b005184404110304c0a480c002e0714003038003508a11204004058010814654102c50b01c0e11400d80403081d41402507141d0441d00c143c0707042c55000903510644c10b01c81e85c00780d60b104540c82c0c6420b8596800d07080042098001303c5202584070b041305c200004400c0000360440c100e6400900d005000c110b15501140d25080142066802800b01010307001c260b0781b01206030303203d0780444c00d200c0d4540b07262080075031a1034407a600c268440802c81000380700c1a11038580980080109442c0440c1c0c2e03003000c400161540c4119403020708050042c6241d03400300000800218090381084a0300204a500c80c0552401c88908440040c00441c0d40301169000902808841e81c456600908480c2c400499072501130401d1865a00460569800001c00c01d4800550320381e044482c01d040c000880701d012680e180c00c0c0e1014106000380c42048040f69038403e41d0381d2a0010780d00c5540c03001052041c4500305001801500c1c550194912070b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 919192248 1250 919190998 919191011
    0x801060f0609051f03020d0906021206030c0f030606040218032509022d0d02280e0d1716060203060103050a0203092d0313030b0c0a083601060603 64
    0x149491030003104c44a00642c1128580d0a1540c1c1c290b00942c028144440542c0e25012001c020501350b03c044d00140350880f25200c1c0030301e410400c00d8103040340460780d02e1069400c005420401d490005030380768810010b440044c4c0c2e031135044500e2002118810040d544c1841080045a424212401c070350307014000a4100d051859180d000742d000368040d4001c4011744501c462030013900e01507a40c940703600910070149211700c1c26118102450680e0300c60b60858800710301800c50104000d00c1186940308010051401c2c030100c244074030004041908120018104908a13466101c00f10001400c65541e9100702e01c00007607200013860320070065082110740c03602181c074100c001103c18400340201c17446400c9107000b40140030f001e40c07601c02203180b82580c044012402e1410082c10044d081008020000a261038204901d00c1c1d407819514220000b032100100b44402e00880400c1a00915002d800594442c490038821040e84814103100c0c500501c02d075004492983d00c2c50000078198031800c140d40c1155004c2c0041c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 919193498 1250 919192248 919192259
    0x907090e01020f0d09060603150b09061215071110060806070f200a0c080102031006050f0412020303160602030105030706020703050705060a1101060305100507080402010e1005040801060f0609 84
    0x300e015020300d0b14012801042030f81800e100540c01041c0046c0324180c001501a120749078906803c825091580c007080d40c40040111510381100401d510800c102d460220b55102006029100c00b0307100e00c91040200840080303064207008546040c40940c2640845056440c840d07440c2e0043c00c0d40d8881e00c41d140c041c0001068105104500442e0745c10311b182c40d050101c13045078400990080d4034031403401c40c2d40a04000f500019a234040380340010a652800545c8034204000440f40311403070b55120b001403203020842e086982500310300303650444074405e01c105100281c0d4008641580b0074999840010034808441c4001c0064650265050b201d0035000c03982181d8603450140e03900c1001c3e0001900990041800704075902e030000003052000198a400d009c5907000d01e2181e402d42c0c1c2c0e250400c0356103402a080c815083c0c03c4512406034441344510f4410b0490429400203044d403508203180b54007070500c10900d40d50300d0740200d08450040814600800c1a255a44520000c0e66814080e20b400a00780e02c200040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 919194748 1250 919193498 919193501
    0x2100506010320031519030524010306020715090c0311030f1506011107030302010f2702010e03030c030a02150a02030c0d0e0a020d2a080703020409050a06050907090e01 74
    0x2c209101207140c50f6090364000200c04503000180100c0441c0c030030490400858803524440000c00f6480100d050f00182586000707410841d24101c0c005540114544200411007070440050449421503401a564401400c01c050060021401c000140e81842c0c0700c01c08000b00c20300b140c02141d004441c124031650980d070406803100d0b044250b81c98150701c1110442942d450700c0044640040c0c0504010741100105074591f0b003803590340d44c030503000b50b5521520011000c0d10790007002959a030b00c00d1a0001c050f80c884c00080b0785200c8045c013030704000c1c6001c100c901c00e8a0400443d810016003c003120340711190000c000b50f44001c01d40403954030001e540041403c01c0b080c2d009481c0603000140c034040c1800c1107072624000030564001005040d2040104140158641c550b400c0340c058010f03200c0450040c86891b803014205980001c0d080002a01c41d0200020240800c3c900d007500d90446020514007081d0900d245444510b5401800c00d625140a010039035800142c19004c503001e04c1e1080c42100040d558850 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 919195998 1250 919194748 919194761
    0x70801020406120b0d02030d0c050705010504051c05340b1216050702040f0c081006081306090b01090c020615010f0833030f1c030b0a15021005060103 66
    0x404034608403488240030f0144e4000450b80d107005010300080e0881500000d01c2c08911031400004038032000c0d5824180300c400c1c06110045c19081c20824a8030349040085000741c08035180701142c0510f102ca0309410000103001c0d0441041c085060001032001c9603001c036651502da240e03d503e590050039400250b000c18102910041c0c1002586081550b0700c0d11108554100b020fa44e190410070100000d40050755680304050410114041c00100481c01c034a0240c90302001810401d014210a0003c1041960140c440365001c0b694140c1034000e10340303610b042805082100700040c03502c086400013140801055002c0c411591031642214034030340710018403541d20100c046405000846294543c15094007680940b9080038401222550101c52030b91000c412408045915001c2824101000424541004071034807030254200605403400745c08420500e00d08034240e0800034507403a0003d101160784d412448400a042442a101e005402080001c3d10780054441030040b49142a0211311254840d1090300f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 919197248 1250 919195998 919196009
    0xe0a0306150509011a09030a061107230a0303020d0204050409050c010905010c05030a051c09050105100f081b031608010f051e06040b041830080121080301060509030708010204 77
    0x20f0a00408901d000c64581c0540b1141f5010700c5126400000580207200341c241940e43c0c09140c507221020303860100c51034035071510702c8901c80b00e000b00d1590f8130400102c4d01c02d030a554182401a0b071404540d9401010b03010b10742c0401e81c060f02d08082c40c2d041c0b040c013207454140b60340241d81c0e4a404507100d41c010350742806d05000c042d11a9006100301000d00d4041c0006111840181c0d040010780007800d41172009440c62090120b8490351a01d062040d00a42e656450b07002d00f458405407001c0d50709040c1c0d00341d030b0f440c00103010181860b08400d01046a45091080d0340759001c0603d00141c4080d2a04d46407800380c241406010110f920340000140c24200c2c40c0c1c0421f80082c80051002c40136110f01003044060080000c48031303401541c41094000c084c2d480c410381140c0521424a480080d403421044d100802540c5110040d00d00c40400c0000009511460b080d042d10110426003e040c000ca2120110b004050403004091000c000000714160f50050081c1c00b098004130308990f030302a2100b13600c40c240d0140b0301c9031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 919198498 1250 919197248 919197269
    0xd02130b030c16021c1101030506060a120b060909041202071202010c0204050601110304120b0c0c150c040e01061e110c0f04110403111f050a030c0e0a030615050901 72
    0x8811000219404251641340000e05040168035000010104041c0300710003120310400001009045503098041c0543c4100100da080e42403805040010381540e0040070449800c4c0d545046030041c960310342c400d4402140c1301800d0300707503070b40751515001c091001304013107140c0580700307410000480428540101400da03506179650942540c190f400e100c042c0c1000b40c415810b00c0740c15195035008200c208054001441400b10020450790386007025102d02030b0140800e07020300c0d800c02414082800010f040341c1a08032076101e4541c141d0740c64502c403100e4040c5810050205241300000a0700907032080e2244451209148000c3d02c845162500f0703181002003641d018055000070001c21490319150000c00e04020014101242c4071050700c8480300a0751040d00100c43c190401071800c501410526145a80d130200705089900e140e802103000b42841c012000440c0405880e20750511080d482000342021120303014040202d001c3d100c7c81d0a001401100401c1c800620114100045515140705014100c0702314040c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 919199748 1250 919198498 919198507
    0x12090602130e1b0a021e06061003021312150207111305150907180b211b03180a05071a130302150f0406110d030506011d0a0b0d02130b030c 61
    0x30054140c04c0507692a0641c02a5414003451910b03c1d900780161560100c064492441d2030010001d0300b00106850b001010300c14004103809c80c1900304000d040c2c0b020079526503954446860030b041413170400c050800b2080d002080300b07410000003000100c004482155030403090740d20b980c545011a50201c2d080f81d105120381405110500303061204c039401501034640f4a0b0907480e55400240c0f070000580c00100031150000d14210b0103042c903880c1c09082c00a02e4000222400c10302d075401141149154015045007002010403902071140c40a40910502001a034105426a080550b00c621092003043c0782038408900302d1210000020440c5c411185620040e40c000d425074080c400ca0b8034aa0000200d0750104100d26860800e0740c0000e84020031140d62162404520409020b080506103510242414109002e00950b81c0e0420100103005011290b5000c800004400185140f0f0f4554819110010700040c005074071700880c0c00500f0110f11f940440030010342c2e5580ea21000748011034036240300110510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 919200998 1250 919199748 919199791
    0x1060e0f090f0c040b04080610050103060303020a03080606040e04050a150e0703140304170f012301090f06170114010f08030403080a18090911040c0e060a12090602130e 74
    0x101d005403c0303201a691a41440c0c0c030350015114030f5005400c01c0b400d42e4852401c2241c507510619400000e020203203801d000c2c0e05d19541c0d000c1c0d03852100da5802024001d0860000f0415156001520004d040c01e0cc2d042d0f047d030402d402c2540e2034110880c000d690318ac11400c550740f5105d219000d025020b00200d0b00405081d440e5403600000113141c4140f0741c4407400104000503807024540811800b44001d01c000d0704c0d1a80d1a448640d08441806c00340200540785501740301548202c0b14001030440744054004140c001d94004a040181420307003024000c0032440d11916104c400550083d4541000e040091040d03988440705246d8441451181068a51042100f44001586130015091154a5003010706c100100c4e0580d1808200300c50300072a4210b940c0700810814400407041c60000710400b6034041094141034440140b1021000514501503a400540b0480091040f10481368490302c2d0181000721208914100b0060b50141004003055000c0e0344000c110480d1a41509015271104c440340c010400004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 919202248 1250 919200998 919201021
    0xd27051911130207061b020f161403010209040515011403130f020a15020c0109060f020a02151c1d0d0c1b0b030405070e01060516060b030309061201060e0f09 69
    0x402a0807000e902130140400254443c010032030b624050008003440c4d40c3d040107000b850848803201c1100d0f41e512280301044a0501410802c054980302403416100c04140000b00e4064400d032024260450b180008200c1040d02c031030220a4200c030240c0e07a14580010f00540d055a501080d5110280f50040d202400c000855501c81c080c942880605602d400d290b50310510b558103046d94200d0030158018070102c60280d0b074810000d901901e211300b000c04c540e41060000950740d10a1510090048951245c4070070090302d00740944850180c9040781940e065010b20420003d40345c45500c00f141e04910050a10880c2c8000c14424582140e45d0703500504800345480d030440340c0388441103030180d20034005070200e101d07048480214031071405100140309552800481d0741012805a0204c02003040034415803c403451a5481c0e420140c0d00204003160101000b030020b0305503ca89224180e000000240510000480401c450304941c4245c0315400144495014040c6030391500c021294007680610024681ca143d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 919203498 1250 919202248 919202269
    0x1a0c0408060f101a0c151e07111b041a181b0d0506030f0c0f01030e01150314010507030b0d020d110306270705150d27051911 55
    0x4188a40c181d03513a60300c107108059441e20380c1c0340c2c2c0344002c0012500c4039207034104248a4080382d64800a0850f05e041903021300c00c10655481e001c1e0035440038000c07400f44d6214000155081c0607200036a0303c0b5510000320203100306010a0190300441c1000c40200f5811840452100641000307001c036506103400d0420680d085070002e08122101500301c0d403501c403001041b0702411301c0a40c2e059002500e810000105807a02001d045002981c0c1c1c080e2400c02c0030350700c41c03030019250042c0070300303010803110310380002c03a40946441c10010f1085403800000009100034801c00d00d0428030854000c100c59291840201c06403804484059001041e01682c80010300741128000411030240c182c04881c140c8080009003030010640e08216002c141c0200080c420401c1403001c9010711201004041c01d038030340008030316800304035035425990403408640000d000015810100c40c0c401181d41401c0391407034280c0014480361000c9002d403079622524440400140c0049103200c000350b08408840d0314280c01c0e50400628880 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 919204748 1250 919203498 919203511
    0x7062d0804061107030518030c10030218030d0804020922031b1b151106060909160b04030c06020c0a0e06041d01380103050601050708071a0c0408060f 66
    0x50b40e0741c408031922000740107024498401c0d91290b54409041006113004941008103902c49e4014486880255072207841e400c1141c441c0e41009a140c1202c6c8540011101140031613030f804d030043d00381178181603601c11481c1d48640d1081340d02c0c85043d1114540000c0454190034204414201c1e030000d1001709009000d0703a5440584100c07042400071580d940c40b403c03099641d60041e100c0c000b00905001d03c80d80c0e86a182001c9895180040041c580500d01c02d46ccc5410107015280030303c6400e40440e00070341c030600200c0392801007036103290142651081260b003503501900c0182c3c0c0c400d138417100205e1800d1000c66085641c4400030a2f00d50040d040035003184070468003501c40c0ea406235886c071981c01203102e10040244822a84800003804600310b400c120703c99461243e01c6058086012882d0601d440e40e84c4000d40460402c3c0fa00007195034890005071400d2103480300141c51403201142100400401d5010320070300e100c6108551a0540303030f0403015105400381d4022454140c000000140844910301031056010740d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 919205998 1250 919204748 919204751
    0x90e0307020907080121150c111009020a050d020d1e0218160f021903020a06201b1905011b0e100302130b0f0409060608010b07020919020c07062d080406 67
    0x14000c2c40f0070301200c0101c043d1307501250078500c0c2704010290920031a6010319641e0420720103040e890380020204505801000c0c03042000c0c1000200b951038140c405c075032641c1c0c0100101c804444000b45425425440c0c60304034401c07031003d40c081d501c0c21030407420b490044980c481c207081c2c0d42d08500c1050b21920b0a81081400318451403015041c000700f09921070005030b00a80241030100c40c207081c9002034507403808060902c800d1700740c00321102d40c10100c2150301c00f0b004c1b0b01c1e075501d11080c40d505980c2000e20f04a6051003040700103200d141480010f502c600002d540f140c1015000b16100d09082e06c1c4502d007054210391003e4503200c1c190403a80250020030420325540c3c110458903440c4e03030096500343c119014003100d0101c00b003020321840c1c00b6845540050015410a5081580b40400c0842c0d648200203000340140f881c1c0c0b012896944880320341c20030b61548420155160b000d0800301607030340c0150380315120015035035042c40310002c1050440c000405902d52a111208110724a0940c3c64030000742c0100e071141d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 919207248 1250 919205998 919206023
    0x1305072310140702030a061a1e0108071409030318030f121920030307080702010506030705100c021e03100e0d030917030c032d060415090e0307020907080121 69
    0x50140c1c072404180c2c802d003580711230649100b4004d004c0c0300702820b80c08016200c0403001d4140c40d81e0700424103d502c140e9615080684010f500e0003d030709400341c0c1c0e0b11590584008501004405003400c10450440e00c1913045074a06440c8010060352920041201000400c04000026240304803118001000b04c0f82c0c00c1000c011210704c0a44891880080101140c82e003000c4184001341d0351206100d60007044600c024803890504000098075001d10b48a0a80b152040e0804441c1e07403400703265031031203854000301000006d240d501080800190000781940c4240a003003a9500145000c0c8610718070740f01e0340b40040290b801410380540091444d80020f03500d2440303401e4a00c02044c003030801144100910b10101d030301d80c104100c448400c86501042c58001841c404405c46600c640b056609601800031a80850307030b04a001c611100e2403c0b560051038401e42032541800100c14008014105140b080c0c1e098201c3d6518500e084500f10300c203004001c1050341c25641c0384400e400c41d107030740032416000d01d4117001030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 919208498 1250 919207248 919207253
    0x40e032106121005060f01080405070603050403030b03100c09150912061119030c090e04230d05120c0306060711130c020606010801090e03121305072310140702030a 72
    0x401c010402c5040120b9104c104110450070006900d900c11a801c0c01c1c60b10040c102980c0701a141d0182c1d01485080541d6035001805240c4a90024090741c10050251060890002d0310280503041000074500407810b112400143c880520140f65115040c507942c00031001e0400080203900c9160f580142d0b0307015142c140e0a0818a50400200610b0b08107400b080c0c00445400342c0075041c0c450300c4010b4024040651420800e03c4541c00b0b4041d4019441a030b4104540b00e4034144542500b0310703102e028514801c00c90f5150503141c1200c01000c03031164044c540000d640e01c036407a21183d40b000b03c6030190003140c00e2018000040c41400c101628510052071842d1000f0520329402c11908410380220040e40b2040520030156004170140c0d024007a000c03414000450400e1507903560348260360300351a420b1102000184400c032544003031282c82d90300805860311240d8030342004118150401c507039800c0d5120340082034150b18019180416040d01d545803200611160801030300c044d00141d1080e80c2601a02a24100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 919209748 1250 919208498 919208503
    0x211401050c04030c0501080112021c080a05040608060a060f1b08030a020d0e0a0507060e0a05040c030c0f03060608130206090a0312031d070506090a23040e03210612 72
    0x4580320701d81e003054032107107035040c907207860a055804141807002401c01404103001d80100e007000c868040c0d601c2a00104442c0e86003e00c0541c0000c0036010b40d10105214585a604c20000c004a03901550f8800c0b0a441d640104074010b81c683c030410011400e034020520b00f0302d00a200c03c41102503500c240d02d24405582c4c403490000e07070040b112141031a600251030304c40c030510b51043c03030a11458400104810086036130b40350b40c3c1d07681e00d001c0c91042c00414045c95040c1c0e65148104000b501001d481480000b00fa00f0b0094040d050160300365004c02c40b401100c1e000e480c824810303542126070326580d002d3f280c2c85031805029802c00045040c2d070800030400c080005a1100c10126000b107105000e0030401d4500c0c01c4005049aa812103441120b98020b000240b812000240d46015500e0403900940d403202d5100019245464540c00b01c01e55070a00e41c0c1c4400d41c07000c04046401020030503603050250100f206c055a44030720495040c01c00d020348814550038200c3c41090349603804200900b40c082c2010580001d680f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 919210998 1250 919209748 919209751
    0x1a0c0601091d01050601210e01090501050618070503040602090f0303120703050c070f0210030b1c02031e1506040213030506180604080d05090312042a21140105 70
    0x8990300d50700100c051040381064841d00410b500020003150038003100081c4802c1a0440d407500d4111800100c24090895500000c03002042c840200f103030a40320301d002400303000d0442e4154890309092043c00350610500e44900e100380c0391903658a00e0742d0340c0c82d61684020740100c980c02e500601c04c094844080e8074208010102c41007107101c1c2558910b81000010192a0018000c1d42904014405c4e0300020380c1009090607895811500740b0301e12a940c0d04110020400300f00c0c645d44c0055401d0b0b0910030703e10300d261403241c0d2030b00a505580a0120362031207a01c541001d983c03000c5123540f110380e44500e5031011500154000c10010720141c6440c455480004100410350400d03246900560103206860092481200010300600054000b5140c1511038104038090100c4650b640381d1201c00040101d0030900072a5164907031194007010500b0141840f441c90b81811080012381240c07081d4060700031090b03449609c00c5800400c0901e0900c2c8135030341c80c200c00e500507504c21104400c26a100c031404240078010103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 919212248 1250 919210998 919211009
    0x30f0809190b2e0e041b0f031202060609060907020f06090c090a0b0607081c060b0c0c012a0c0f081c0309110111210307091403071a0c0601 61
    0x1602c0d00d0420a869005820803207841880d4407000044001c4011200e4100c0400c0b43d00c032481d00901d9179034905103c0c2e0035000040d404802e003c0c2441d404a682c0149458000a580c0a626080c2e0030310344028040ea80e5900a582c42790b407140c4280001045442d00c1400c00340e0148851050b5513a81c0c151303c024038130b40b080a442134425a0094080344049007450303980c26034044182082845100304240c01b15036244161000500074110024244c6080c011005450014160200d001c108860380e9161000e407a0300480740c0720400d400741d100c02a1003076100301c0a40c0c4100389164201d65240e40d5401002c0c02808030144120365910501c03600180b1040f29054040c0200340d440f024000c51807034090034030500000f001d807200926103060101d401007003800c0101502c5140031300b40000401c00e80308075181380880810440d44d420722051000443c030080e11000e54040c3d2001c2e26120806921582000b49900d850060140c1507480800c081140c503030503108400340c00d5018514a0301d4003820a690358100403098000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 919213498 1250 919212248 919212263
    0x13030c120e180606030a150308070c061b02030706030c0e0301020d150602120316121a010908070311062104080403021003051303030b06040503100e010f0207030f080919 74
    0x10540c080c107100380000140c181c074101400c030324600352000131014080035166401c820f588500c144115100541c00e4800381da000400e0135161070040c0340240d290202030140c000068202e262060416058452541c0b004c0d07401400380105c14241a0200e000740302d0781030728408104401d80840035a490030f1000305059111803501056a05814040904804260b8032031421940001c05403d0745601c40001d40317420052061000070325520b20002102c0030a210100c403041c1c907283c0340d02055141562210004581422b0302c404180076a501c001e01c2e01e0f050b2910004d48400205000c55006292060081c61501c1c0b000c165044404d405000d4076000d42c400f26411543c9101c00a4248290300d0459442c4080341e0700e40c90240428a84040144024503c0002c005c091545034400c01c41150740344400d84000d403001504807010703001516103690180050180c500e4403075192611080880d05903000b00c0d0b01c084e415460320300d40c4080000701140e5843c0010001070603409030502c0740445142c03119445030303554041c40d90b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 919214748 1250 919213498 919213517
    0x6032f0f0f060d050906090309010206040303050705040b0d14010602010c120b0a0b040806190204050a05210f0d0909060f0e0907050307032001020604020913080f0301120c0e0f13030c12 81
    0x45c01464504054400442d603070091196003c1680d0000301300b544254180380c00b0400b5110300c501910980940d4010718000d00003c03c4040b4814030310340c040c0e8011031000742c1410791070b41e80d214140d003282d400143d00c90020f108644030901d01c1311075030448680420041c05a0640a554103060340305604130707401c2060290003810038803241c14000300f20001848819082145014548000616110300510449008644416154007500c14000c031101c5005030070000c0e6110300000d501d1581e1201035880000000c41c60f03202c400f0403600807501c07449007581d42032460840000e0030403084205044009041e0703070301849030036800308041d10103101260080d81700e507400300c001021040201002c189a00c103507a04542c80001000090b030350302c10f8181d030040307000c0f00c106901c803541d410100d603140310781c000d95451507900100004050964070451287c00d07024003010f0074420f40740c050a9900000a4840e000c12030303d075101240101501c0444040413900c40d0401d0300ca080129641d0008131036500c41c014000c10032692 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 919215998 1250 919214748 919214761
    0x10516120c050f0c0c011d0904030e1206040c05030d0309080405040e0708010219170402090105040c030e1203070201150e07120e150103050708070b07060c021e0106032f0f0f060d05 79
    0x2052032047c4203101022003c992007002c0351480713070002c202404201c1c66010300d004a0b256011480041010f100560f2110300d81b6082180720725003c0d1081c10b0091040790720904130390344070348544c03c40c03250700240309440e103031405e002c11014018241c0482c0c5136001d2030100103070242003403004002c0d2400c1800139071409201000c010f094500182c07901815800000100001a91001006810340394115000600c110307840004400810184070b05807103c2c0716100b0040d20007000d41001c0c6102e403107a50700a120001000c01050403100b0a40b246030350448030840414542800744a091450f5010b060000848010640d5418a0700e404404080d034660284001481440024041c60000d0b184000082452618001600100717200304640680719651310300c80000c480d4800e0040200414142c8007a402201b8442204e9000341401e11007210303010300040111408041c4c18001100714902c07100040c2408001009001c820b048000d440d9074460035940c84605d003a5500c20142c15494001000060380b0700c0e044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 919217248 1250 919215998 919216007
    0xb0109090e0309090a02041502060f160f08062205040c05032e060302121f1517070b1b010b06090607080a11060c0c010516120c050f0c0c01 61
    0xa41100040c5030400205000e0000700108a0b49000019201d0700810760791300c2d10160081c011508008540c020003203000400e00c0d070028082e80980108450030000351140c019418088400b501c0410204070322246490046000b11400d43e4807501c050141084c206e16005964103114901d41c000c06056a0380042c0300030300008031020000f0b0078058005051120008455422207140e503010650011110340b02c050601102d81c0182000755405001e078101980241c1a054442c080c800c0035418411107a0032051050300140103003916643d048007030022541c200000c551140358640f00b0111180714560f80007581801050044c81c81070001140c5594070b500d0080480e0940360601c7c11f440c030030700040c80342404503910481161981940301d840a56105048003050725200b0301e94080c0b0b202d9000e00e504002020b6881c00c0241348440c1d41704020131995039400d40c0c1d201d0010030700d038001c00001d10340400b0340a07075041a4041c40c48190305003000c904201e09103c5207040381d07000d848800c4103500f08422002d600d5812 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 919218498 1250 919217248 919217267
    0xc0d06031406070f050d0207080d020f0a081e01090209030a170913150506070201141210170a061a0a170616021c030b060d0c0905180420060c010b01 65
    0x1a031400f41204c0c119818020898041c0707031503040119a000600404010200040310240034088000750348800f42d402c00c0c1409500f1807003032341d804503021000054141c018a190030034004201c0d2010403142c0d0a10440000a400910b1354a03050700c1901111804105025101071100c5188c003481699526030405100300710901403003064490f4101000f080207200b21002c200183ea030b09a505a46940450004943c1180c2480424200031400070b00000012616801940720f45181c1d03c000c01447d0ba40c0301620b02000d55031704060b000d900410345200005402d5080910310300c01d002c080341b21641e46840000c4600441d5881310b039500c6060b100008980d0320070302849500150301030510001c4000242c001c0c3d218051450f0000042e43c542a0054445009038031501c1e4160002d41050385609403000305500500c0c8049140c0046010900001400d18080314032801c1c1c2c882c0c41d01c0c0c07480c06480311f94480703610701001c56580105a1843c00b81c02c0b543e8032210082c003c03013110480003183c84074400001400c08000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 919219748 1250 919218498 919218511
    0x109020316060804120201140106120c0e010507060b040e030d020c070609030c15090e01090b040e07120f02130509160b0909180f0714010e1c0b0c0d06031406 69
    0x200030803142d034000002560090300441c290305070b101c030910124014402000420388050001c400441c43c01d0f03010070f80c01010803410f00200001c04c0c81c500180d5400c0800403034140043c01c104440340016019400c1b5801801e8041c00c0410b442e050540003904680200c100484076560100b81074552200801a40004042c00c0c00c00c6480a801c5450381000c0c4002809401c002c0080c2e00a12407449200d07004002c02480c02c0243c49145585428101d4060aa244080c82c85941403000d44440c0721008907401007183c00e099070282c1c41c500c155032049500120010142d90120082460313400c094128005c0c02d00c1800420050045030207104059070481b039080c0c100411040051103040c0c07640c4c5802c6205034001c11010016000c43c0303c410461407a160711b004828805005e0032030000342c03403c100000c54140380c0c4240c0300c0100e19102103082c843c100800b0143d24183c40703c603005031800b24480c6080150071480c514400d92070202001c00007c107032a0a0360044400c0c4400b104610304050b002d2080703941080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 919220998 1250 919219748 919219783
    0xd0f020105010b1b100c2604051225080d0c18120804030501090803040507120812180708010f1103040210050703020a06020f120c090102060703110c0a06020c0f0304080a0f020f1201090203 82
    0x4040d20b8452b40e1302d170801120304280300c0004d0288414107a40d0380100e119180c8920040702d041c41c07441c0142540c3c009080192040c0d04040303178040040d009074000035400b107030030460b20105440e00601c180d4034502d140e4195003801c01088080040f440a020390f00744079014004503a901c2c1024607050b86002141c1d804100c0c0243d00c5204a00020842422105040b400103103440311611419042078014017142c0d0054040d1041c15000190107606400503072151210020401003440c05a0000a2030b2008850003948002800004010b29000d813010380390b264046e20444481c1007a50f0307241001ca03484650f4116000300c001c191440b40209211401c0d038011000700160b81000b44a80010f0b58414019044c20181078484179180544204041500c00f039400d4101103840d41c0c002420043d000390b000c0001c040a0307000f050800c200c0ea040000888040714000001004107007056101d440111028140407a40001440c0400c112a03071015550741444003050b0000424245510401d40f0f0800c1c01150103002c078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 919222248 1250 919220998 919221001
    0x309060f0206010e270a03080604200d14071d010302041d18012a0c0201081b2b24091a030a03020d0f020105010b1b100c26 54
    0x169011682e1411104144228420b68440800c0f114440170841070031680c0d14071040b80039604000c0051030081c094081d44846030380d504c801050006440da842800c400c00d40c480c00341040f96502040081c41c007403102010001e001e44510307400410150b800d58004000400c401618100b070f00100100d00902003090070218030301481d10140b2444122108200d040d5174a5140020346a0031402024611b402c00c00b0f0020004a00480214550740c84042045038801890703118800c02c050144060f241d850790141c460700c02554800c031149400f5004030010303c81c00081400314070110035108810482d96496101892021031303480c2c0103c01154580b03202010300040f8070020b07444e18854584040c080c3d03011040e000c10100d140c0500c04070400b24007141140c2510441c410f8074245540881c0c40c0450b40c1040c1d07500d0b0301d24004100100e003603c0c400c2c06070315020581001401000380e6150705400d0501c1044060f01c111260244800c4c00710340c01c441c0c1c1d442c041112244000070040b41908600009852030400300755070b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 919223498 1250 919222248 919222277
    0x10e1f052211031f0605030c0d140705030d090602060a0902011d01020307080d02120c09060904091e0605090f031201050402071b06020c01140a1706040906021204030906 74
    0x18620070303070024900e202a8003400d000b07204001c4006410040090119820b03101c41442e8245600420628501c00919103040071509180220f0b40c0881800002d203c00403a8089464040101010103036034860380c400c4040000305c90b00c0c14480c40f02c0c4200f135a25001c0e80c042c64064080d040990040501d45618600208440183e800c00010710705402c01d224140941400c16005134994803d81201424642e0003140c110700b46510f940042035001e464400b0088280c4954600c5066401591159580700006105000c49420642d02c5615264010200940744000703034851b12080c403030701560660340ca0b40c4907010010000b00c200544443d040a0a0007946450010030303102d501c110040c0a014495900081e10300140140300450440250540301f01042031a40c40d038000c0d649484519070140460706600e48bc803110801c500c1901e5514600d0748503d120104054900e8201c150010001a40547d681a50801243c0903101400040d0140c1840c47d400e42410308020b0800c81083e8009410031021143e80c548 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 919224748 1250 919223498 919223521
    0xa030615090611010608070909060b0312040504020d0612030c0246051008090105010b07110f1203070b01051824030106031203020717040b070f06020c010e1f05 70
    0x1102c0c8649400031100c00400001405443d140e4080c200300d201d404404200d10020368070100d070851140c1c10800020707138003030181900d07680351250100761048203000c100540d041503001042c05000070000003a030035031a1181d03100d0701c1c00c400030250000368244040b0811410101042400d20410502810304180318041400b180000368900140c3c400807052040f041c3c40717080d00301070050303e401080c071801c805a010000340041c40844032000c0c05e60030500000b038403159040c00c640b215034120404003900c80c896000d012a040d0b496800d02e40202d6100c0c403100f0400f906201800d4242d02c82c0400d130904d94580320801c210400c0480d0350004051343c00d41031202907808031400824840c0b14500c019040e03959540000e0040c4040c0e4409004010420f0343c0305040d55050740140350a80c410124407401c0744007228040b16501641c0108507200d80204484004102c100c0554000d00d481000e001d49840d80604945080d5031400d07010028503031107800c0001c00010030490090380118070b40b00030007052800784042403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 919225998 1250 919224748 919224767
    0x30b0f0108060c070f0f050d0c1e0f0b04051f02120a151a09041401090f0902010207350f0d02010b030601060e0414012c13021504030c0b0a030615 64
    0x107050181e0031045d40c04214441c86000402038100099650800e40300c40040d002c4a500c0e20100c52440c04458124031000d640c1000341440c640080c0030090402c086d82d21a40c025001a105562521500c80c1ca19903502c2c0b001101559141420340150300d50a005040300c01a03a800b074510030340c0c40d04040d00d00310303c2922010181c007100d201b01064140003c3c0100310407203500c580381c40281c01ca400c00d8104c040030b41e40c00003420704a84e50790b01c0c10050740c0882d142d4001204c81080307000740141c00c001010009502d61088201900800303000d40d1380c4200340104078654080710404a001c50b074020000c42e1510607828030042842c00700900007404103142d09000aa100c0308140174410902c0101543c00c0ca840c1c83c2c5a01580c0019a403038804240b0b0f503121040c20751203e070103081e5141c600c55a041c0082c10103a2a003443c2c0c0c0103003a9102d40f020341c1e15295080201200241c2040420360105010000c0860256810310b0001d100d04a002640c9602c0c9050007400d550141c0c1260381c0c000c83c4039028241440c0d0002816 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 919227248 1250 919225998 919226003
    0x509040b1303050f0a0518030a02030604030f110a0c1d01120303020a140a0903020f01030c09150512070c06050c07031b1e051c0e01091518030b0f0108060c07 69
    0x6203032200700c2e240540d60390194045460310000042503011205400400811048060141d45418492001c0400d0b079520748620000750180c002c5c40c04140024041c0c01100480411030514a055034400c8415a18241761000250748542512100f04256144482d101c40c1d01500c90441003075a6060210200d1b0447c140300c4001c00309540010040c100340d03c130780c05c2c103070b40781c14441c85080c4c0d503000180004140f4141c50009912458410401e554558028031903990401400c0e21061320040c0f40c007905440e0b4034107041d291414003100b040090854007110f40760903c143d16603240c4406012960404104a440c0200712030112142000401e000c244c018480f58601303030403c0e505a214006500e408004100500458848420078000c00004c000000c18440d610a42020303011280c1c0c0e065480440e103040c0400641030201b498440c061105600b01000704a89a0140c1486491901c0703182042c00b8401c220340c825902e44075448140040c0e1201c10300903600404800000340914102460000c100c2e100e00d1100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 919228498 1250 919227248 919227271
    0xd030203070c0b13061809020409050a050f4305120c07020f060304020a0302030f0c0f1f0c050111030c03060315190914070e060a0602070b0403120e040c0f090509040b 73
    0x80c55500d00701c14034024040d020b40c1f60f05640320760362001104007800c81994544005424400000d110320f500030302040c410144003c005074050340c110202c0c1c01c8071188070b280c0c462500d401454220146403802041c4c040840a644441d0b48030341c0c4804608240c0c101410b12440c59500300071190250382d9502041030442e27003c480d4260360740c580b840002c101c100d0b2a0702c004d4040c0901e0a6145440c000030138400d440140c1a2841d03581c00c0041c004002d0481420300903003840c003038000e80400055204d2007000c3c03406845040001030000c4507600f0105150001c82d0101d40300c460000030080a070130148800d0088040303280843c059030030070885840f60300d094064180d140076a82d12080c014414240da0208084110388250380c40e00c0e842c1d10190490404c00c4507010701814002c0310018645200195150468090104850625044d59900485186c0c8031a0401c10000c1d05c0f07045c01c2560369548950682100c450f1201d2840c0900d002c2e015000070066480030b8440c6040204210129100f02d1011b90300021140e034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 919229748 1250 919228498 919228517
    0x11011106100e0903160606180902101b1b050f0105071511120f0105270a020d02070b0702060117010e060412170103030e03060109061d150d030203070c0b1306 69
    0x341c03d0300d14090700103038560031040e144462050220b29404401a6000340c0e00c3c0101d001100c1102409031048a0300080d08560401c0c184011103100d4200b080301c413841c0001c5807411088a444603041200c5140c0c2040c1d0400354140100150700e06a4098044800e003070030414180805174440c10805801100001b9440e500c454200e41907403924000c4407101c1d07121819150142c1413400700441002824000c00c0d0081c8100480f001c1b6107045050881c06020300d000c08000c095031071100b00c2c000b030341000090144058007403050a000a51440c086445285598014030843d8504a881a94400d075000700040c00e9140000801d020140882c80783d03403294000d01d0401e140084403030101c58049686429407035408080001104055109400d411554001c40442ea03140c3d0300c8000301da08494803440740b442c40a0b544452a40c01c603580403501544500c1581c0c1181c0c5407140310000c07071906000602d044006070000107001c0e08100c1200c42c031b400580181750461f428102100080302e102e0050303000360000e000303081c0c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 919230998 1250 919229748 919229761
    0x60a09110d150503011d010e0102040305190c1205010c02120c0a0b13080316020d03020a361719030806130213060c060c03050c04141c11011106100e 65
    0x1082c41c0051030082c1c0200081c28004e0350b440441c2a05c41c48828455081281c403072000c41c0140243c07025240c10002a01501d0000201c581c41030b01035070000c4503c1d03a1049000140301d00080c08919030359018400108100310305503c001d04001212081c0320401809010340b607079079400000d0300311075140c1c803082d25409900d074140c0c050040e803030800e0020324844000040120100803800e896480c0c1c402d6800f1a083c8408413030f010740031303802040812400224601c0814620302d1a50710164000390220014201d40e40b800642c01030902c040340c1000860f2440051420074030f05040200b86800520240c160540400c5507034010a0110040d1820b0b1044030300380d20064004500754129407ca40003000d1590440d17540c0c140c0a420f0300a0740801766009840c0242010299000b805058422a0747c414018038007810040c03003034074003ca0621700b43e0304280d420510781c8102e0510401c01940e61b0046621000d03030308002c00014070036200c4496030040c5401c0402400300e81c200c0701c00e00500b680c4e01c0300034114995a075003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 919232248 1250 919230998 919231031
    0xe010c1d0a0e1303020c033301060f200f061e010e040b181f0606050903070308130306110409060501020f0309040207060e150a0f060842060a09110d 65
    0x3041c0d551f03458010406100414064001d00c0d02a40780030307614580d4620210600c600074500244104000700c1c14a1442c5815244034020700408200d6002d1800758000304080264600420300c0e14003142e03940b20030b041c07000101c1c2d0344247d480c461046024242d959810b11034000700751500074000030858044880860800c1c1c0707030030011504c070724400c3c0304132609400e9107444001c09407052070144940f07a180a102080441c8990304480d203020b00035000f084154516a0382d04401c0d0b02c110200c040d2180c0500001c00007550303034050080324225036504251198100301502c0d007140d0a5074091411b55204092120700740d14080b0640c2c50244c0708440040c0c03076850303900746180a020070720b03074600d03440c0180402d0100d82c9000145117409010909402c100340c0c0060020102142d80c00e00600e1480c1d4084200300c017500c4921b0380300b000d0440c06d03000e0441d020790740b184805031095031071888070b100b248400341000218104013400000070000c0d0b450074466558030345810542e030300c45c0e01c407528050b94075410f6640141009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 919233498 1250 919232248 919232263
    0x14012d060f09051b03070206011d070206071101020c030a08060307080715050c07090c12060e011208030916030317060109120b0a110c010e0105060604050a0b0d0e010c1d0a0e130302 79
    0x1000340c440c0e892502802c001d48130107090156458080036090742b400c41500106020384135895580041190341c0b81d00c00d007510114562f442e0021a50340810280f00000d00a00c080c0100c07020903241c0c162182001c408060034045140c001015640c0030b05010448071385104100e200d008144d042c010b40d204020026181044101c0d00710252032400c0c0440605225403080f0700c0c0f000c6a000c07104c2003209039180d000262141000b8801c002000b01d40c0d08248020038201402103401006402c101c801c40d01100a50f00010012a4815000b24040e81004010300000d0b40c9095031040c02480c04088e11810f00e001000c17060b40c0c0010141084440000107500c40102d036019800c00202c01e217501c3e84403110a10058042c1c450007420200319403d040100e412420f000c000c1c1e900780c4400a04801c1c261b81000e10942990300319074040c10150381c944c0304460000200b80320349000c01d43c080c1c0c0e441c22010144000c00101c0306441010500900e020361080003100360300042d1030b412102000c155401781c0002e040803481c2081c1e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 919234748 1250 919233498 919233541
    0x11202040b0304080405180420130e06190c02030307120207020409060203162c0a210606053304030812100806040c1214012d060f0905 59
    0x1001043c0000d119040001e80111541220f41580b0104020349114042e501690005e140501e50340d052211605a6080070380003040c05401080420103844151040c2c0380300c04022a803c1c3c012000384502182546807040480e04079000c14404200031071030080d5a480014668410007103107080811890009030115040c00d0b8000300140101505810050300035881074540c0076140a40c0c504040000c1d000b84100e010000c080248403160b800d405410007003070b20300007040d0707640302d85200b40100b00107200c481110141d5480788803800c0701070420b2401c0d104483d142d4002910070110450040210030442180f580101c1d10440380000c5c6d69052501d02e000783c043c075040180888004201c3c0d03006450703082c10151082d46d0420446192680d1000300c2e98903190140d40240003015002e0052100c28030038141404583e00c02d800d00700d22606504400d908407100701d010007084243e0b4402081c0640b40d21000c2a000384074521007000820314058900c510342000c0c0c85460150380d00d8000041c0d400d445c4d102402c1072804c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 919235998 1250 919234748 919234769
    0x41409180d210b1804051f0203090105070305061c0302190302030d060902040e040b0402220b0301060501090501021f0902030703120909090c061d04021b0c03031801120204 75
    0x110050101d000440e04100d01050b02421514404aa4000c0104048001d00340c1e04075400804842c0741030a00041040c1c500d84a41204444a000820002c0301d5000d0780c0d290068032803c1c081007441c25204003130420b80030075082c13000307105d4075644800901084136144030454914086034601a4100000c0414641c5480724a10150b010300d40c0100041c000d01d4010300081100d145c40301c5e4407004a004074010101012185400600094040280103400c280010154405031000c950360740d81e003008400000894540343c6003000c015042c2401141c01038642401c2c0b0a20140c10800001d656210480403040d85c0940080b041c0c02e9004942e00070300c1000c0d0082c041e1862603407203080142038640d10040c0b41c00042c3c1c003014001050030f514813899403400c2d03015480100c0300c2d203059421250701c1500c0d0302c0c0d100d030104180c104151503038652000385010410107104d081200c000c2803c450801c00f160400da40039420402810224180c0f40742405841c0e002400c02248117068411048000d000d9030b0041b00c0b038003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 919237248 1250 919235998 919236013
    0x50c1909031b05011119022e0e041a1f030b0901062d1b03050d0905060115020a12030e0a060c030506100c0c052b0f03080c04140918 58
    0x9402c10001003040e140c0a88849044464120580d55114155103481c0c0384020354410000c0140f91180241c040c003090707003c01600c41d581c040c1c492a068556084980086404840c92400c01e0405004000d001d000c0c202102621145a10200c1c2a4014941c1784c0040020184200340300c6a02a030b00200580101400102d2a036071280e82c06031503414040c4010040d802e015032901c42c0c50003404c60703101481700789645003100340c03000a401081049082c0e8085040c000c091117030030b0102016100c1d079007413503000c0d20003030500d54581041c62100029400301441150403a5000101144030f8002c501c86100e983d01d00001c0e500d003441d001300c1c10180f0301c00c0700404050a1001c0d03507184030b9046c0c110300d005110885040f842000140000e8440f1280000010402d8041c04400c2160b46408002c1d4211206a0702c0c010101440c40404040e8019000e541165403200f248034003c140740d4042d01c601d5002110540c024607150a08141c1d50580b101d021140c0c1c03055208000055101c0c041d8502000079044400498220703 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 919238498 1250 919237248 919237283
    0x30609021305091801051828031d0d0501060311010c020f1003020717120105181902040b0f0301080c060403150f1803030e0d02031306030f0b06040303020a03080901050c190903 77
    0x4210a140b5554114480c031541d4102d249124914800c070070b07600c0102042408c55598007a07480000d49400602d40e00c040028200007511a403106980192003100006909800c5103800d1816000c40719845040100b0020350000684030321109010400d01111103519003a15040210302a02c00d01400801c0c440d822007980d100c01c0c0000d0050722032195604079072292a0b0300c1e2000e115014007021100324060704030070003090044001081c005008420b41102500d050f03220300d031a4003150f10101000071481d0340003004004006050240c00d403400c0c0304494142c0b4051844e1a200711104202c00721030400e9030f4808042a600140d43e02c240303a011400d15014100050b10300f4064020810049491b009000f09900c84032074034404021182c480da051481350507120700f0040100c0c000c06480c142412003640c0c40341768010303a41e2908060300c000e500c039600030b00050340a460300528000c0c0c09044a00260b05000c284460540c807182030381d03511b0104400310494809920300443c1c80b4011584003400c0752440d060020003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 919239748 1250 919238498 919238521
    0x712080706061406070803090111030c040303020f0c0312031003020d06050603150708160e0301020d32070518090f06030c0d170901200d03060902130509180105 70
    0x1a01448003045259030755240303810f0007002c885180e640508104844d2000400b4030014580101d056400052000c1c21207401c2803960380140e4030084d5041c00410200200343d41080104920344481018081d5403000c1030100c3c2c2d985002010200e00082c01100107620a048140f04100440d00100040e0300030000b8106140104000d0369034601902039044040c0001105140250107040653340301030f11070350f4241000e00120080d5401c0010000420240c00e0190340900251100045d40d000c0014040c103040d10444803407800343c0d00c6001440211441c41003988564513000d511815a0a003166100306e0704114940da080c52045040d40700d2140c0080c4a0340384498000d0f280300c0c0109a040368100440a420403400c81c941c000001c00721410b415003110300c0340c01c030000b074102c00b10181850102444220305e440e05600260f101f40805900c26050041d6056240c020b4800174000104c1c00c51070820b1072078601e548002d031801400c2c080d07080c04011035040b100300a640030400304c89600030416810100d50880 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 919240998 1250 919239748 919239757
    0x1b06070309021e0112020307170c0c070509070c1101051917010f18020a050714010903020c0a03080a0c020a05060c1006080f0712050304030c080a1208011206090203071208 75
    0xc0c00741ca03040c031141c1507020303c00c008400e146005845200d07404d80042c0c0008085c1d40000d02100c10000226481000c009040320101d0050080c41d9016843d030000003051480c0c440c0c90340c04144241c03410410f0006a03034008028680c03840d002407036604030340300da100141d4081c407a4252000764016201c12050300382c0d40c058008010351107150701c0b0503400e0760782d020f440a03007a4403802030030b040e4420b40483c3e100f903602aa00070480b05c042803c1c142d003010703190b07103807040032030420401081d00707035143c04800003010b43c1030022481094044400054030350468942c030000d8003810f40c0e10f1092141d40c0b08442c0070355036003510030340c0186402480c2555a02d4120981c6803030f001c5d480017290540f414051b0102d402d00001c038051805a040b14002c14886151405140e0990060030b0240c1d5903020401010001c549020003907400b900d0450020140b000051409240d5154610390100810450318010f1080003981c03004921031350b400c00310200c0c44400a00019050842e0355000080c00080300545204105c01c41c000350 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 919242248 1250 919240998 919241003
    0xa2c06070f030e070509100e04050307050c03011802011809020d150f0303051617040609060e040b0f0114120a1d030309030d020309030c0604061b0e060a03021b06070309 74
    0xa64000c510401c0c00e60640d0b00350080182c0c641c205920074440c904003025115070020180c1200c0e10708075946c80305061681e000f503030199050b400001c0c01c0750a1020801c5041825102a0b0003042454032f84a4082d600903401d100090401040c03140745540c01100c01c0080d006008012030855480c1c03c170410303500080c2500c08451038844203031000091904040c001c0c2c54110b94140c0c840900d080e040c55406540c1100e200340c111641e650303d6942120f0101c01c030001d04080c1c00b00e625441e07800c0e030500101030003c0d100540c40790f100e00c0c10200b001078103440380468900f0081e408e00b010007158034030420b064810301460359076890489001d003c0100c900c105030081d01180544945803041410f0042015071244000c0702d0751041f983c810402800803d00950042d58032403001c0d41a00d05080a00c885241880019501501d40755224945c0e4140340c50b20340c1c0402512801c9060400c00039070401c020820a010313070606541819804601c1813456009100b0941e040140d40c0141d412034548071001400500f50402c05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 919243498 1250 919242248 919242257
    0x507090812030105033408010b01080a09050c04051e10031b030506010e13050a3009030f08040510021507080609150a08120909070801030206030a2c0607 67
    0x640e02409400700890b8180c1d040a0041c000004241003680401d015910810021549074102c13040c00c1d0440e22110000344c8410070000c60310061060004000a0029211050b828500002034000500c0062642c0640350f054901007906d6a0743c100e004403e07d440c0d08041c0d25040c103441040150020150020305881c400c09404420011105c501c0f40c0f50529404001e0140c4d10850043c00748040e501a401d901c80150707401900300151940c0c98605001ea20310381101d5111060701071780e01c8001560b0135059218881d1200c0959060320301801010003d41e03201c00707002030f10100226414001e8100c01c94001d000007400004041c20b640100030365448140c5030300000510401d0100307490b1031260084034002c0c40b000b010984580c560320807014012400600440d48400c007282c000031201c40502510340d0314498040031607200d43e651400d100304824020901c20820070000d00500041c0c0d1014241e90b0458040c100c0040c4840260b92404c3c24640000300d00e1f50140c0e00b002c440c21441000248642c8100e5a0750359 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 919244604 1106 919243498 919243513
    0x10513170f0c01150b0c12030606090a0e040302100501030f082811010605091b0304080c030714010b0a0f231309031b1703180105070908 60
    0x20b40c50140e51908085421600c2000140004100803202030740780c40c07031030b44403551204000d401801c1e1608021010440707a88030341080d04c0c006980a4244500e007503e0361b64641c3d008800b01d5080f001441a40000504800c25019039412a5071145c0402c041200c1641c0c0d10907190009540007904c40e60340c0e040755288403805d40701c02c0700d40d0040c0d07200c045d152540b04484d5400e40c0d440307821040c007416501d0103100c0840d0500e00104010095400c54640b40e882c2c9181c501e400344144a4502038600c00402c0301d0051000609034500f4510714130700200000321161007841380c1f680b481d11507890341e044c05000400c591036101c0410030030f400308800100c008881040000b09030081c07004c204410300d55654940130401d81c2100d4000300303090301c4007504803000c0400e41c1c41400745000440864410200400420042640c0588003050250910700030701180c0b800301c4005000425a20410a140c0710380f40303 = true := by decide +kernel

theorem cover : BRFrame.Cov 919064748 919244604 := by
  have h0 := BRFrame.cov_init 919064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 919064748 ≤ n) (h2 : n < 919244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
