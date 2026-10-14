-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1936
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:13:03.952052+00:00
-- url     : https://prove2.me/submissions/27d638b4-d127-4b88-8e41-95b009b6b1ea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 348021582 ≤ n < 348201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 348022832 1250 348021582 348021599
    0x60e060a0501111c0914100c08160209010e0a0e060c0a030c0203090d061506170105010305060f1201020408190b0f041b12060507020d0206060609010909061202240301 73
    0xa00b8100041042d20b100c0e8003e14844e980c401950042c00b400601428810400c1030807005501d40e410b641221a006081c8418030000d00e184403001c809801550f002560f008400819241040c03c40d81c05030802803290b07511130b40c01c01002ca00b01c0d418400381341044094504100c010400d03c0c07017542e40c1c413009403c003580f20408600410100c2030280940c44100aa0071640e40c0f100400c500d503a00c10b000104000c11020300270302040e03590b03502c00c00610004003035403001007042c0a20b981c1034174000c6c81c00141c150f0f030340e80020712040118007040d0703082403118150200c0a0b0064000b4400d03a24448200c540d44c00d1988104402c036854540043c01c1c1004040c04a8a00364a015400b03800034011102540c5400e034242c00a10164250f910001c1070031030040b4010200070300e41c0141680301038640060b07e00c620f91804d01a44518000300302c1031080c078001902039290303030042502d10090840c000d03040025584070400300c20308040064081c1e20408412900c00c1200304120048410640155403072401c6074600702a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 348024082 1250 348022832 348022847
    0x402090a0b01120c2c01030b010203160f022107080d0e0a140102010b100c02010f11030d1d010e0a0506280203040303180302060f0a0b01021902060c0a0c09060e060a0501 74
    0x88010089002d05840e4245e0040c500d080240f1150405c030b00d400040340300050200c43e024101c06d0705640007407081ea41000d16110400801503080001300140a401e4800500720014860102400300107000d69040325850015042040d186682c04442c680e50318030000f070b10b00e64000341c2041c0e80010210000d0100c041800040d640b1128180004603403e8080d40c002103051021940e9a0300143d070718059038040d0b41e40b001c1a8070200810341401c60b40c0010029040381c5030710419619150203a02c43c0307140350b85058400c5202c00c2d804042c2000b0880803111404090329058600410340f41841007034003044000c0d4504403000030a0000709280c0c0c44c1c0051400303000007e504020015403e069980c1c0c12161021484110740020b2407113540642000c3c0b034054800302400720050300e12102c561504d030396003485980006d1030b8082158044042c035146c1c2d1913440003c5541c0f140c1d103500700302070042e60102c904018040b4500010788000709024030000340c58a0410454000840b849984409801020000341d40504d20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 348025332 1250 348024082 348024101
    0x3021e0f0f132d06090f03020108041703090102120105121c05041203080a0f090507290f070b090c010e0904030314010f140103020c0c01050c0f0a03080402090a0b0112 73
    0x700c0d08a0550f41c0403090034015100140e200a040004445010b0306802107221001e0499410003042860604842e002c9414260000a041c016032a02040c2400540560b81500034900b02c016952460302d441c14501075045602640b844818050002c00d0030701c3c4c004102e2036441c05400042c0710a4034014150f617102203002a02c3d03424400104000f240390b00b601051114000d001e074a4070603071414500883c2045603001880d541c0020b01d01320020000580115180301107511004141c1504002d044e00d541d40c04107410030000300400002807005051540201404a460081c030b415401e0350399000c80240c8928a4030f45d0306002880d1407103000d09510b4070803000d642050088c5400101c0139100f00c20402c00b00000e801850b4002000e01040116030100f403528416490207180540c01c1c95030564080d41d41d50401250503040c803d010940d0350120400b04050240b02c2c40d40ca08075008141d00e800c01602e00c90041c0e905a000d60884c0d0000303503100c90395001d007003c0c80e0810394a00c0104564150004001c5c5070545 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 348026582 1250 348025332 348025357
    0xd1b060504021c0305040302120c1005090f06040305010507030c08091207030c06050a060305070f0e220c1d011203020d0807181404051510030e0a1203021e0f0f 70
    0x10070f4070340c02042c41242110161003a00c0300ba40c2c941c114010451211002540c004407135201031007800242d1202106401021a1418203e80f0707244c1000016035203010401541e9040700e008a000424000f054001500400032614100000110303150100c40c13006040756001150b6002103915056105140001e0011600929015170390000903907450b0180e0760162014010a52510303801d000f8464184506401486e4600e041d46040340b409003200c2140d07800a004000b046050000d92201c10354194861240a0788020031000791074607030340c0340821504840850304000019100201d06c1401940b0f4162516405800820002e01c9000c070031207150318010701800820005a0045044030140501007000e01802c004c80c02c0307a080000240011034100604103043d21609250355041c0340c82d840c1580d01b6114143c90085400006514560b181c14a0b0120040009600000b00185240e2590250084081112014074110b00b00b034881100360240c090002c588900c01c10403821703603c1949006201111512 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 348027832 1250 348026582 348026599
    0x3080f0d0f1e050c0a0e010c0c0305010603050318031504121202160624060c060e03030705040501020f12040b2208010b011106071b0812010303110d1b06050402 70
    0x10001c900a81c0c9242080b8030620022906415a691041c040d103503121503011102401e202c54840002c12141d102e40aa5062055800800c400d100d60800f603c800345401100901c001642c0e4a01603075690320040302c0024400302e14000da500c40c0b40100300310204801000e81e8105a0722107481c1d4030030203011050300e0f100f4084c280f04481d41c0c28020740050406030103844a13800000000781801c03001e482e4040d80d220420b04800000c440d02d00100c1c4c10075030076159546403070301e1800510b02d400d800404601070078515a03c0f003c810080d40542c48070007081075400a90035294166082c0840b00d55484e04c1c13601d19113261400f03100500c00318040d032011701a00552801c185080300c180d20b007a2084203d0581052105945500444806581001001400303010700b0005103801d14228500404a12030545441c90610700d4090510500c890030040c3e407911100c0b52003411055940f4a0083e1646207800d140740700034001e034031802c0c2c0750703601070000904c2d50841c1c0c0c1d503000c418200a586000080000400c101e0703000c5a607 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 348029082 1250 348027832 348027851
    0xe0c070213051006030e0a1211030d05071b12030f060329060d050c010309020a030b07020c01020d051219110301090905070902090105181512011802030103080f0d 71
    0x14031100c1c0c080071003018800295410700d00224034000c485600484c041c103080c803031450700500740010024103040d003140c194910000c1156040301e5080c8980c111441500c0007281706500e107405944480e02800d0b0549814002d640c41014004401903a100c024101c40074021419925a001e900b140c0841c001858000441d40d880380e07a0000c1c1d42801000c1c100840f20203104605004a01103103a58000b0707812243c4801815065580326601c1c240201e8040c101a102c2640900719211200c045000e15440041d02d1304030300d042c00e4000c0d5160a40100503005200c1d812211000034003405c104c410b402100d0300045000d56030040108030b61042d20455000207a541c503008005c49640c1d001641c007804019801207025005424644d1038030743c10f80c0207184028070400800c0701c142c0c5c10000f11052260255018201105c241d0000f800303003600441003020010001a4000e12078014040c0d590680f50f6800300820b0351119642400200c3c00309020042003910100a400350403484600500b44603440e031400450b8000e0b5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 348030332 1250 348029082 348029089
    0xe03040b120105031b0a060309060212010902120a0509070501050f1e0d240e090c03070b0d0f05060a060c05010209060a210c08011a09030a050c010216060503010e0c0702 74
    0x121210a4a001038660014080f5290601c0100750b03510a0415810515800c00001603003090180b00e014103156540b540c00c4104007268040e2180c00011064006007507940703010759006584079490010300240d403940001c5680c001c521425000d070601c400181080fa04280043d00d8a03441b1802840f05080103000c217402c4c1c00382e8024038401e6009130380c0320340b40c032903c41c21680c00a8601c0c45494a0a494030a44800d04220020100b00300301c468900c1041c88588a8201c2d05080135110f00c9295090b02034200e002c00c0e1460350350018400a40c03510010081b401c510300f01c1c0310887e80140e400990110740303031204100091040710711160301c500031400140b0b420b28440000c1e141790b1103401c04001081a420804c1b0700d2f10000b44800d840041c02c5e2100344800720b40f140000700356850502441034036035207602c9109810f40c1c42c0025289200e1010f01243d0a403150707800e1035540d0320426082d05005118410b01940240303150085041110341c0e0f601c80b2400d40c0d0a021001d40205e40042c400f5010135014010900581c1c1d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 348031582 1250 348030332 348030337
    0x12080c0106091e0c0e014e020f071112061609060302090f060c0a020310150605180906010311121501050405060706020708120c0a03050a1e0e03040b 65
    0x11480c0c81c0080c1080001c0804500031070010500042e00e4a00744c03032418503a42040000c06003080c00d2800e60f41103502c941c40c8101032104da110b682403c00300c0355091264000e10720b00c480340990188204ca200910350201040076031182955138881070106116243c009624620704400200009060300c0c103001903400014a000c40803a980c402004040b0031514480350041c0e0b541c00074240c98a000d41c500300c0f000300421150340366046124003504001800304180e01061240c85400d80d4020705480c0c40031042244040a08081c1091050559007041c002030520302801c21683d1500400049043c1c01c001d0380704110b010640140418103142e02ca400950682d0f00c43c1008251120010203045020f0078107040198100006944150501c0000c100900180d9604000d407044c60781d1121004da40c5610510308840c00d4001c0540545080703455a09104504186501404d41e21116a50410140e0b8422138803005540200501550382402d005110307075008480d070010985c0b80481ca0440f0300c0c01759246034403041c59 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 348032832 1250 348031582 348031589
    0x180903171005091006122f0d0c02010b03010b0a03020306040b06130504050607020c03240a0e0d0c051002040302010e060c0a02090702010e0f06040b01170c0a060302031e010f12080c0106 81
    0x12942d0361414044980c00140d403011481c200d46d000c100144650303180340384007869003040ca64400702241940041c2e140c00401c44210003107c810510070808010000b0b400f8007100c000061180d42403c80003840b5040880014044980080c010100c68841ea00c2d04040070101424035600504e041c02081038800b00707800f44a00030f0b48131b40c0083c03d03e03150202c3c00a06000154400c181720b17401607420703900409401d11400890b2005181c0540352902d48411175001031031581c860b140b2900510900c9140190860f1280004500403401d6603004410075038002c040b8400d500000b404103a20001c0800c0d10b04080c0701511007800c1c6071040300c400b4101c0d1780000300c903402d04888800043c2c0d103412a400304400107102d0081d02481a100405031810581d075001c0c201c00050051700141e125000362441d050b101000002601c0d07401420780155035407a400c008020b54001c40b1001c1081072502040990a800104070a040301c0c400c8080100c070f0703410803401301c6403e03203094000e0342c0d4500700380030012000c5000c0c0f1928004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 348034082 1250 348032832 348032851
    0x19170919080d0504080405120106260703052b02011407030c0216091508071a03040302150f0f010b03130303110d0e0334060b06070f0c18090317100509 66
    0xf100c0c1f9200411004d42c1c0d006640a2443c0d041000c20003403036a1201d07042d000e004542900d09481004840410f29104150388050f0440c802c0032081e502c0c50000760840803d80420918641c120540983d00381d0030b0340c0140990844c0145140002105144a07511405140c0c10303034030580d08105035a070b08007004886c03035400590b031407591050307070001c01400c40041034024510300c03000d0a2540d2400178000c1684410300d1502c0355100000000504051080c4011303015006865170034601424201c08030b568003801100c002c14010040340010030402000c0e42500c0c82004502c07884001c044030396034114082d0804100c154200e900a020820708a4964000c0c0d13600c108005000355165540412050034074802c0070030401260700008400c40782c181d40070649444440d004003021030f03403048039808113001c0d01c2100b40181442e00b18451440c03c00210744c1900b0220380c4021405081810303c1c60440c41142c1c8a18401800b0890400b80d5641042e4800b58a540c00320752211305110703d954540100e801030b00d048a60105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 348035332 1250 348034082 348034087
    0x303090d0e040b01020c0405040602040e09030307030f0506131a040207080c0d050909040803040309030204050a090c050105030613181a07180f060c02040b040219170919080d050408 79
    0x5425070701c04008a80200d08072010b0026100c400c0000c0e4075610300008650082c0d0311040001c003880500d40494005211300101042646014803845031690015210707000080e041c1a07400e4031a940354000d09000700001440c108900c6071000003400144441400e940e0417446102640180b0742d141d02c0541120750203101100d58030802500802d0070400c0c4400240148482401100500c0d2100114650b00585c0030380782c241d90740c446007015104100203030b100941c0982414204402d414140d00604002489207030300740c54050700d81d401036410740421910700750805501c089080b9640c000340c0150315107801c3c804501c05c042e682d0b9241c0c4088428540c0031380c80d646a20308180100c042d404489903560748002d0b0031144d003850411200301e21400a5100d03410801104091040031741d52150f005001c903031350003041155201d041d545a0700700280075512400c04039000440181c0300603400b152140c41205d10030098801728105046000071061400300603589840d00f44a4810716600314031440c0d0040d401070600340e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 348036582 1250 348035332 348035353
    0xf0d0b0a060207260a08130905010b0417070e061c080301080721152706050105010e0306060901170a0f03020114070e0904060209040b040504080a0315080606130905030309 75
    0x41840c0c0c2e015640c0c099050640c04c81450103001c41d4034807243d03a021903416600c22142807050035042c115040000440d1800c0000104414604018411640300c4500c42040c1d01310142c0380c54860b0414461021400c81d03540c000f46d401d103410540002407109102c0032102d0100952503868258000360070044860340645000d021426181d4030400e80400c6003085114030510030307a078030414509641103004840303845403d070040341e080d0107803600d0490710801d00d0a030000300346081081c09084288201400700300980000102c0b805e000c0340d100e108030000b400704a07959203000e40b050121160142280c030240140f988a9002409a005c00c080250003540082022511144036455600001c2c03d10802d2003140c0034508525281c01102030750240c2c00c00c0006071111302c0000850007070540309840640c01484e00b8104020000140083c00040207507135400c208500c0b4103800710040089a0040c45515844000001c0f25803030200b01403c004844041c0100341a031440e51101d103183c00c181e50b91080c2da0441030652 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 348037832 1250 348036582 348036599
    0x60e0a050f090f0c060a110105090c0901050103150312050909070201271a1b130906050108060a092004151403280908042903010b0f0d0b0a060207 64
    0x80b6041965000500710200c0301441e45030b0b0380d400344003d04e8081e440110701c100e41140650308402c40c0203d844000e00861410a00030f0362240100d0110320300c66004080040340785c0d4468841c441c400d00b2180d145440088c21034a030b080c08180700001407000c109040107058503989039424020f0089100c2e0700007081002c80c0d1018501c0c44204013034000002611701207100c0108881c00e580c0289a0340d540a081b80c1030700d600303034100c103c0040d4171010210044c1c00244061140140c00d0581e040310f030820703c1081056114801110104001d82d003803607200180c0101800082c2150b80088100300360700c2c80341d0068501c81d154030f88258020303502001c000e00c42554560700070b42c0c12446031240c10891403200c0d4510b19007040324100d880c0c5511101001c1880c041e00f0071001030b00c42d9204041c010b4001300b1560300d4942e64001c40c5510001001800d4100c001403040c030140280385400d0b07034103803a150000903041092a0441c1d540c079800104e030f884107003616050015196110441c40c90050600356005d48995400e06008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 348039082 1250 348037832 348037861
    0x5010f0b0901111606050c0609280219080312010509090c060d06030c0308071a160f050408030f03091204030f0f0618080301090e060f01050607080d05090a1205030403020a1401060e0a05 81
    0xc1a522b038010501c04101c4070129401ca861314008a00700340f030080c4550020500c0484481844030940079641c00105030301c00700001401604445001003440c50b070701d0300d0a00c2682c000c265061030490340121740c0c2140e0b9140039400f50001c0c4820310800100141c3c3c07034803440c00780c0c035459000390354034100010000e06200c2049480819000312100d4a6428101484102c0c2e29a00c4180d0040c10803101a0001400234424001c5800500340841100e484003c001100c2007664800d80b0135009500c102c61411a041d650f079004e03142140e0b003000f810724006606840c1c800344031580c828100c03a6a81d0780c02d0b400002152180700c26400d0303030044080586960418002a04460200300c0042030341d40001c080250420081d15110b0549409036906074a45000785008103550042c50031a940850500301001003154000908141d1140503601d80702010321000c0085e81e841c8010344018005800c1922282c0c00701e03e420f11031101c007101b000c0c000542c40b6a00c80c82902c90b08402e031040c14089884405008501044654 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 348040332 1250 348039082 348039091
    0x809040e0610140a17070503070614041a1b011e0b060f090d120c120c051b03070b040602030310080105010b030f040c0302180a05010f0b0901111606050c06 68
    0x340500c1c00c00d105001503a1440380b003510f040791032106280075aa250303403910800520203882a005914010b0403820b89445090140d0350082c13095600000325a4825100c2e003005180408120340340900303180c043e14075907000c0301c02c0b507500503001c100c1c03103280090380c0c2c000080309900f01000044ca481c1d0303683c90700550000c1c02240354089041003900c41c225650081100d000d6040d00c5032090b900c5c080750000c103401e10102d49024221b4640d500549150a8106c00c0510300d192040d0309105400300602e00641c2d11b45021600a0b00a61005444010415010070b40080322a001411104030aa95540115495025401503070040c0c00200500c80b4500740c001c102009003a800000380400e604142c400180390000030102e12171898043c1c040b600340440c01c0000340166401601c0e0b1403400356281c1c4282071848054400a5500c2e16100c00061109140115403080d150300ba09a130349404c88903c0115402c40c04001480700034060700664078905807008131108024003407601e40303a840741680b0500a041030002032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 348041582 1250 348040332 348040361
    0x3011150a0e120a1719020f070b0105010c1104090f0524060a05033004060915080432030a0816050702220e060a1b0c0b060103020322080904 61
    0x401d858050390469403003c40008081380f01c4045943d41c00441401e107000c00c080d242200d200081080c171100d0668004c00605010b06600340143e681d940045401e4005400082c202400d0000d06a8003880c1c260890b081d101e0240c000e003001210aa103906060000b8044100d1814850f407100c12804001061102d81c000801c0b960800e5007850180401e807500040581110820000f000c14104c0c03081c80310048070b820004a000e142c4850311941c014110030010700400e4881050380620a41c603030301c0388038054410f50307000ba441c4041e204804000045824001411800c850340c1e4421002c0800d400c0001e000440403a030303a49400e0f420200707400c0107140d121984032020800100b02c2c01c40541c548140c82c50079101141c4068010701d150320840c2d4001e040c00241d0000602940c801e00014028680041004d0000040340401e01c1d4260001510701c00c0194070021300011089c400a0301c81d40c020780c0510b521541e40443c50b19104e000000310104052030100448540c50701058400141c1000d104000c004070004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 348042832 1250 348041582 348041587
    0x1005040e0a0e07030f03120f0b030d050a1724030d020712020a2301110c090604050a02090a030c0f0906060203030604090312090b043011150a0e12 64
    0xa088031a80c0c00c0080c001c074030581c1c440004074000d00003003000c2c4009507080b000c2540001114900200400040200c2e08151428030003088211042c0d449a100c0320a0028000c0c15480001711058a8a401500342181400800100118800c00c039084052190940240b2a00880d00c0d24000c0b100c02116140024040e5102c41818000c0d141c00040302c00946d005120404001010f5100145050000382c0011003542c41c0200c01c6030b503100e44603d100c1c4001c1800d88904180444804001d692003c10200065000c0e07902c101041d407a04142e84515000f06c41c40c84050701c0d140714680032036080241a8001c4034020701c050010405910a012100301900b004038041c40300d41d1400100035a40d01010340814070560341d07a03800b041050f000c1d0b0a040a01c0070460b070180303e802c3c150708202040c100304450541e0207100e05540501d810070001c5038030224009003449000d110843c0c100459030401c4854074805c40780704521800300c60400d001307600c0d88141c0c1d60b15008140e000e1a2006c0c9818030000d4032000d554400f00303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 348044082 1250 348042832 348042839
    0xc091306090c020d09210204020a02010c08060619050d021306021b031b0f0d0b090a051c0801031b180b0f121c05120c0c0706020a151e0c0509100504 65
    0x4500c40e0000c890b21122040c00000004c049034140025046c002903100384001151491150113400c07000308c6419a85400101e42d88200520005204801007205d020307030f0140c807000003540160041c1c1841180d207600107040105406c00495084400c2c0c01ca031026034030040b41d2a05d0081d0100c142500301c1010f4016264100d070500c02c24004038103108600e44100181c00c503010003600c0d0100304080aa400240500c102e0601d05281511803140d1b00064440780103100e4149034500032031111880c007000c0c40d514401c450303196407511080301d1403440040a240e81074620000d007801d0b55803046841c100310550002412051141000411007040d0001c0b8050010f02c04c03408610396010a1b243d01403203104030700302c44c00121500204c1d414880c0350300c0000038012000c1440250385102d00500700c8507142c0803c81e13110319107540b4241e0f5215050302004201403101c00031420b6800c01a004030b0455141a4120381c2000d9440100704190303081420300400055020a00305098034200100175040d03182402c0543c0b9041c06c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 348045332 1250 348044082 348044087
    0x14040f030b1003200409120315060201020f0301050f120d02060601030b0d020f1e0a0f0306110309060c09040b0907030b0901050d03020a020d05190305040f0b040b0a080c091306090c020d 81
    0x110b42521090452034044030130250b00e0725041100350550100028086050095018004220945d0008400100c0081c007248890051003283c0a001c0019070301400c50f860901088006001c00e0b107400c5d0000300102c0d0301d040c00201003008020200304c80d0003410652030041c0c0010200c89800c18418841c40600150b600982c54405e100c0d41c81d06c105868045031044040d8124004000f050003041e00000000b034002801c6405c82c40c50001e0328860f4809201000e0f904a1100d4203001c00c1e180c1c440c60303401120100300c84078450402007510201c06000031030003d0100000800403442213070f00001180d11260a0718031450100400d501410088510307000c00340d000d86000f9600c0e0542c1d00001e01860074030001c3c105000c0c0c20400c1d10ba1a841c4210140c01c0307881649401440f50300309102d00e029606a1080105151001c001520706440b500480b641c10281030f4201101c03030325400f404540303401c10104000c41c001d89441903180d12011000e403011800c0c3c5d181c020b05000311082040c03a8400c40d0070810800c141c5e282e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 348046582 1250 348045332 348045353
    0xf070f0503070305070e03030706020306030114040b070e0310060803090a060f1d0d020307060203070507090902060904020703030e01052a0901140d18110913031e14040f030b1003 78
    0x10107503e800215a51200380903501e1040000007294140300119210f420003031190011840303032205500078040c0b001d40c1c0145030f1150380d00351401004600d40700002030b0b1061240c1606800c07071000800b03c17507205803699071150403140280c12100241c3c00008920802e070400c2e150420013842d10785840c481210080100901010702d8804004a0480c411101c003819961803145048440d0001c080d158215a250001303541c0c3e80c4900713411078840c0140680080c400b41c083c07203090081600549020318262180041200940c0103240c1141491382d2461484ea01c80000d11806208500c1c900c2d18454040030344103511203c1160041614840108010010b0244d902c444d0003540c4004003504c0c1603c2c0d1981600410190040c44c02ca200c4100c45182d00005002251030003102c03144040e10612496119500c2080f43c0941c1200301070040784030903107941210940c02180012030032151814020880c042070559009900580c041e840c0e03035881c09424800e0090600ca1103400808203a142c13000d142c0307560303107202810 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 348047832 1250 348046582 348046591
    0x406050403020d1e0e01110d031409060402030c0d0201050d050c0c161a090d080a03020409061706040209101d09060903070f020904020d02062106010e0109140d080a080f070f0503 78
    0x21010b40c2d44005c00d640a41d404203606944141601e2518642640c01002010240c280104641c0342d07902103040b061000c504d1500843d0060080c18410608001b40b060320101408101e0400004028440c21601c0074850a40541100c006250342c441c60040d119180c00e107500750b41440c80c80552010803883e41309003e01400036811400080d22800e284000403040300012030090522200062920720003907041c0e009100350380040b04200000354680c01e403240e010380001c0800a003a8031050100f4090f260000b0b1684d8031091b1228400d0f80552a9003140700038650140c0701c6502c9292460a11151844c1804140d40c03241003000111b04091407910f41c060424805000070b8080d040b42c2d004942952280032940c40099005000641e4079520303070550004403845180c044584046a0300032038140d40c450f0900c1c100c42d60f81650b8502d0271a061616100ca181e860703050040c0c1c415884442c4000048034000644050441c540f1181002c0c603040c909900b034100000c09044c200320040d0196619160071406583c3c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 348049082 1250 348047832 348047837
    0x30606170c12010801050601030c0e031923060414010e100c0e1e181b2a03042c01170a050f21031b0a0c06050406050403020d1e 56
    0x156101c0715420758140c0300d40301074080c2184602001203540303141508194010502a0703020001807034084400c840041c84c1c414a41e138160808852101300b151021407041c03100e80205e00960383c600098203140765181b6100f900903800d0304040e00f00b0040c4440c50b201749180001c018020700080307800c0340c440350310740f4441035401800c540c1e900c1000c020240b15080b96a0f0191015001034a02c5402816080d0031400030300c5c2491080481a2521680c0c11000031f510740110440030f00b040346190b66180d0001942c101d40805410514141003190f448a1100d01d041c00c00308040c4003031a500d900344100000c040000e41a40e0f072004071401703500350010000780003250440d141180107200311800e0014141c00c0c0706851502620703501c541c00141c3ea070840c001c1480700c1504501c0c0c1d41405e04020b29818050103001c00c40790300540543e24520864803000d10f400902510015182040014140356205021110152800e58149603240e08020801d40c0401c40f07041024407500346010700c2442d1600c410000048020003404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 348050332 1250 348049082 348049127
    0x1608070501050a12181127010b0901030908031005090a0209090703091407080d091217090310050103050604171c0c050c0307060c020d090e0a1503050d0c030f030606 72
    0x2100445074021010502c0c00d480500c8049070908124091040740300405205d84009403007d10ba1010f0010710790000510700b00404440c1e881c100d450702d010342186600e503060684403001c480004482030020340c498100c00744d100c2281401c3c80f0030300c000c4150082ca0754820910410440940c0d5031400c400c164005100e140205801d0b6092034848100c4040d889041144c1c858000c0100b00b0050100d62020000700d1b0f55a004401a690011161800d040040241419071103a500d5074045000100914100901504640e0082a14008102140c00982c425a000e800900c1440704208041210801801c03013058420b0504190804142030b0003c1d0501060074190348030340d516005406001a81c0500c0d5298095a0b03c0c4c01882c20103802070508200a4001401000d418003071103402048808182c40b1005d540c0011540c9050159000308440030390031401c1540c9100c0040081c0c1c0800c21043c8603041940e44c4004050145800b0b4000070f004d079805410301d030804600b0300007241e1240400c0980c1030869103100c0e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 348051582 1250 348050332 348050357
    0x906031a040b0109150810050a0c091805092a030105070c150e0f0a08071a0408040b0d06090603051006090204120602070807020301090309150f080a05040515091608070501050a 77
    0xf4130207611031b88440c0300740c06424000314070014181d002074801c040e000002c2c05a981c500d802203540e64000c3c001c80c01c1704c081c040c10220003102194001580044107000300ca55140310b031941000743c29013400c900c90f1011051400d8500500b02805100e03000743c1e042c02c00c0c07584010345542d402e510b07540446032180c43c0340d41c0b690100e03d600003c00800111007101030075214030760340c0703400e0224165000f0f0744161207202c0740140070010b400c03004100c00d101c0c54110f202e060901e07050031403040d0560b0080011940355034640034041501280d9114010086120700000c004500c0303e201c1c05016900345502000c0c581d803062004012883c101c50700c81d01c1050380135600680d00d030301340d1a00c105036000300c20f0040d40643c80e1810351810150091031040594400c040e0614510704040300860b81c1d0200e07104c0c1100014002c0020600d500410f8000070b810503c640d0030b0ba0004070847c05070380003010f4101c07910480c5600040c1c002d8201911441d25402510132031001d0100d10b0b0500d400a0480d00c01c001901040020014041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 348052832 1250 348051582 348051611
    0x60c04060c030c320606060306060c0705031501090f06150f02010609050c031009020f120c070501090c050406050303040308121003060c030911030f060c0d0e070906031a040b0109 78
    0x140c07115a0003558188552101101820b5135084a02c0140000c0f2503911034910465000400390311071394008010720b142d9620740c0148030160f0401d1401300c0607440340000200e425034052180d464444165106100c5941c5801c0c9108181c911000e8080c880500e07100d814800d00c4140c500d506141074160404081d45150008100d0052400358004020145040280642c1c502000015400303103c44401c1c401c803098590007082c04900c6400ca1075090000208804d484c19230790341404030341c01250000018241800f68031102d09441c001d50f0100e401c040c44800520451800d445004041c3c001170b4025414a420755a40c510f040c80b40100d64407a070321800380014000315003210301101465220200384012036804101401030303c000b04080b601d00d9500c1d000003070141800034440c842000303400e00400c090380301e181304010240e0040003892002d60712018403041d2030364100f004c00010805e84a00183c03071031a40c01c146040c21030685901c102030107400d003803201051408081c0340c10b4403d0781d00300042e482c1c500c4515 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 348054082 1250 348052832 348052847
    0x203061f0807080c040902030c0706111602101106100e150307090f27020301061a030a0c110106030b0f0108030304050607270902091e061e0702090c03040c0602060c04060c03 76
    0x440d80c6c2e907000204121906111b0b4010b01895881050140280c400c070004051050040c140030b608080000c0f45007202500d000d4244400c04890f50800340d86208040c11154103001044800000c1462040c00400c45042c00d84110b40d4803960b00e10400d40760b074a041c000213480740050300c54045002c0d21442c081e001040641e001c0f241c0102c50b05501a60346038281b5506d91440e2030900181c4c4a94a032030400103001c075644807400030600c0306209580c07640d5982e081c284024a548e0001c8020054545568010400c09201d14000345001e541110400d01e40b001c4c01446113030058004603c1c81d04180305100020f20005519a04004981080042810a0504503203c61070310028150300405100300010040c0d066130040c8850542a00c4103544c95803504000a0343e1a0244d42c5035070420390400070350b1a601c440301b411301d110202c000406450110a500025003c41c0f054501d61222480003040c40304200812030070b003005060751b0000e8540c1c1e1500c07000c0352070344ac000ca00c100c60500c0201c4401c0d0080520a02d00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 348055332 1250 348054082 348054089
    0xc03030203060328111504090e070902030c120108010b01020319050c070e060306060f010e0609040212070801050102060f0601090e060d0c0b030a06050301110304110a0f03060203061f0807080c04 85
    0x5071118980c044510f0f284080804d0340341940e8a946540d0020500c1c202900d0405241c5036000c101480d192030004c07403034010046526860b07481c1c0103103400420000850b00080d401b554032142055214451401001791640041c0d1001c100b5a141c4090104581d80210640b1904409820f504640025000040da50b40c4a01102260580643c50001c0303025031340c10344c00c1030144006404603015680c400d03041c80102564811190701040403c0107021040c0b82803002024034480280001d03081c194180356004500724203807007a8021842503030042c007895904004181d40044055074a90032400c0c0400083d006800c6801951141e191080000e08503071600000b2030f8602d9030044440c8802c075911909420113410030360301004401c0c2080701c00102c0e460140540d103d040d5080ea1010716645566903802494128202059004054440d00041031900610020700660182c3c20250740c0e80b0b806c5080000c1d00b0001c090200c034031005a00744842c040d0780013031696070100060401440340d489014144043e80147d90 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 348056582 1250 348055332 348055363
    0xf06040801020c060106030605010f080f0c0d02070f020910140d1a0405060402100306030c0504021e0307030606180e0f09191a01081c120f0504030309020a0906060c030302030603 78
    0x503c2c00d20382d60001a41e54100c80d211b580c20004d40f526040115030181c0030300110320000b22840f002c43c0d00301c3d003200425500142000d11a0780340049007249102039070000c0c1c406a42c0031503028120b0040d1309250100d00e40c000420b09403504820b06003945103039519880990f0034000c01c0220404010454003a507041c0d1440110403003a0000c0c40c0c0342c6861582c0381d401302c4089000d08040507500e9462402401043d0960754080c00d1001c0e607900304401c0c04000d400c0420b10603200c0380c0440081501c4001c041c0214010100c545d00032440360304200c0050450140300d021004038007070145040040340c0c03501e207035580c11501c3e04002820f981c40c0c04503101c1c50141c45202044285009103d0b50040080300c1d00d0040000c40b0010f2101d11980c0c1e00d1080c00d0f110440d48841c01a8007080460ba4070310715106544001c864040641c1c0022140180140d080c00c0758011102180469603981d41c03801546171407141440200000d00c4148452810004001c10142141c9801018540c010001c21070b00c1d40e0503c8602003245a94 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 348057832 1250 348056582 348056587
    0x219021c030e150906060424170703060c020d02120a05040e0601120203090102090f040b030601170f010f0e15090c0d1103010504080318070303050a08040515190b0102010207110f0604080102 83
    0x60313041c03a107900e000c0e00c2d0760f8441d501c0c040c0e100002035889100d04040510441440079030918080300e514120091a10f08003241c002c4510100c000380003445602c10240a40d40200301e10b0038904000ba160086059144445410901c000c08280c0c2d071000803501a243c3d01d490380046519464010380719038940340480c01403180003104024034520150301501c201082250300c202d030350345004184821908040600c0780c00d41c10890040c070a0402004ed4025408000b0080350031b0800100c5545084642e5016440c41450315404c101c488403904110344c9000d00800074062100d400e040383e03400d80d146c20b114101405004a183d00c4d1082c40350701180d407a00d05c1d03c05402444940361034945803119500483c1c0038804261490313064549000c0004000083d00d926448035413034181081415222200e008100b25072a109940d200c84103800c0d103200c003e024130031844001c2c1002c0290306040701610f842010319811603106111000100da04030000010308042920725400b518900b10205205e8451500000941d6000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 348059082 1250 348057832 348057841
    0x509101106070f032c010f050613050705070f0c1d070818010b0604030803010302091602070b0f04120c030b01210204020702120d08060915012106080a05010219021c030e15 75
    0x10080e2050b10701101d0001c01071541e00c0c01c1f000e011545d007581d03604e403c41100f24407058510055401640c202c0b1050404605012199840d5603d400c0baa0700221600c01c8007200401c860480d03600e0030521150f01d0342c00314025160080000342041002072a12140b030745c802c500350f04280e000b0b5205580321034025259a903108d4172410952020350080c40304a0144424900080d00c0c07404000c52024061515030280640914100050805400c2800e92000c00b0380104030000e0381040801100b20381c288106242d4801a01d1400d28000d03c41050740821986600322003501003004145140c12000e03a4100c2c0c00688400107400070901d51410205010207a11900802c01100c1d60829101031040300e045403030022642d50350030901c0040107194180390106080109090140c802010b41c6142020b04d41030005106985140300c2d450178600c2c21040c0d03416580000c0c2d001d90302c011180555240212800103080035034804401d450740382440c031450030406580d03056405408100b0310410280c1101c03e5000700039410b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 348060332 1250 348059082 348059141
    0x20f0a0b0c06060a03210513080a210e061b060711010b0616061d0106230d05030301150e0a060f030b010801050a171c0509101106070f03 60
    0x4000400388280c481c030000504180381c00f1341c3c9a41500d6000c840400388245e11005440340d0030b890341031801406018440f001070345203140301140040402000070700c1038004c2810102644c50300400222105540c1c142448040c54121020310a10304054030030b203613581e0184000c00c03500b250610074540d2500869050003042c2d0b500008241c18140f50304001c100d81c070040410080c6031720819006125409884500e00041500e0f03070b2104809141b40052000c800e099030100608460854102000a5055103a028060650804000030803002560811032488558448a61740d020510480740c002c19130103644404544600700303c550044016200301000c949421000e000c103400012080c002030316000880c0030b550b204d030403440c4c103c40001c1c207650302030382c1420300f020851914107220804901c15101d0b01c500150750b104840e208a041c55440342c0d1920442c07001c0266491240c1150000c00c41e000090308000400840d02c690403140501300860030000c1c038081500079000003001c0350400d50307481d00304150105 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 348061582 1250 348060332 348060337
    0x602010e0f0d08010501030c0c0c09020301140307050913050a0b01030f060c030c0903021201021c06031e110d030306050d050a060c0c0c090c0917160e060306070804020f0a0b 76
    0x30340e00041d140c8030100700840d540e0324501e54a8581c0041c890600400195010764801e070043d0303401c1e141101e59503402d0b0701c8130000b181c010707401281410f0b80000100300e011000c42d811741e040d00045002c0e00315240b82200003580110702270050301c440b00112100104000b420000036030210303400361541260b50307900c2c1420100481d81d1101a80c0c51403c05a801c8000c502c00c1c4940b071f1803030751180c0f98140541d040d034003800518400440d2072141d40d07500704030300354540034404074142d1710b05031220010401e01c1c00c40c9000000e41ca607008034012050051081c40b80001c1500d2100c0094120540b00410300381c209040c104c2c00751000741d00913500b14440070b0000c01400004100c80310228021801808400081071044600341440e600140101441d0b0340c0c280a03000450b040200c0c091103602d0701170882500e41450044501c2103c0c8074501540c04040100320420307144484800600580c190380389140741c0440030946546000341074038108441e10000030215a0744180046045101501040040d130320f460312018075a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 348062832 1250 348061582 348061601
    0x2060415020c0a200d02030d08040303021c06090b030102030c071403090a0806180615130b060f13080c060f0a090b03090a06110901020706050c01020d11070b10151b0c060201 76
    0x89001e0720030300c04e00c1c10880c910341e072000c1d4090010030099441c0c00f000c441d01d0fa4042c0040f01055020050882500c21254100040c581c89600001d40c43c0d2405800700225100340317507801d000744d0050041000b1000040c0995000310707000a500c803141d001324552a821845443e84207036001c0c0d490301c00410722000000c0c1c00d034400c2d40400110f0b030744060140d0802d40d40f04001c0b5400c02ea00f01c40710095042c40e00340030440c0106800045c0d00450300c409200000366a6400c90800c1301c0d0200e001040c401590070b282a1480000c108090240980004540c04a4201c2c0306001498242080015207804041c4c8150b90440080c290b11084035264100320740e076140c0311991504291040d81c00c210481200e81c041c003089803a4014140c00410724280381002c140c849400109a5091555007805003034045c1c85280030303410103007044e551180c1e5590221f282414241401902c0d40404102025040c02071280810800c840031000b414113007200c10708000824101d0f211244000d04a0100c0000068030940540144170076 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 348064082 1250 348062832 348062873
    0x501020a05031e06060a051b01320c090f010509040519060501020c1f11060103030f03110a2a0f0807020405130809190806070f0207120302060415020c0a 67
    0x511403960350b0381c003c2e80003c2d01c001d40e01038803c01c00d1200d1a4000c0000b0405900b58030556070030040c18150702403c444a079402e40089120b001c0740c10780081b000b903d0319031142e000000e90460b141040e5680c1c01c41800740714202c80c003980881903409403a130701400a03544410001481400146031000d1900860301e2404006120141801c1000c0f41310760000c18900c6020070080d00c003486100706400061441d00c0f1407200541032082d40711500000040c28040326000e58026120361180d00c15065005040703c404011404800c4414868040020b80c4008800c40468004010100c034080044403021250320b0031500400a240210700c0174200b05450b0064103d0398003c4608004a0b0380e1550b8a1491200c800001807400074100b01c181d5891034800e005032954918160524050740e03c601c00f06252120031348181c1e010072401003070b03492829410000b0030007500194069290142c1c0030b5402a56441020308028148842c0010080f003051031541034511712260034080714803010613820405080c214040b642c425 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 348065332 1250 348064082 348064111
    0x50313060219090b090904020f1207030525030b06151309230601080c03041e0b0906180a151b0c032d111006060e0a050405100b07050a0501020a0503 65
    0x40d0350701154142c6040d41030281c40c8030810f5942384e081125044944141c85d51007110310031400100b101c20000e04018610840081564031140e000d11010822900e2040010020700ea01c18000500412406030b0410000d440203000d0f001114070544482c050748040340c100854403000003441d840190042d0200300241d051804800c0c0c500701c071250300030342d00700c45030380c0880d40c8000800d0480e0803d500a55005002d820001c03501065128010483e4940724401d48021407407405001d09210180728103900210b001c0c0d6803812501482c90b5a03034840c03c00240150140f880702010200007080341e0400a0000111007420007a49001e64003d445081c4a100540000c2c0e0007152000500a00400a82c003010781040c1109008403000d4040b680e012000c540d1b10501d01800c09513281410b0280034002c00b8004a40314500304480d0310051003084030480d0f000511990800c0180301304445040b290000781c0e80018042d983c0c58000d806d01514041b61024024225840090301050b1a0783c07080146008001c500034404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 348066582 1250 348065332 348065339
    0x50108060106270306140a0b240a0e0603010909170c1b04090212010c140909040b070903050307120e01030902010207050603190501080d0f090e04020105031306021909 73
    0x395a04000d015030004a00b5031400e02c05400080403030400c1020202040b0600c6980381d030742d0f15094510104140c46101803481c140721454841d4026440700e00e00a5516409810000580002058181d04000301c0142e000620b0b9840074410040c5038440e0002600e03280c0d60703586d00d01c14180100320f0807406072010032282c1d2040b043d0900d102c045036001c688040040840c1105800817849031880714040c5a400307039650307400317400503101c1c1c0d010402c90300812030001a40030304660780540690742c042c2280140c180d040005d1080d507503652106c19000354100701000c00668a4990554900610790001780c481c2c40085040750070000c4000e40c03108007040755958400e007201090019401e40301c0c40b00000b409031708402000d0025007009405180c0c1b040c032400c0c00400005500515804450080c2c00c0120140c01c41400c4a5100340c1003038004c036020f0304600d8020241c62a20448100d0b06001500003410000c0010200d513040b003131150005062600940e04640d00d011100c0e00700001e0880c104940b010485150000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 348067832 1250 348066582 348066599
    0x30a0204090204080a061503080406030203100509040c08010c02210717070605040501200d0b012610050a0509010b071b1d0a05010b0909061203070b01090b1f1803050607120501 77
    0x18208da5200e0505410030342000400e80180d000102421446035105078002080c0c1e42c0c2020305070255015000940006007040491fa003940c00790300d242c00944d03000a20016a040c0071034055100e02c00c040185039110025460994040c16038540401034915006c503450040c0400c980c800c038000c92050008002407000001c140811002d10b208101c9074034418070040040c150300d50171010714050140742800c00301005569500c10841014142040c0340c800e0001c02c0304400d0714200d0140070780801c039030782c0348071a140100107102c01c01d0500441c0c9a41c0b42c08a004410828891460300d0b40c2e50b200701460120584803601e05213260401c0e1120340d4403a0400c80170900b000030500c103840c1603e0000c6403031440c081d0340e2400e0009220011713110300d40003a541101000c200000f800901000c80c8900107503961949004a980c086c0c440010106214003804510881320141c0c100801e819241203003460030058030043c04244030b0800c5d41d403004d0140c0c0102c004001700541e2140c1c4004c410f85684a0070041c590700c51104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 348069082 1250 348067832 348067871
    0xf08060103021f02010905030a051b0c0604050d0303021e07120c0803130302070302030f0d08090705030604020f040f0914010e0a1a0c041e180b010f05030a0204090204080a06 76
    0x183d040a0800c0504400e00c4525842099080c0320340000700715414940d49052541c0d02c000e50300c8000541c003050b0a0394000124541d402c500c0e000701c008121002e80c44001031780d0744c80b03184181c921880744070000008140c0281c040d40c2481ea06010062402c1c02441204001c0d90302070002180d02d403030401c80d9004064000c04401c03108580000b4009e007903507142102da40b1942e060120a07015407181d2900040140d4080010445540e017a001802c1800312802d409019548041d042020a802112051002c3d0b1400568540e00175011540e00c0300144910700480c005210103003240c610142013005400501800903201510003820a00800601d410074070400c1d11741100140c02403420181c8494501000b0341c602e89140c10840c083d040c585002c1c5e48071801c0080b0b884c00c0c01030b02d848410003001080004089400c99051507071214007400452a0705c00002c0500d400c604002c000c0c03100c0407021400d100015816a005482000411565580c540c50295503981d1f22071000c98209052000d81443c60100c1c00c0d2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 348070332 1250 348069082 348069089
    0x70b040f030c120c0302040f0b060f0c07060f05030403030c200616031802040506061c06080d03020a120921120b030109020a03030c0302101a01020d050306010207060e0f0d03090f080601 81
    0x9404c41c069096a00304005800710320b02c418407103030f11105250210ba503100010241ca4a40c94902940e072000440c0650514100e60310081c02c1c080800c180161301908402101da000c0d9051400264200700340e00d0541d00c50100002203174040c1c100d80c529410440d000148a40207042100100c45400b1030300008600762421601d000b0700503d1400c0d00032005040a400c9180c00c100e00400d1076007054810500d299080c0d46040d1596407280d1128410064150280124000d64a09150641c580150020060580200060780784002584c81400c1000e001c1d070803080040c1d0303812024000400c101d05442c003d091101000040b0400c2d031510b0340f00003e500d814850150030070740c040e120391011845c1d07031000e40341c124000c542641980603052020004140074841d482010f03601c6294203002c0310901c00020301e0302d8445680c4c1401d20404005004841c6c2e00040c142045034032519000074042e0400d00131613001300a01c0381d00c1c1c0e0040203a080310410180c2143e8a601500c0801c06003440e41541c40c10f607142c1d6a5401e10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 348071582 1250 348070332 348070343
    0x20a0308011e05041806050c2808070f1413080613030801030f1406070c03020c0a0302010915140c030a270b07110a0b0d23130302070b040f030c12 64
    0x50b002c0105050540218110082200d0100032036001900c44c842070390720071920303d2040400000c4a000c2846101c8003422003040d58039104501340301c900790140041c80b0251558042c0202149040032241c4118003040002c4141004240c407000c1981a01c081144140034038035150081c6c00004403d09040100680d031a80c0540d10b20741c10383d19544541c0c09040d1200415200d141d07000c90101c2010500300070030350040825a40301c030401d0702c0c40e04000b41009400c16989202c0c450200c01000981c0e480010304003034420000c0401030803a070f507000c00c0d01e0018a10f40b140720791030340101e4035846800c0e010018140300301141d1591490b17900c0d8403003000318850758844810702084900f5001c0c400ea52080300680702c600e120388a8000203503000b100091000d0000d0b0300c40c5051344000203550101c8580d0303004144c1c4003a40038018411440c2c03204800142e50400510020311459030180b110b05241c0708004d04001411151803040e555500c40741c0b01907504e01540000d45040c1d5403c20006440b109103140421300743d4002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 348072832 1250 348071582 348071639
    0xf0c080405030a08070203041e0f0e13150f060801230f0705250506060a050409050309100203040f030308010503010c08010501210605180108010f020406020a15060f06020a030801 78
    0xc10f070560784054041e001c00c0c1144402c1c030002c10220700c80e40e1800e08a20914058040080c603210b84506450101c3d004100455074070014800c2c2c3c407101c21000d0030900d40c080b1041114854004034071009110341510f840e8824280800010f081e2410342c0002c403915000c684014102c0c0040707110f07101a1100b55048002411550300096440f48118040c03c0740c148003a000c1030410030440805a042141c4001c1034034260801c0c8144926403038090026002040140c600740480c52658035000c2c0c40c2c0c01850318007400f6400a95090501300e10920884000d0500c0c0700342d02d28001c1d100e080040000c0824003c16010350318000c0350329151801400c525048800580d24000082d0703180002d141b000c058003c3c0304090540ba6003000c01c45694207076115201803a510302030070f0b203176140480003403d5070b0880d400442a94410807050118590209895540c950401c00e641c148100d141c106a008180700d030b22040b45888150408688541d01080b90707501c06000c0c1d42c82600da46d0b200e65030544007800c0840d255020f000c85 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 348074082 1250 348072832 348072847
    0xb070b040605130b0103080d0c0f020d030b0f030115080606010518120703060c050a0210020909012d1409150105340c03020108090a020d02040f0207150f0c08040503 72
    0x100c1d000b8543c403034009200d603041e01d100c80d03a8210280c6020380080f9007020004c00d030b02a03070010b28841ca60310135005103400c1100c080d220314041d4858000c590750034101520f035050500c540c0c8542d40912914040074008100d5140c52a4034403500c00c3c80c501480d00d0a01880703020070015845a003c0d14400c0039060710704809501140e040001180660a038810140102180000031500340d11681507035507410f450720b5030b581d84030980c024180001c0c8800c0144103403041c0540c0d05680c841a4038507041d00c1daa02071600e4595812001d5103c5400d100307041305959080d40e20040790340c0c2620452440d82090a4071041a2500c46840f00b9040d600425013031400601c0c00e10400f4040c0004424500741e82c064494841c2141d81e1204002c6105407140c80183c0350710001341c8040045581c01440141c2c481942805045102102d6000620000c0004406480307561151000c00500c465076040721895540324080c0140706000500301000392401c0081c24402c2482c01d048450254042c43d6054451a0b0101c05540350410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 348075332 1250 348074082 348074093
    0x120f1d07150315261b28060309080c0a0c050a36020d0e06090f0d020c190b0304260406080408070c0506070b09120c100f1104030c09060b070b04 63
    0x100c3c91014100307510000386041001074140201c2c5184104c2c02017484805800409000f40701403c146003078020541e00d09620403c81c806003208007959943d03e400700c0d0180850620301c140d40101d161143d0a0700807501e00302c04200380201858100c0340d058440d421102d6642601d14100c11403981c0141c102d2240c209100354034628900e840d0550004010014205842c85500904580c5c04c000100c0e01940b15100303201071108104050703403e03081d90740014540100c1400000751940c09140c0820b0013500c3c58103030100c01c200ba403403245002e403c0f00b1403aa6200d117854107181e031307654104d0301c2c0460300b0700485c1040c0d40305110520111001d494513511017111707070340f40ca56500760243d0200505642403041030002203115590341c0000d0180030b026503800e0500d4203042000300c0c1400007900842540e888100180580f01d0f6000c102e00c031540306c100700d00245000383c3c038000d5070141c018419240351380d5100043c003004010141d2030a03002d843c0098402c21000b078032026100c2440c8956400a01240301c6c4d000010001030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 348076582 1250 348075332 348075359
    0x30a020d060608030a170a180308060310020a2d0c080306060c030301081501230907030b04020c010905150403090b07031e0f030c0e01120f1d07150315 66
    0x307109820001d00180e4441c1c00d2030a5800900750f10780022000f08001100b080000301650300103240389020013044501c402640340c41c4c03a80c04001000c1c01300c1c240000780b10b0342e802d100490390000303030450035550788030040d50040c95441c0c0c440700380070003a10b5812001760b000c007034500d00f0070300303441c5030b10f40c041162025200d00c840d80d04003c0007107900480410100107020b006002030744c028074030740000b4a03e40c8c1051444030f007050416081100f011f80402c11040d04403101c2515600c418405640180c0141c407400c0044000e04000c2c10402d420500000d02c030b42c00b8010561050001d40d0249090341d129218401070744541000079140900090000c003010310540c49404010300a00d0300c42d050072a8100c0c00ca0400041c0d403500c034510741d004200348001240d641030701030003080b13401941883d000000d4880d85002030401d5038924984402c80381e071160420f14210603607000d080740609032131030f40c3c00140194080c0d61365150715008180001698500d08160b10303010b405004403004000503844a03050030b1501ea0100b91 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 348077832 1250 348076582 348076609
    0x60503071b020307030803040312020922020d050405060610020303011a0a0908192306270f011a06030c04060e010c08070f170a020a0b04211206090209030a02 69
    0xc05041d5400005960400900c0700031882145082d1f181d00d42410040d00c000f00d50440c2c2402a8010001c4960300d580f508551843c1103260f401ca08900302040c10b14900a0007852020800c107482e11051105012000070750a02c5440e0495054194061100c2c0c00c07a144e000a11541c00c007180c01070568004600e0b03250180c00494080c0c685410701681d5448410b1070840b94185e010100d030760020002c1d0500c80515082c07402c4c142c2c54121411050010680c05907a400c00030203005500402c07078500403940545000d00810038004808a0b000041007001050007400510507400c0c0b010041141120282030076001d0324400d01e032600b1078908040c1341c518140d0711403040a60590420901c0200d980010f4001030191600c6409070340d14003605882c03407524440140c50104a140640c2e01480407410441e80040d882032000d511844031602c035282d910b400300300c686e0a0f43c081200c07007411403092422140d0107007030420302c3c00c100801408007541d00c480c88412480742006031230701034000e4200b40016051410342805032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 348079082 1250 348077832 348077867
    0x30201021b151204030e0a03020d0b0c0c100213080a020d080d020d020301090b0f010306180905070902070302060f0f27120a030c0311090f090703020d1401031b06050307 74
    0x10310614006442c10356014116503001c1070500400d01c070526900450042210307000382c0b0310f400d0850458000a94150001d040100481244030001c0e1203026103100f030300d10000303a0710101c6000c480d2455554000c3d421040c401d40440c540808000380c0094006445101c258000d0035110355041c460f04c84500b00c3d80900c4900280c50380800081d444041c55200a41c001c008110001a510210a080100a15440e001c0a041600b044401d000340101650300501a00100c80e000888491901d003890400e440c036030001c0f8110707101160010070305402180640c4a40c04031000d0000307903034607189030140044069030b00e040001c1c5446003100300905004906030f02619004116481205a00d000810541c401c4401c0703000a0344914002d05055014042e140c240c0700c640250758105848800402c2c50390203010b0810348201a0030020072442c902a81c11a03040f150502014000054a04125078a2803002e101c211801c100081400b10150044800c80003a40c0d400e544031031958940c00b200300c2c1c0800d0501180b015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 348080332 1250 348079082 348079099
    0x315060748120b102606090d0504050d021306030605190603050a20032a0a050310180c090204031a19391112030109020a0e030607020604020f0406030201021b 69
    0x1403403c00c9840010600645c0c0b60602c020b1400490135500703011014028188951181501401154120080e01c06868040c0ca0a40708511180006100a15208204a4001c0c07601c5004800d115054011034881c06041003001c00c10011000100304a941340c0c80b018200d40c108510100c0003034403814034194140e8030711003010b01961845000031305083c10311203c00d4081140f020705110007000100342290521084980070303d010325241c042600d5051482e124440306641d40c2d10441c0135480101800d80558000e040361103656151000c1c0d200039405404151a044001240041c0d42040041003c0c4140c42030341c0400c049074a021a62800780c1404c2900f000c1403011501140d1108042c001c0700b08084210b0511795511006044c006040c401e20ba4140800540048000b80708a4850604403411a04a080b00584d5060b0340b2030203c0d00b0310201d900c25585401064144010558000380d800d0003180210392081000035000e04110071034900d8440240941c001c202c1017000d81c00781201c05059401d02500d01070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 348081582 1250 348080332 348080339
    0x405040b12100c02010c14040510030e12073806040b040e010f0b0109082817070614090a0308090a0f0c080c03030315060748120b10 58
    0x504080020b002c0d401401c0e03a5441c41109140e0900070402e050b82e5078140300200c283c5448070300440d480b0703a0044501800400e804c80460921981c02080c220030b1b4039040d140c0c800c3c1040440d02142e44280e07000c0e5400c1c4c075015442c2c0002e0203060980040501300c0000004410070502010705c443c400140255840340e41c4d000314201030b0722180200c4114055100000400c0942480300345c00325850392110f50b04220030510306003c40400010400640d103148810a0348a0400201c0c0445c1c0f07080f000e03801489200c140c034401104d0480740000c0c0040901c0703528180000e80c4501242082c100b0121800b00c41a481404d0f1071000c40c1c01202200d8001c03411005131610411585c403024400b184010b421a04d911540100b0000404184440c0e1803405089010b5803441c140300805412101228015512941d0000342c80d004000419140c5103900102148a1922116055611205404800540c58a03114100000c614042d54100b941e068030b20340b580000c800141034031860301c480c0008082d80081c900401010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 348082832 1250 348081582 348081619
    0x90203070f06030b03060f0106020d08150a0b0c0d020a050319090b0708090a0e06010903030e061911010605040e060103030f09030606090501170303040203060412140c0a030f020f030405040b 83
    0x20307029107429140030410101c01028185048001044003000900b0100184041680454005410346081c9403d149503180c1940e4605804503001b41a0351100400c440000c2200e2880c02801c5940f0301c0500381c0700c80d600841400e1f61544201c10000740f8a810820001900c12171106445000441e070f881c05aa109880c2d03907411103181d000346001d40348241c012558110918051303050a001c0c041c0c0e40d44940007420107500213400424107010050170300c10401e03041002a2100c0341502c4080e164820329590b00740d00e01c1c201802c035000040c0810358039401c286010660741081c3c042c070010180000014a21a880c6803002c90316a403200c4a48801c200100d02c001003c01c00c9802000080d000040b03001a0a5251a210500b280050228618190130600802015903004291141d00a0b0400c2429001200c0f40030121494512051035444108022403004001400002d9030f40c0c0d10742c8039441d01200e201030f02e8000d9030344000d03807000052a03030700800040c0850300b01604510000d507800740201c0d01000b00c45116 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 348084082 1250 348082832 348082859
    0x7170402060c10330605040315021c0606140a051b010b130e010c0c1a040203010213060201091713090b0d0821060f060403030305060310090b1b03130609020307 70
    0x189001d6010020f004224a141000e01d02c10a0b00c0660130081a9450410042c14500035480041d19043c545207900000c428150102c0d006e44001680b94802c50070a0091100100078034011ba40029420f1084644004c40407000c64000d111a6200c860511505074071031010a0003500d5666519526914504c54a4450b01c00200c80c01c141900041003150036101001e0842d0f07000070741c10042084e01003428000c60080e000c031070000e400884d0181c503169524000301740079100304c49026003d0f40d0703543c03000a00da81d4198001d2250768411205d908c400329100c50b0504180c01a1036000310340c10302800c030400c4048820f5000100b107a001403c201004401a11000280d030440c0c01028540c030151040b0174001e41c50301380300035030102c0700300c644000a118400201d426800749001c010300703042d900c002042265600704030506403483d07042402d00801001b4641800103643c144c4548441c0c0d8244c44010684041603c20761344901d101020284503070b01a40c4440000c0c19902600b82d030540036210b0040b8461085201 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 348085332 1250 348084082 348084101
    0x6150c0303150307060504090203131e0212010c05191806050a030e0d050901180503060408120903190e010c0b100f080616230c01090b07170402060c10 66
    0x30319120b14014a180101500854020b8482c4d00003103424080ba64228040c0c505484040500680f25607400301100c010010190015040d8807100301008014030701d0449041c000b61003500c43c242580a84032070b0130700340d40c101d44010010507014030a0b00d0302c0c055240c01c0700c1c441c01e01928003d10901800c0500180409594000310001107000070981511605409480340e2000454000c01d200102050010311074096400c00c1410000500e6080c0c0e82d0060001c065800740c40000c00b9280942010f10341103500d0ba0100c001e202143c444000052500803000c801d40342c1040001111004461803034904540500724014024140105200b08102003102000c10754811001c1d1400d5a00c5c603403c100d414850116217030312842c041c1d40b084040110b00c104540030702040c803965040c190140f50601c3c01100320b00a4501100404a02c0800c1c03001640c80150004501c16004081800ca141c448440071201074502404c44001002d020010900505004000b45810000f82064459400c2c0600468064655800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 348086582 1250 348085332 348085357
    0x130509072303150603040f030305070504030c090603050c06040305060a2d0915090503091306080d020a021804200f031f050106050a300507030f05010605041202090615 73
    0x4008107600941c0541902c940b0841300281585401e643d01c01074440e403440b00408264803207011407400c40c0100300f074502a5510000e20305c000d039144c1c0c0c18240107001510043d501232240d01c400005078180181103606903a0448050034040e40d0b032502c0103001d0050303039002c20401406020034550800e040ea800440161210f24007090000d2103061040088110041946610b0310f00404000065800421520940c46c10340d0300220b00010218050f0041455500250071401401c12130b004003035000c140d0401d214402c03140c030186c0c034001c1403000d1a0322208440051114822040201c60026000c2040400d114001e2107004401c0c100f0b0013290520760801401c10b40300024461182070300b1118041e003805000c543c6005030a00d9030030100102083c010f103244042504a40305046a01c21405200494001d03181c1e1003400103041c100c80080c0100113000c28101181e148c41c001041007071240702103d044a04c1c8480006104920303070204a40708001030b202d191b021156a101e03d00744580c074406811b0712103440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 348087832 1250 348086582 348086587
    0x117070c02130914010b03031210080105090d030606020313090f061e03021206160507050106031a01090b1e040f061508180a02011e020309040e0c0301111305090723 72
    0x84c034080a86445202d400c3d00c031a4142440351615440010035222842c92904074802d582d1114079442c403070b40784690045280b55083c0340800c2680c00d00010021070104a9950070004141c0c1d0b03110480c1c99010720704003640c0c40034980c01c0801000041e130701f0201e08804460030018100f962080c40f040c7d075028142c41c0c003024641a510420551610380c0882011101c20806000301d4503001150400703181fa000e000c88140035001c1081030a10209502000140d6806601c0e000f4045041c2c2c1c038440450801d10907102ca0905080401e5903e040400030365019200000003003086048000801c0080c0c803900d62003078190ba940e00350009014010080e000400000382c0c43c4d0401d5820580e9501c406051035030240790840d44040c001c0c60050740d20402c40c494a05e540118003148405100c0100e0851045064881d8010f0501d12010b00c1a100482d00070810790088001300801c0b0324031454248503002d0034038016000500541d0400041c10441003055204040346080d440308902c414a4110021010341c0012005c80003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 348089082 1250 348087832 348087851
    0x22208160b070209181c0215070c0c09020a14041401030608160b0d0f0507110d020f0c0d030212030a140109020301080615150d05090c01030b0117070c0213 68
    0x540355500081c10300d10315110302d072140540209046100140410314130805001032080c1040c024000103001c01e521020071310046910b844020360302d400c29082160008150300c0404c490310b02035100c01004c583d201320b200c2c0c009413800042c0d40081d008901c220040c0031103120042108141c3c04e0003000a000c5d40c80c044101e030340d00c440004044030095040301516521081c0f54092003c00004600b0446010945083da6606880c8010000d040750348002e216035405d120600404541000034002e00e40703081c40440e541141008400c90383e90103074000c000a50340005145c0244c40c10848640c0c2c00c0580030740120703082004007501490550784100c808504541e0b42d142e00c51400c2c064502c40c640100780c4020150305550405180325142d090207416509a50b2a40000380040d44a070542b62440400303c051a54442c103040e06010058201103500b0a400e000b00030110301e06600070300c10402c0103041039491100f081203d404401c407141c406000340c070034040d034142104016036800030340102c20101000d0220b0f01d8241d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 348090332 1250 348089082 348089113
    0x60d020406120f02070b040f02041503050f0d0503070e0f1206091f020702100509031221012301141204080c10050f130c08060403020303060316030c0603022208 70
    0x10f210f844400c107a4010880200410b006104542d08540c114211600190841c4009401416130b002540107482c6d410384008180b00c0c01040b40301c05081c20106981910b8100441160648011518a000f00d1219440d213034071400c1502c0c0300380219a010308081c40303034041c00300c1c06890148100c800d00d21710791028404072400c0611691a2400380720404080d82000e2455000039901003545030a0000c0140c0170441842e29941040918a01018a00d00039a14801e03407e00d69400032500d20300c105041408000003504100c41988042c1c103510b08101880d195104a004441c0030b00c03451510111000284100809100703c0707004640282d105621407592078111071031584c01c00c1c6280500400441c07401e02005106240e2040c1564440100e4a04002c01c6103640340400e40c0c0c0781d1a820101040c032400c400c01c4100764000008500822084085800610300d210a418030103034103000c010900e00d140c5104001d520300a4019040000381c840326428242840503954000211681c8259000e81c06901c0440000c1c6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 348091582 1250 348090332 348090341
    0x1140709080f060a0b21071706060a052707020312010905060307030809061312260d0930080c070309050f010201020f070803010f120f030c02060d02040612 68
    0x601009401c2c0c8050000e0b855484180c000c0c44280800e458a5030350711703035a41d688804116407000e0b0845c4000e0b60020b4840c103035a06040d0140c02075814103006c1d40c6042c01400660644114002860b04070050704040521030a0914000010141c01e495806175060700000d140b220700c1a400c40e4000c40c0c4850590050015408040e44425602880c0800b40034080e200030a8900613250400741d1203070784800510100300d1600c1698000100111450380c007059803980c000e800c814803409400c1140f003098492110550340c62200300c0e4403520070010000707002e00c01c040c1d4009015860080840310a00020506c1901d40c0701c501100d801c0041c0030102e401501c0342c1d0866400c580103540c541403103041900d1582c1c0030f480c3c00003901500c2d2080d24041c01003c60780e8401d404840c03c0072200000c10ba00d580007450718500d590820f0048000403080f203039000c01d0030240c10001000441d0080c0d503d00d00c104254038181c4403c0746804050760055801c028582c45a0941c0c00100000d241d103680d81d9410700080544181100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 348092832 1250 348091582 348091589
    0x9091106030402030d1419021606090e0106110a0b01080109050106060809030706090602091c03020c01030c171b18030c0604030f030f090f0e0f07140301090906090501140709 76
    0x3540180706020140e2000504518a005242071000348105000d8503440540140b101031042d500f182400250680d0340810301e003000340741907071500403041c1e100c1c00143d0b9440c2c5c00b03029805100ca40d442c010031080348150071007070100401805484121a00ea203c0d01c01580090b000b400c0d4580d1119030a02c1001000d104110040c00c440c070717042ca110308000c0c10482d10780c420700c13002070441a1210000014480994116202e103072000b040c10281d608101036400001b0380e0200140c0150191541c5044294003038010003a006145079039410000d07640000c0102c10711000303020b240d2060101c1e00f2668400582000030070082c3e0319140810300421041c02014600500710300120300800080c402040086c40090300c0346010380d414205004440200b00c422078002425074065941d1140d846d600064640c00e260032140a44807001050140b6030f50400190382a8416000721140c2080801c01009094545c0c0c1c041003ca40c03060602003020449a2a071500792000520118210344900f000c0c001016009810305005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 348094082 1250 348092832 348092839
    0x5090f060102120f0903010e1609060e0a240b09100203180907180b0703080a0b10140f0c0105060f010212090913060509011b0e0303031618090911 64
    0x8a18003000001c1d19030300c14180103c601c4001103075800c1c244c6800429640c8401000d0000c0011145003030210b0750f00c0c5080800d06a2902c03800d6000310b1055102c0c02401c0949507103403002100e90304c0b21514103000789203400c88401c04500e8415100c403048481301001c0700070100304001507160781d20302e020040d1540d1000c08040640d842000007500c060101440200c5440c4121202c0c60f00d540c0320344050360802c01c6018141982c09060102180700c60300d03100030308211802980c84d07454507560040002c0c1200c60701d851007540141405445c03810184102101110900400056818a1400406603055410102c0002940e946800421059040c00381e200601c02009200500440b0080c14007480113100e0420880c0c0035004040014981c41140500b5142180c0c1c482420401460710a14060080c080844080c01a0800c082c3c6145100d01c116840000c000000300a0346c51500c444915401c607075443e41e410418404427411142c0706142c8082c1d890001c044e20781c40490740000510342500d400d520520b040b8403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 348095332 1250 348094082 348094111
    0x120609020309160506160f06202205090f091c170f04020603150609060a0e040e030901021b270a0507080c07030e030c03010c09030b060a03050c150405040c090509 71
    0x440c85036080a0f110b5081d08200c007101d02000c42d090548c05403050240403240c000042c0141c0300090f0216009007800c00354280451030001044103c01440300c058421540e104201c0e1010442000e0b1029005070400004801c0f41c0c00115006403294500c1c80c5824075001140740040d56460490701142907944c007020690900381140b51990010328103010151541080400680e1801c00d26101c410031103000b0070700241100d440b118050002081d02803212803c5006500309035040c45855000020b441c2a0380c1c05070054a02500d01041ca20300100340c00d18101d07444000d01c2140361004052040420010810500303818191510b146171600b510405084141004810700c00c0010010401b000e9640340d69040c40c043c0080310a030000289000c56000005600d9440e00d880c04030354a400c403000c0400c07644203515101240c0d4601041145550386032001070320603005132510821920f8800031052110482980c041c1c10691220085021500001c1801000c118641c0052007503141188401e54840641942038a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 348096582 1250 348095332 348095347
    0xf0501200307080d021c050916030b070e0a030c03052410031e02041e0b03011104030b06010c061a15090f1c050a0b15060a08040201120609020309160506 67
    0x507542e00c03410390042e0040d42e000c2040759802d085a01200c50500415405401910884540c41c0c014601a0f40c007030554803800c1c1641e4080b414005105080baa000035a60441c0c1d80c1e020b03010380e80f0601c03c41c03a090740001c2805000c400688468010b0f0051070041c0000c250300f000c10001c0660154111100e040d2171900141003018088401c02000160382d4000541140500503940300a244003550b44001d61050810011200050f28091500400c003100101405010103a6081c03500300d4070400c2c1c8244040408100900c041384880c1415500b203241803424036020461500c86500700c440c0c85500c420003a0580c60115081d1078100510302100700b55021851409100000050421060840cd680500700075401640000b882905840040c0c0d080030555a511000385040b4400300411140d0b9074060130400014a641c2c108038080e41e1854010345c40724a00c903200e6400540f80004000d00c0403090325100e680201d02003540e400a90f004500c0314000300b030901d2410224080c044103581103075000b0740044c032218 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 348097832 1250 348096582 348096647
    0x30f0f0108030d020a050d051303080c0a0e0d0f0b0a09020306060616060e070902040801060f170a03054b190c02030c06070308071101021207080a150f0501 68
    0x290f02c1c0111410005a9521500c1016100b50103011004407129240800700f02c2d40034011f455440391948a41c0d60207440d90b544181c12495030103895201c230006108180c0052050400c0001c030a03000380100d01c01c060703000082d51412030140701160307007a0380c0c103480c0d0451030218101040203a81090381211198105101e403441c1c140130000da480054640c80d11000d2510350000180500c801800c07401c00c0541d926600d5081e9503001e060f682c0308514103034081480015113980310f80d0a81020351200d00c041e102c20491520304845e19000f109010003030100e5140a80c48034445111494003042410096080741038259561554078103010f001d0130700e0518100328071494041a81d0007080014042d0400054886050021900c1e00692044041d00904001603500900d50440c400b14402c018aa0f501c0d43d540310480c1c1518280d014051540940000c804c0102e410399014030345040d80518501c02c0054014039466441c3e41d0b0200326445140300340581e038028412543e001c1105040c0350280d4070031904554818020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 348099082 1250 348097832 348097837
    0x6050304030e0d1e0c0902091c0c0b041502010f0b091305030c061f060201060e04061806061503150e040f02150c0105060f012c06130b030f0f010803 65
    0xc0800201e41624602e9075600640002280e800c80d141c00000d031903107150900c0308240080c05444400484000090b01c074054022145081d0b0b0103890304000120180c03d929480d020040100d4203954108008100011000f0250004100030749032100c3e01600150084d0071640c4805018141c1390420795030b880e464850205640d0021259540c201d03c0c2203035400c05a0642c00b600c1c81074138141c05480c05010b0302050340d96a45000d8001c45800b00541036554006900f00d6140b0700c544c16034198500d0024001c41c099901c201814458003180b580580c503144d40b05030840d03815800008401c44112801072009a0506c203451600c0d03180e40c6051a46030030007080e0070740000c00030b000078101002508504210340307401a60810444800c020341e034440440081a9002c0c2400700c2d03205008003042a503203842d0b03612904414041440c01d4582102d1110580800761030b07c03000c8c1407070036000f1504002c0c5178100780005445c1001020000151616410803003248a07440134060038402c50350010307500601410030301204 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 348100332 1250 348099082 348099091
    0x32b05011514030c041d060306010806010623070f031d0f03031206031c030606081e0f0a0b0a0602032505060c030703060306050705030610050a1407060e120c010b04020301060503 78
    0xc0e26140e1381c918006062500c01d64010081c01c22030307040d21504034900210741781d02512040341603a0035aa01d41c01403a43d1078000740b2031900003a042002c0b544502c0c0d656401e0841035000c0301c2a41d0314004041c1c40d80c1c05086118182140002e04005d01e00103401602c8440e20b002180c2115440b400e480d041f40040da4a00541840c111039110f0100419039581c3c04014080c101e0780901d03000c20b60710610703ca01400800040c4a0400412030420018500c6134049155100003a8004402c0e41d45880c0d00d03a1400f00a8001007504907250340d2131022600a91b5510381c10070091135070782c0c015583ca214194440001451b95550320169960490920b400a000424040e51001103075501507101d5580f180c0450240000740d0001d0003907840c0c00c0502c40075070743c804011840f480d0107442d44404d200e14024101c0b01442a0749003030000640002c400204440c41030003e100c031a00600c00400c15500d540c585905140358500c0040c22036a0015056180140a005800524508580c111b0940d850580054080e100082 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 348101582 1250 348100332 348100367
    0x70b070206070e101b170a0f050a17040510050108070f08070303020c010c061811010201050907050f120307060c08061008040308010e04050f070e18120912032b050115 73
    0x5d801001c1030007006001d41711079030061a41ca018441c02c0f0348003c01a8800440f541c00544140307801c01a060149089075420b05660351416050180101e03007035982c40018000b25154003d0520103283c4540e180260381c0a00400b101500c3c840e89001041040c0e2255940503103800d0f002000b080002c80e8020030010007505081c200710040749440e1603c040244501c00a8503940f809a080800502c418a800301e00004001e030001c1000e80c440459003980d50506100d0968040c400042d03000301c81c2007030040c0075a4440c003101101c0c00d18130280e5a1009540008a0b51800141008100841d5180400800110b0105410003d0301400d158a004143e0710050182413840601440807500304501007146001d000184000d035124680c1362004189000300580d403400c0d40802126000030030000204c1c1c03c2c0c148146444c00c4500d45000071007440007a03440c48403d401103000c140300040a85100407800c804c4402e151a0782c1ea000515030074118121b520680008154541c010798140d41c480d007002e424001218400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 348102832 1250 348101582 348101597
    0xc050304090c11030f040f0509060d03031a06030a0c0f0504030b07050f04151d0411030a0c0314090604030f0e03251806150503060310020903010b06070b070206070e10 73
    0x42c0c160781ca01a040c00c5080140f10010700703040c0c21540d04c4080d10540b031484440c1072416075500c0800008210641b02a6072107a440c08010000074000c0d400240464810071495103410280e900240c6c0b29041194500c43e2141c5030160024200d40c044030b84110b144581c28258103040c15611900c4448500400c0c01003070000014408100d42c091000b0790340107100001100c106409520b030300030101d00c042c0070300c48501c000c1b12029204501e032a015800d1030107003040e140c40c2955500d0041c00e01818030b01c400441416503e18000115500001c1d00501c42c0299100a04017800c1c5440c000300310542049654080009050f40f40380260340101e182d100c03568280c104142c00c0880c41e0071200310085584e010b00300d040f40300c64150000b200c1540044c0100d0b400c130180010389982e28402036545110072034845501d0340205004c140d00c088140c1c00b81099040207400000c00c65016004906a580f200c0c4090380c0410742181040791040d410010103a01200d03603d403403c141007551001c11b910202c403590000510680 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 348104082 1250 348102832 348102851
    0x70308010e0907050406030303150501050901120510080307120f020606010903150e060a09350d0e0703081b07080c0d1103121e03010b0f1b1501080d0c05030409 70
    0x2c0143d04040c0800802c20840e8a46e00d1030054002c10554840c0c403d01d0410b804000380e10340c0a2019200301d0541a1141824151200085c03070040030010318440100c140b1600c0422082010000307030948034421508041e4000c03143d000508204851041101103500a004100f1142d91040090085031340c001c3d0070704440361007440382d8005000407a81d0540913210b2001080740010003600a01c100c20b0183d00102600000d49021141028650a0f06038504403140c1c030603040c401c0781100502414044050004201080c2c2680a0818401e5801a1215440480d450070240c2c090301080d4004c080200c0103103403c9291610b6541c460b0201645c0910a102900240d8180880180c3d920b201c07000007402d0303445800c01007000d83c0458200c084c513000021003030fa0f155202c0480131812a0f0603036030740d02d154900388a20030030f800900e54400c41d009100708100803142c030301d40202002078441303075245640450425070400c00d500303161402e03540c070800401c40d01d801d00c2008110040100c0302941c00d2020040f58503002e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 348105332 1250 348104082 348104101
    0x20706020702090f0106091205070b1b030301140405060d020a030b071701030b01060314101208160b0603330709030804080109060b01030e031204051015080111070308010e 75
    0x201e44000c0c0d0008140750410004040b86003003e070503602c0a40f91200c500d515041010700503110524005c1c01e650000e04280038018019001d000c910f4585014040e5075000072500301e046030401e0b4441410010014950342c0c0f40e244c2405001d40c40707c01501c0c25481d072101500042c0740d420300e511003d003d580c40c0724085101035205031000980158140180156969285895280c1002c240720f03880010786403900e041e80080e00d8400301c41c0240c0c482070398407400c2e9081c50300503c0409480c0c041201e801404000d020440060044d404040e140151001070b4140760200c249402d2600b151150701d2082c0d2200c4c0d4074248400300440f0b58000e01160b810380107855448001c1614848416000907003a00c001207000190382505400000b03903c3e01c65201400320044000054050303400036100307207035190403e0010050302620b200901c1da01a02901c122241c5d4030440c80c400f0125040c44060500c0440038401c21303c145802405182002880d8241d1711b85403001e56203004080d0704060242d450079500c202e000c2649500f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 348106582 1250 348105332 348105337
    0xd0606050402070309090b03162c0108030903101b0507060f051603060503010902090406230711010516051e2a060612070b09030a050a0302010b03151902070602 70
    0xd8050300c11942d079516401c0140c541e00703052180e40711203401c00101c0c400c00e05020130f842a0031180e01c5801e0403441e0400545240240003180d10008900c0d150300e0541c5014050078990b4001c00601002d150750f000c040042c581030030b01ea003d0000d8003a0903e45000c40380082d40040c2121a401d030314005480c0c1e0780502d0144040e060070207140040768108018080106400001c2620345011074400b002110b903190700345420395103000c8010703600030307080310019000c1500f54005103400c0b0120400c00310603c0034684145500d44040d1040f400155544004d600c06400c00d1081750f8009903014525119103020301c000400c144106c150705405000c5c250201f040c102148401d03500729812807101440541c080158224540321039132400c00c802e225a90114060382400e145400c441c0c008140070f00000382c00c0000603086680040007d03500f6115070704200340814018000340c62024402c0d40081201c1c20341c0801c240c036105d00006180340c004810b00a02041003001c4030900381540b100310780941c490310f09080010090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 348107832 1250 348106582 348106589
    0x30e060a020a0c060305250c140c0a0303021606140307050c0316080304150506030d2003030a050a0617071203050f12010e0a0b0603150307051201020903010b1c020d0606 74
    0x40c00f849101007a02609030f004184500c106902d00c0300c066924003800ca01c180721988210011481c100c4031000800c8544640d040d040d9001c00c11141c00320b180c24042803201d11603900030740060b00841c1141d84000741510217480182500c2c07620f00d520b05091500d0100c948000351003807040c08030004410320404000c1c02a500301841d540510f40a09010341811450b0341e004aa085900c82c801e81150130070240d1a208180c0200030140040880c01c28541c0300340c1c1c0d08115003810314450104040d80c008001000c0009510071b202c2640d0200e05828442d0b4010140e40c5503801c003603c03407a1442c1d512202c0c88400201d070001c82d00b00d1500c41c1605050f500381034071035201d0701001004c0ca000010310015000c0700f0081d03c0d4100c41031164101d205940d202090b000b03c0d10701e160040c0e8804810004580d8203000c415001900c01d5008060b1140300303607520001340503140107803d8402c1c41d940101d0081e40741d103402c0c401c00e071003d1410b650001080c502501590880308030454001d1240141082c8081440039660110028 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 348109082 1250 348107832 348107843
    0x14040603080309030d0b0901061d1903030309020a05010c03120c0e060a1d0405060a030212150f0109060e0714031f06020a05010b0a0b0301052103181c030e060a020a 72
    0x490403c8403100c1e40b40c1d800007210f60952810400207403141d0602c112058102c03461a036540d42d40c441c3e505502e012188070050b00a50201990350f852020a0828102200441c03003502d0010b040302281c41400740c1703081c20707074002c030706000b810844000401d80003140c0c0300349000e14100004a80348290425580e140c82e617107601d90085808180c2c0100d10381c00402e005030140a07150112402a035048c20081610703070450b0441e810624031141000181004c1045140d10110b440c00ea841c060340780260900801e10031500c10041241000042140c80250701c10382020b032090502d00352081c5080342000d031900785880c1500121210000000d40740603040001c7c0404030f90450580c4d8a0340b5502c0e08000c0d41d40501a90955140d440c040c007004d1303913185c0f00700010100c800c100c580904580c039090402c860980c4e41c001f000001c1042c04a0b40031a50f20034001040c01e000b0060040d03040114039000d00956842c140008056034800901e4200802e0b082003035400300c201e044070f00d0799803000d500d8002c03800c1c8054034900404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 348110332 1250 348109082 348109087
    0x9080306030f120f09060d0903082406161b0807061701141c0803010906031e03021c020c150a030c020d0e010305061503130b0703020705071404060308 66
    0x100501440150301420007201190020b50401e03160a403240701d0350181e804400020820328410790381d013101a00e1002d03801000181802103032507031041070320400101103000030302c001c0400c4259040000580c1180c5004441d88011081c01d5000c81c0a5200b1441c402c0e12015010056108100080c0c0942400304880101d5030340c100d0351141c803141d4961a9006030030202e08000c01080b070050580c01140e040760041280c03102170551850038030003003114110030700fa00404100b0381030000c521000015402400c08220000d1001e155080c584450014401c0070801c0185500381c0c3d0b00440e50014101e00001c5054007520140e460500b03043e0700d0000070803e01500300c2c0800c02c0050075807081002070302d001a0162070501c0049c64400040f45c0382c0c0100096500420307c040c901114652290f030105a0203107016140940c01d1000d410350854507041290b03d000c0040000b43c1545c100480c44070342c2600205182025800d16041f0f0340c8003074940d4241e000380001036441c081031000c0340e5103075004480155004000c007030303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 348111582 1250 348110332 348110351
    0xe070804060204120302010507080714040b0a02030c061312030c050912010b0d030c021009081e0a080705030712090803040905040510060339140a030b0c0901120b0d08031801 76
    0x207020742350449081010603080c400281c0900d00410054540c43c80368002a8a4a828500a10310030741200500d071302144403e0000c0c81d04030000300f10060042c06162035801300c2c4e061900e030072001d0b01002400391040505061040e10683e80000690f4000241254502540c854251040340180140c6000035884202c84000c1030a01d40c0003203440850324004d580c1014112001c4009480b0709041e0301c982152548411803540e43c5a0310f40c940100180c8007902030303900c050345640310240540c2003208155040e4200044440400c064201c580302400400d0420345406407070444e80c03548a001c0c0d403080381c50264030b8400140820800788200b01c0c4801d0082020001280c42c0d081064220185041c21180c400c180c000b0440159134070b250040d50101212000c0309204d0074498100c0c0903681c0300c091540c10418840c8044001001034660742d1246d000c210545450b03411550005003c0129240041c250a24218028a452b180e40100050b8142c000c03c007140d0b03e0700d40c03054203604040c0c039400a050035444c112988 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 348112832 1250 348111582 348111587
    0x6020a030b0405010803040311060703020f060c211006050c01060b1908180a0201030903020328020c1f080613110d0e0309030d080a0227030f070e0708040602041203 72
    0x1c090040c0180c0d802c0196a80710810140d9030b103d136000142800d00d0f5069100030740d1421a005080c00c030702c68811b90707a80c800c038410140d00e4083c096501810100b130226601041a40050b036074403104007008681c955905150b00d4140c01a0402d00645003000400030314886200001d42060004000c91140799680f0781c01d1005210113080111201400544900e0118441c102080004e08004421401500e201082c91313005500401804004800b54002030025454844c90072003504691046016181140c0c81003000084c02c000946464904c2030800c030074007614080c060008844100003070f00300500c10b5120180082c40301039036005a00030700340c24020203034010a03852010f480704600c080f500384150700419800369200c1c05030902254061b48a404400d0000c3c2c8a41c21940c1c010030760140061828611505c8541051104004510086070105098040d03080c02c2140d501c1458101004d444500e06001c0c0b040000380c0c000d00300500f0019010702040170b001d51030f8115002003c00030101819103c1601c1d01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 348114082 1250 348112832 348112841
    0x140f0703050f01180b0f19020a08040b0c12043504081603080d050c211008060118022104061a0301060f05040908040302040e031201210201030e010906020a03 69
    0x8081083d4201002022038041134040e9041030b5030322803408542d035600c030385038181128001400080c800d9000100e1542568903440100450070141e82c40d05007130718103420040142c0b500030b403841d41541c600f003129a141210110080d9003141d8805d2100215402908040212072600c03203a401c0d0b10b1980080c504145080c00c0300400807540340205903202110180740040324141c5511003d4280c0800308420ba100411540c0705070790284001000768200409000d02005000c003d014070b5145040140c203006071000140c103e01b00911074040205807541c18000c0b04240c1c50301c520003030340ca410340210782c21124000d000c0c03d00544903004074080302ca82c54030f8103050000e0301d80440510310a40031038080044030f05040c003400b020f481881d01f214034158508070900004040940e02600d10301000c1c0008801070703855001380e010346080c10005644030707000c8001c201e50341c0d28180c0c030a05511030241c41b0f004d1003004550041902d16024240012104030341d80f1458050403003120000d18141c400a034003075565405912 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 348115332 1250 348114082 348114103
    0x409050d2105060607031b061d0105060402030411090c1e03010e06100905131503080301060f0e090408031911130f0503102403030314160903140f070305 67
    0x70304040c5000520301c003422514260383d5150403460800411700401d00070411068500d4000b8696880140191181c1c822078520703880e01d4490540c0c0302115001a40c0c02d016658100d0000c85046140d0b04141e030345c0f20050624829242d01491065000030f066041c10410740312600000704000004c43c0f4080c1d14140340303034001d018103242501102d01068544c2003070702401d212030910792201d0070b0050a044c10080c5007048a159600e406445510400d80c0189400c00300c0c008502c51030200c1c2e220750400030003508940005400d08100007a00040e522603543e80c14000390416000642140c2e02d4070350b403850f00752a00002c402d40180034180400441c000c2c1009000780020700b9058040f92041d615400d5103024004c583c814103a140c1e0003244150803032000e950100c1c5071240c0c00c424039200086491f4080280d500960303c10340200742e0368482601001050540982c0c4030054584910403940b108901a04100032808082c00c2051942c115418100080004030704154900040b10315003036892074020ba60303620a10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 348116582 1250 348115332 348115367
    0x60c0c1202060a11070210110c041104030506011208181302130302090a060e1f080607030f050a020f07150608011e0c050c030a03090218070c11030f0c0d020409050d 72
    0x8240a0304d121550140c030400d50b8024450740198008140071540c0e03c1280140d0070250003800400d810b113a45605c254150b0f0911403070140c1d1554514100f00382400c0d01640b10005a443c024501c2000498131400c440007070f00f40daa400e5a1104124000c901c001e03603030344c83d0707e50414800142c0c800c429450001c1d00c403c591003140c0658142d902d01100c10107441551180041c041811004540c1d8401c4100c01d010192042ca141c40c0750295840881524200301903030078501003540ca150710072040c2d2244c0281c84d449843c801b400d5103403071030b611510712080c030a6600180c01c10202c807801c0001000550042e400810800d4020f000640d141584409043c00015106410710701c1c180c25500503e000e081510700018444014500748400118190060960800120380c405c08041240701e05d130290903469030180c04d003640d0301309008a180c0740c165818011510316511030351040902c030018034000101c03084011001e841c200c0c03400501d80b01140203046010b0b0014498011940b80403103080d81301c1810700000700c1c00d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 348117832 1250 348116582 348116591
    0xd0b040f0b01120b0d020a030c08070f1505160210050a021006060804080a030f050a060323030301170a02060c1c08041122050108070f09020313060c0c1202060a 70
    0x114a40302107400d24600e450115002280c00241c40403250301c4151914000f5060480b00401503000941c0940290002c4a00488956050203640720800005016240c0c41e01c1441f841801e01c0e0868030030165580010042007000900305070b0034018030305d485620a90141c01514803241008019165030840f5100ba801072150059a81004069010711001c80381a5210000141c45580300c8841c607a102c4e06040040c1515006141441200d6100d1b1501c9180d010000290700c0d4110b02d0620149650010918980c0343c0000d802c160501d0040200c2c0d044850303030344d00c0d81d01d0781103d003003040c0c14524000d5000c2d603c10000309032000c0007040070403504c41130084c82000440d00700e48400107a402c400165009083d00b00701c144c96141e2428580040200281c0c4010030380907800b8140804815100c09030000364240c2c02c000e5040040b9030025028002418640a0a608500c0c1500c5054481d00001c240546516258918030402c14000d1048510041d00301e03508254580030307020083c1d81c5000030b90b209021507141 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 348119082 1250 348117832 348117851
    0xa03020d030b0f0a0b07050a050a0b0601080105180606090d02030a050105010515040e0f3103032711061e090306010909050631030305040b07030506010c030305040c0302060d0b04 78
    0x83e00000720034510007813400810f64200a403042054220120455191261980c01004107904112254141d40308041d400003518040d00010a0904c044c1e00943c0030700c02410b0f010032485038070059154420810365146454100000004090341310f8070308080d405000e000f405200f40714040d08001e050311030941d102c1007003544805031b80c1254030039442040d051019001c04078200980074205140c00655000785000c04032090840442e02c039028031448030b543c84610300090300301030f094025206601a801035072506200140c204a24a149242000300344207004141d00070143d450360203540110038120b0350200c01000040194559a00c0b101465200780300d02800002c5442e0140200c2400950180140445446910760400342000160020089411500040c51103402c01041c011441e806a07030041124101070400070750019014156104060801040000c10b981000150704426458070b0700180300d52380d41c14501007441260704020b42c401d0340010300c1c00d001c080d03d27049403c5c8648100c5042100855 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 348120332 1250 348119082 348119089
    0x4020d0f0b0d08031506070c0602030315030f0d080c221703040f0501110703020303361008100b040f030506073b03060406050103031413090c030e0a03020d030b 70
    0x82c20b40b401000590304000180000200c9083d15410f1a0094003050410445035100c00d004140303904104c00507030000c020095800f41c0c0d02c132241c00c0848158042c100401d001c0066a072036505c00e9a44c18144000130000c1103519000100325401c211400c0da4134600b48080b41040700701c01e059442001c011503440c419205113020003001700c808075030989035000c0c0014038000054401181004200c4803a014090340000943c40501c01480f03049d1020344154079504000020740260440510104218201007000d5015a141d13202d86080072030480c00c0804e5a03503290702c24200c17000c0d180c1d0040d0b85410b6002c100010340c8030f40080c0480550744181c4c2a074942d41d0720719500b25141c0b14511000181d6201b44051061514680c40504441203a130044501c01c3e41a0000821301d8842e0603141112005d9075000100141648a080490b041c00a070f207101d4546000e40480c0a004c80b01800343e1240d650395030040040d028001d500c0340c6658076086040d20740e61a114103000e501c4200420f00c0b08042030400501c19034a25 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 348121582 1250 348120332 348120349
    0x4110a0602010608060601080403031428020403020a1202031908030717280917090a12150b01110f0d1209030912081204050601080c0609060a0f090504020d0f0b 70
    0x82d201c2c80103210746d550341c900454000001500c282c06060703481030110041c8022100d41880307105030a40318400c6402030044402d000001d508055641031040c40140010307030b601c00c07000e4102c3c1e10780706414001c00003500010b41094040a911281c4207461080a0100810a03010b580304402c5603c603211550400c1c034200c85100011180d21200d101494001c0700700202c00070030480707044140701d00081e00005c156200b00301d14110440050b200d103404540100c41740741c00c0020002070040c41400b4600c0740b259503150300743d040d02105508811501e81c003004405074440c404500da841c85501c21580d4220180513015121010300d0f0007080003a01d4210342c4100d0440074051030000c3c65041e91844601031404451500401c10800304a5802d0301c20441091000c0c880c2c1f1044d8019805000501140d5241c8505145441c08680c01e29010b184180302078101591031800752080b0381c80e1418030810341325038000c040342c0312800c9422041e4098030124034807122840540c4002c40701c401403d802c2001890310000c04c035610 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 348122832 1250 348121582 348121589
    0x3110616022a1210110c0d05070507120f081603031b05070f050705041d0105010909030c080901021509010f0b0f090c0f0403060c110d03091518060504110a06020106 72
    0x40c0141040711140c10440c1002464030550f0341651038940e0b10320f80340003c2d1034a40900d01c64091000c520800e00340d4090103608500343c2c41e407c03d01d180c414a5950385444208511640c5c10820500c2000340030302604e043c2d0711342c01c640c0c05400e003903981040001d1400c60b103040d07540c190002490451604640407600c420101d2030416500c0b80383c20462140d5800075a07181c407401c02c0302c03240683e54000034292558054400c071408528807a0307088403401e0a40a084813016030003461100e0400c1d41002c0443c0d0805051001141c0012500c2d648500b44401030f4900340e0403200000c01000350320700b00082c1c03100651100c40b01030aa84801d010248042c1c0401002c90004180c1d90790049224011404802029000f4040c03107070101d000070300305607030381d154141100c0c8618040c20200f803c148450300c1980080c031105104074841d0504100c81190350b2500a5546840c86c2c0010203140d071b54800d0401e42c80d036040c03895003280e40004240440d240900c0c02283c01442d4144240c0034182172540440d04a0041c0100b0054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 348124082 1250 348122832 348122893
    0xb0406030506060d0201110f06040b09060106210207151d010b030d181208040f080a0507030b060f0915040c080702031909030b040c0e0604020c03090d0311061602 71
    0x103a480740d0f4100710b54a58101c80480c107210380544e89009004042c80048650072200026001c03034034050900c0403100000400041e03c03500410014882c441d00329190074420010040050048403420694000030301c00e51074040e00307400e4012548008001c8581242210300e500c0c06861803030079410000213003621040018036078140c07c02c000010340e040c80b504121440c66850141c9a0b82c0c580d4a040e41e0000420384031041c0d410040008052003507020031a03114004000048c001d011a6030b640d220903454101030b000c02490040c80310081145603803a07845010807160004c10011180c10701034401010610b030340b80d009004a041846110005025460451085101d600903500d00913812600c8014444544040024001080b4012011405c10354001e8851481034401d40c424a003444420407501c100205001e10460040280c00102000842030362006881692180e1041c4000d140c02e036841e0650f003842c02c00c5849500e0421002d8000c0110000c0f032410140c003a40c00702124005000a11076010106141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 348125332 1250 348124082 348124093
    0x30402061c1b1404051c0f030c02010e0a050d0f0c08010609020c07050d08030a09020102010f020d0b040e070f0b030a060812031b0918250c020a08010903081b09040513060b04060305 79
    0x3c1d007045001e0b007022100c507016509111b07078a581d94802960b4012010303000274103007400e880115600302d100b0204001c070442c1c03942c4a41d45030a002400007114124010b200400224140c4200920220342c1c0d0042c0200200038040242c03210f08142c021b41041c440c0c2410b521880e0000501410000d07454004140c1150314146940e48604a81010f880c1c0074108030704641da0707071603052407800282c400360a00c101901c00100c0e81c0b0524004010594607411600390b510740215004204d104440501d0100320748402022540f255281003d2200405550b030280c283c5000f03089940140700080310040d4801c00007010701803404080c0a084007141e00a20790803581104503c105060701041d070851090b4008241e241000382003401c411122020500e02e00d402c00410f8020342c0342801c5240800111001d4043c60f070007080000844d840043ca020406000b440f4400400112941e41e00c80c980100c3c1d851a0713002d4001e10690070505204200214a964181d039030a20f0035050440516050003070b04100c0f9045002050b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 348126582 1250 348125332 348125339
    0x10b0a0e010507030e19081c1e2d08090f0a061116050c01020f150a0b0a0b0406090501110d090603020a050d05090607020f070317030402061c1b1404 65
    0x1580c5501c458415000d00020300d0f44c040c0203503030b40d202c0c5481b038000444036a807101e4503003003049103072030780c0d6040800030b030b16003107546042e1940d001d508501c0380602111107603001c0140a00130b9800a04041800142c01c020000c1d50a1860380071000080750380440e91025900c1d03481a441940f0b96041070702540598014816a07404542c651b0085104850080b4031540382401c070701050310403036601044c221010340080c02d1041456805000b013041122215001d0301c1c04400211040d4400400203003100891070b500c04080b1499100c018416026140101640d640c4a440c0c9501a24001d054401d940c00a0082511085401008145512030b10950f45a41c5d0b4150300b000740a40103900803010711030400c201030042d44038a510602540340503200410250640d4104070350001d06085084580c0243c80d48590020800900003c0140001c0c400395040c61340c90740c88501c0000d401c0c1c40f07001c1c848441c01d400300b034150300c03e95820fa10124007055441c1191040504001c2d05642e40108040c03a00c0f0320410600c42003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 348127832 1250 348126582 348126587
    0x50d020d14040f05010515091906081501030c0b0702032109100c060b0a0509151f0810061e051308030403030909110909010b0c07081b09010b0a0e01 65
    0x410310395240c00d0010035103041c00c1c400310118010440d070590780082e280c1c40e01014050284501c6410081d110381c69080350040801040d0018409000706508181215401c0582d91a580c40400540452400e90341d13844402e912002c0e40b61420300040c3c550807054400003899181e5182250360050f809070151403030342c4414115881c00074070a07058550900d0104410b1289a85200c010b000d100c0e41c0c1e0325200c01c1c020071420100b0841e43c00600d020f003d00440c202c03d018680c1e03405522940010000703142d041018132000480c20410040c442451060700850030001c40c60303001141f0724030802c40c0c00c08181241d50740c0c120442d24040343c0da508014044a01d03044803079551149000b41458a044080c8907142c56076220f10601d184e2003030380168002920400c080c0300359007443c000d4442c11000110004c0c04e241c02c01b00003c3d030300c10061084201c9102c001410803c031520501c40c40b8010b060407400d9502929007000004145011600010b108080610001c00e122800c1d00544070f400015035900440d8a1041c0010b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 348129082 1250 348127832 348127837
    0xc0e06010804020f190b0307030c02010b060a0203120a180807020909121b07080a0804050310090c09180507180e07230d08032410021b06070609050c0f0d03050d02 71
    0x501746040000001180204203038009600405040e07800140c0a21807940c001d00715024016181d02c0b540e800c210580b010b540c004160b0703000140b5400952420340340c2d00c5c1da650081c4000c5401c843e00200104031882400105809060500c0c02554071842d40c3c0d95460300740343ca0b00401c91005078200310620140da50b40624000740662111100d08550240381c44a5503540303004c119903c21140c4280000b0f0034000c1c1e0034140109601c40d51944000c4c400c6000d41d50310000c0c2e070119030040c100140d40e2108821032075481d031403195003e9500807040e2000c2c80d8850840f5240b0401e4907101c0b40d503860071302d1340041d0308002c0041d6000c00c0f501320540c2c4195842014410080c01650603c0c00c6500008c5800840d000c900c002c4021030203204680002030500380440b02d2216030042140103588954800038010281e6a00841c09031400d400b244400910541180c001500601a410024290310700d491070040810000003203070900b007102104c85c000b10010070020441c4900c5041070040004100b4480300c00d10100c40d402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 348130332 1250 348129082 348129109
    0xa090e07030b040c0501110609031c0f1a03210409020d0b060301060e1f08060112110c030301140303040b041202130e21190e03100501030c0e06010804020f 68
    0xc0d40e96032592500d40188445041d0b500b0b643d24002d40c00c08004941c1c00503941c602c062841c83c0545000e02d044098141c49000741800c40e215550000100309014080e9406a140e40c680c6900811150f005440208860014400390724020b101d028400c0c040000592110280105044c00c401d18090818040c43c001c0d400040c143c030050782c0c450504003800d03650640994040d00180c7d40e0a2030b401020400c00050307400e510004030031255015590702900da8010119903202c0c10a00709102800c00703190602c002406007844542c0140c034045540580d2030804002181204c040104140c500a0310000b010784034070462252030b600d035004001c06c01c901504140181030303407800100380c1d4900f29507400030b000a4900031001104950041040c40d020340341a0f1707001186030b07110441d41e14100060b01e0086104280e107040d032001401024000000c159504002151400400758402d0080d560f40f8a80740c40c11000600032003140d07126040000da219441400f21030311898000700b00c04480b40c22034003400080950b144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 348131582 1250 348130332 348130361
    0x602070c09090b0a1109130c020c031e010b0a051c0309091401090c180618080106060513061d0405040501021b060a0e1902041e050109140c03060a09 65
    0x500010760990350740b14100015000303844100d41e5241807401c100c02c07188806200411050144508007060705e808200e040c08485c0c2d0140068520b403d00e40507450705a80041e05541407041c0035070826000710003146550500131400c0244100c8856608001d2b180a07540129900301041003038210b22a03000c0c10f509451603000303040110616494281400030b888200c12003000040103040100101760b0705204410207013900b4504105902c070846140f01c4003003075602c02c14003041200c000300d66003001000c0c0d0a00007424564000c200f0b0ba565004082d00d80c1e000114032020380d002d8401c00089041c0101038119040d40d9801c10301d948826050204001054041d04c00d80ea11342d405c0c4024007488000f8440c0d441052890801040d451400c41c1440341580c02d01411207515030000340004541d0b038941401c07940426811100415180895008003641420011071040001e041000016002c805036201041507a90b24451411984e01d61000280c603110643d0b4890b04014290020825003005500c03007015000c070340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 348132832 1250 348131582 348131603
    0x6040810111905120c0c060406050a110c0a050c0d0c1a07081215030d1209030302070209041514090a030c030201151403060702060408071101091d0406200403060207 72
    0x9101020a4038480c078002c03404100009210450f804211080b41e030b02c10104551716140c500008440d58503a040a00004c24250702c50f00030581000807a0864140c40b04400040c60b2207034122914641d46a11400c0c0943ea0790040f02c0d9443c059003005442151641c0c0c01180452a603440c02c21095042c41e200030094285d00024058100012428002001a40c696162901040c10420700681a410568112074400c0e40040910300b04107400455900d020080030760300040346a403d00f400d80c044d03c107000e0000c0d485181c0f40204010450841200200c000300014200107911301840c0308036101d581a01c10908590014402100080c450030104551500c248004100301d4004c103030341a04001190400040500c4809048895040801c00c05038008040c8c8001c0400c5d00f0640c542040910901e00003400d8542030400e00d01081c0d000348010b400500d50902e40380d45203041c4415038650588140d5007111506d041c8000100d0540300a0308074031000310400743e0145001e15594580009510151041b1240702a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 348134082 1250 348132832 348132847
    0x90c190504090e210a090b0f070c1503050a15150c0503031014150f07050c0a09090303180209010b0d0b040f061802030403140d021e0c0c0604081011 65
    0x40e4020a4a044503680080088440414600c21244c08510714280c03402c1c03007801030345d41c0349500284480481ea1552407072a91040c2944440d01c0d140f14001015200640c008000540f80c3c0410401700c20000d070980e010007654a031182d22030141d540306020b44001d43e14032071092006451107041c40e0940340c5541440d4880a02c95503801d07041d80c2003291700da0130900c850b107330070001d040c902450062055400c40b80c0c00140c4140c401a40c140340204e080d040a090404121503042000402841451940040924010740c2d6910400f0b8060400c66100318000ba040071110500640c20350903100c8030641c000c20485544e801d00c0e254421035044180030556190b2641940382e002d4803288038100d00d84225510100c1d03903600b4240c4000b080922090031300001c41c8100108004654807003007455214a414450703682c0c0b543da4a0100e000381c0140c0402442d8045040144030650341c2c0720006008030410b42085c1c400041c030446c10030940b400796100310741c90364201a15085100c0c04690260044031200c0b05268100b43c403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 348135332 1250 348134082 348134099
    0x6030c0a0602010b0a1d0a02070317090a110d0309271e0e15150a030204230601030603020d1101090b030a021804050415050702032203060605090c190504 67
    0x15a21010240c0d55942d1405800d045c05044403024041e0208a840b03001c800800010300f41d00002c001c04a00da60210b072a400b0144030703400c080b48000d00d6401d5031003141072200303542d07490741150a0704849002d5010421a2a82009103034150119059100c240e184c0f8905502107184241400c001030700100c1e000c0e0407000d0704005208040c602000e281200149a0200440c0c90440310a01044007080d80700e00d400140e192050030b0910350152a0b0061644600000e02c0402c4105500c0d410080d03120341818034802002c0f00b001c542c14107100d06910111282c1c2c403490300640840d403107030101a401c450401ca81d100400c030705800d00504108103140050036203a580020783c00380c0c1c10644012119540009841419031303c7d441c2c042d100c0700d40460b401c0215081a40d9040c21154034000c1d0980c84a4071703100060349441c0280250742400c040008203c0f07998081001000d01140d6900045540c40c0c074200c0c011a803400c0001c2070790700c94014180c0d01c6282081e100c04401034035039007c410300c0c00c01c103003040040b4100c007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 348136582 1250 348135332 348135349
    0x3081927031401181101091703091008130f1502160b0a062d1e050a08012016080a0e031504050303011e05061b300306030c 54
    0x411410603040203508500d0010210407a00b5103a01c80b41e814000c190064107425200e0a41850707001c0d040001c0d00c00c01c0c13030042c1e50503c6076030300466801c02079900034a180301000c00103040300101141d900c0545480d41c0c60503142d00800f0350348140907801d55078411000410a844c6200d426001d4518101c50712420300102e4243d84c4403c0c0b0881420340c01c002c1500810a070408156000b03200900180480b0782490081c109481410881c1b102c0d001507800499460420322210b00c02409000c014101d1246c0020039210240160307120725030042010240004030701ea010300c05c80811000e080030340c010300b1002c0300c181c2c10140c00220076600050108030b40e030400a6494070081c031040d00d0720380f500001c90003410708050518019002000c064900c8004200004001004482c1500e074001010303013860341010144460303101907070171203a0418000600d140740c5c00104d0000300e20080c0a8003c07204801c0c140651b03007130517802d80464962410510741d225072094171140040c541c058000340c02c507240380354074000003901003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 348137832 1250 348136582 348136637
    0x309050f010c1202120705091206041b06140d020f042706091a01030515090c0c0c0102190602030606120a09020a060219020d03110d080f10030819 64
    0x140c1d03650900000d52900404004040d9208a07411405d040c003500345502c08000080c00c07103080240010306509181d4034002400c45010b040002c031001841c0515200d405800c00002c019890456000c001409a100c0c80c5201281180c602da84c90801f28410138100c0a03400440d0741041070101848081882c0b0f030304450300c50660204014003c140003034002060100c1d8455004610401d0070080d8100342d864040000044e100801c4c600001c03031355107000b1800b1740b0f4a075036001c9030b502103c1482805604403801000c3c09542c80c501080e210025030410041e6500c07001c440303034200c8890303100c000341001c12644c4d03010b5940408050070f80c0389082d4184454010019040701e51800d0a940d0388003840550a221600001600b4140001c103925000590205040004000000c3c0300d903001c13851080c10140300e5550400c1140020f0216600700780d1141d0003810409044507445510340010000030821050501e04c81d040380d0304801e03454648204181610b610880e40c4124000703010800f0f10940955407401c25250700b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 348139082 1250 348137832 348137863
    0x603050c0f030a020d060e0d020706030c0e03150405010f02040303120b0d03090e1f06020d030b030303060f12010f0504030804140d120c090503070b07020405010e060609010c060e0303160e0301141303030905 90
    0x18282410403303021250502d402604001024012540503200020b980203220a0701d4280866903460340703070240c00341403204141503800d4000f060002c01c0541103485250300c2d404501050140311180010b0020444183c0400ba00007403074810304100c4110700700b40da2a004020100b069100c00041c042020781d00140340e0240380141d000f00241d4042540c14440c1610600048019620b0750801c50300103000c204040850030712a4040402a9809030403d50010251050412080c421440c01c0d0401901400c0200d070103070707440000788030148802000070495550203110b5846421100c00100840001000d00d03100b200d00b0300c008594003181950b0304100d202c0c010100320a00351760340c64052061005958040c1e00c40d00030302c00400113000341640e402d07064600c050301c203103845031f000800741c2401009010700a404610071f010000a202011100b10f02459005130700d0744074140c25504140505007280c8401001049904400000c500d044240d00001c00407a4082d150106010b1036070b481e100e0410000c00140240d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 348140332 1250 348139082 348139093
    0x31101060605040314010b01050910091d0610050309030a0503060f0a08030309160513200325020a03080403031e02121503150f0705070b07030603050c0f030a020d060e0d02 75
    0x4229117007901d0700c100f00040380207028010551001800342d00400b034215101d40100c640d082d80540c412600c440c0107021701981150712030101081010381400a864082c09031180c1001c03200034500a1003101d01031403c4800861800146050480e025000500030a40c4000300c1c981400c82565101710304406400e100300596500c2c02e140c40181c1c130b0700c0b80020b01c59a900b0400f1000300225940c0d41d0040c1d8035256400e07000b00e0100788041c0c900d8046052031003284c50310007011082c00420703a03080d0240400340e1150145407008541a080c2681d03102e50041005001401d0140090000ba110384c01c0380d5003410548582030002c0919180e0007040c0d8104116103e0605072560412241c915440d00700e07250760506402408841030004400e40f0704020041c0039a2501d006500413800b020720500c01c41e940d140d0040060710480c141004028080c2101d444141c8041c828200d441c0010f29002040e8004510001d0061000c0800343d401c1c800f1011120ba0241c0301c46a881d82d01c840c1098091101c1182080075501410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 348141582 1250 348140332 348140339
    0xd021b060105040b06040510031b0201020910030218101e0e0901060801060504030b15060a02010e10020c0703030804060e16060809010204031a1b0f07030305090a020306011203110106060504 83
    0xd140540507480350348198140143c980075500c80c4e2080310240c80b01901e0f401d10b06442900240c0141440f15070751382004a01200d0002104c0c4d040d4080d001c40c00c011520080c4584040f0000c400f40e01828070014105250542c012016180050590202c1a0541070004044200d1103030400c207124001944400300300700007020302048c07900c100101c0c0035103c3c80c201000d095041100c014140c3c015800010200029000030a9291441030452001d076280100403540d5424500c000a002c1c00b81ca00c51031600c0c0c402c1c0a820400441e86e030090394510b81c80c00c80209034040c0785803000c03545100041c2003030340c040b607840714140072005082c020000104003501000c03d2442c034081c0001c100d680014902c0314136034811b0109000041d40080304480c244000d140142240c0c5403044003030050b81980582514000000401e00d0307500140c04058050b45029440400103a940c48140076125002404000d40c9500034200500c0180d078020441c00c082802842c0405a0303084200419085400a0b00400040360b0089801c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 348142832 1250 348141582 348141637
    0x11101061811030c1902010912120f0b03251a0309100203090709050c0c0d020d1808190c0b04080c2706130207050102030c0d0c0c050714060d02 63
    0x21810b640003040842c9185070012494425014900e03007100401021701c00d1010b010320035086018a035401c100e2002c6815004c0202804541c8070408484070f80d41412000042e0714114070070304d0340100010700507112100e40d01c01500c2d880340d18410f0588085103102804606111b001c0101c0291050342c002d081d550341403480c215450201d100c9100c441640c01001004002407001c035141e022511400c2001c00c440e15092200d2415007e00c229004007485110400ea800a0703000580080c40d007481e40b00c5410fa8072803650340300b00700003981c0100040760b80114814048401c00184c841010b40c000c134031400c00640c40b20b6603401513a0190707000321616441021900c0301454480c0f64055401c903808080f040440308244100502c40303005060f94401c0d041503028030074050f065011580c0341170b4820002c5640c1d01e08000c1c0c3d08060341288401c844080d26004c2580741c058043d40b0203484007900500245495450a43d10f11102405030aa1a801030130901140c41803c14a0020380000303001c00d00b520440d0842c52071070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 348144082 1250 348142832 348142841
    0x5070509010b1e1e0309011d0a0c0314070b041401021009050a0b09030c07030302070821030c030603070f0801050612030a17090a120203032e140111010618 68
    0x70ba40c120b0307002c03c4807045880419030008501546001666111503550280080d6014403400d40c0ca940d200000822400071010f500c01d04130750003030303000050503d40880d10f02ca66034a44070341c00600e220f20350304007480030622891081031110000c6044030a100e484445003051504550311081d4490020b280d849d42c01c0d0703014850340610a10481003004200401d41f9025a102207803c8050301c802d83c19004900b110034140304444d0403c00c10401c03034175000c1d620714000395a02e200384140c1e28a40140c40f0360881c89030810a0305041c0300041e027000390942e10744061000f195032000d031249501d4451200e00190724146070f0340c22001420303030800000da01e1520380c00f03011803416083c2000c00190410040e03511f0594212504810b0481c121210b80095500d0f0480301d0b1800382c515002510074998104440011035000000718403400302485d80080410040d0010404105035620400e101c4104520a200c2c51a01c2d2100760741c44441450411240ba6826034100e007182d00c0c035001900880941d2201058109240c000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 348145332 1250 348144082 348144089
    0x40507032f0607151806110c07050909151302041e1a10031a04151502070807061101021308060702010b03150406200307030207030e0405060d060c05040e040507050901 73
    0x7001483c01030241d44000c0102813098580808035a81c0c5100e4603a040f0007200407030180da10030801c0040281d211280321654220840e0040d0134400d045000c540e50078400030341806000c819008004544000622540700380c4018902c003d440d10203400d4801503620350140c840c0301c01c0c0a8098101502040031030300240c1d0001e507459561103184500170605500e5011030820003010b0391400096000025a1303105058218040d42e580c058240001c480c680e40415560034121200c4590030071048010003c281d07120b042c41d01c11156140c1005030300b049410b0081041c03180301c5003040b0006103094603e03101c00c200002c590b04012050b921800801c10841c1c0c09101741a0601c07030843c01001e040100000ca01000c280041c001041e0680b1012502c000f501440c212060007110992020b4a0b46080340000700290805503003a4001141289407080b17a0910344907150181501811002d48100c20f920340302e000c0c2c4034215002040003003c00000841041c1000d030759004500ca94042e00c801c600c0c040400420340c5040c1c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 348146582 1250 348145332 348145339
    0x10501021911131a0f01170f0411040c02070806090304080c131d010b090f0606090f190b0910020313061103070602030117061518040507032f 62
    0x42034021440301c0d2041282405a022440c1500200c003400800c1d0b200c44400d0710b160005081104052507454503038000c091011054601c07035800b0001c84011511203c1c6820042c02440042021940703004000e41c0303081d80103028294032803682c03110344041800c440c2a044c1c5100142c0003103006110a100611201c1e0b04803003550300035030170541444200c0c6c0e11066120810b5100700044254040303200010742142d0b0014400d2009400c00340f10b20000180600840c0c00d0305441001c104000507401c60403050a180510000b44c10182860007900500503031111740310900d40c0c0309051209032402011200b034640058035446504a0302c4000340c1c003d00180e00e60042d69002590402d111242c000d0441c801d80c481124058900360040d90502ca005a065200301e00300a403055000200124584404103500e03020040f09104403402030340e0340b0301c45001c2090b0440c005a40000c0142d244003501c1546019903030032074081d000341c400301a913030f50710b80d40400420340301140c42d01c0c3c001c91034459180040e51260b01c03016082c1c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 348147832 1250 348146582 348146593
    0xa05030403022107260d051017060a0e0d0f0e0d0605070c0b0c04050f060706020d0c03061401020f06010b130509090a120905130906150308090a050d0b0a05130f0b060901050102 77
    0x2007000c6849001710104080c6c4240c2da0000600301c0000c42032444024002414201440c03081082c840e9115a0101d4121450303604000705450010070001c9c0700c2041c52100c0e501c022062080700e4048030210382640c0360940c0720707456040032004142c00b40300d01801082152100c003824040380c5415502200000c08000d1080c0040c4010400b030303120190910290f5008480c540da82c0d401501d0408001c1c042c2500752081140340540301021a41c0550101040d0b81404000940b801c0c0e116004981d2030950302c40300341c1d6607000400100444880383e0007401100040c1403c0c0c204858940000c1140354002b00e881c40819804810704400303000201c441401c001e1001d2400740410750400c0c4c00305035030f08800304004c000b45c0d41d50320791242030124503403007a941d0940c2c0410165015683e4289880150040e140712403160300ea00c200020f00340381001c145182e13142d1000c0c05041d20755944030014000c10006082d00b21040300031108600094030840c0d105407840c480d4812414609101d000d000c00c01005802c401d0656215 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 348149082 1250 348147832 348147893
    0x17010f06110a050d021b01140706020f0c0304080705011e0905330a1707020703031d10081009020913020711030706050c01051503030d0515120715050307050a05030403022107 76
    0xe5400c994a0503002b40001d84d40b090310700c800c08654440d07c12406460b00000c10085890312000ca400c1085401c00da9400d498180c49940745d90102221004034400300c2e03a000070402c03007130412603c0c021091a030303010101881e181e03001c144802c0b0749081c0042340c0360000000381c020031141c01141c032a4980c00d541d03400080910f8003c40c065500c201c00c1c00080c0500903000e20001d22900241c0c0c0003420040090039040e10407000c003001400c4501c007901c0c20306807400000741c049096034440c406d40b1203019004100501703408194250400950084000351a40c8940da0740d004120344003006003100500b0319079902da5503413083d80e2841d8210742e0702520355000c04144181c101c5150741c2c000107658115607101000a8540c480b0000d060288504100540d0001c1402c3e1307042c0820000815298101d80265031101800c10802108403100d00c000c82e40100446c03c2400410b0070740d849013014691207840380c01190080b082c408280c0b805c074200d0303003040c100c40c0c04c00044071001c1144c1503080240ca6040104000e079080311 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 348150332 1250 348149082 348149117
    0xc010203030121080a0e032a01120e0105010806010312050f09010e040f0c02030a0201060e0708040b07090b19020f0106030c0b090112050a0c17010f06110a050d021b01 73
    0xc1841809140201d294803600300c44401441c0c2d08940c2c4c1d2011040f680c0395201c00001e440e4214060101f4424050b04000c0314103002c424422400e0101000d2452100c60400d50040da210700003890600b02c400d643d0043c0c185410341c00d22510340a82485401000150301d5031504400011a408100742000802c0c4194002d4502e45004c0e900c21840034205011254039000100d03000b000301580d000c0324141401c245120168010008115180b4544c0c0280200b03500d40d50600070b5400140e0700c0c100087c0c0000b0000e00400d0304440c01d0758102c010303480c3c010301050390b410701031a041d0400c040e10307000d9000341d0000c440c0780c1d40c0401c005080c8000d5030f00280001491600c8001e004c8200e40b0400740d41c1d40c400980c00b03900703a2182c204045102d4400d41e0422040c200601032a0050000c0c500c000c01040540f1030510b209402ca0768800c4c101c0d0308080683d030740c42c0e05260007183e0303554480b48550039921a0301254400500300b8880703009110402d82c02000325201010111640d41c40c04000720b4188204055140d04806 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 348151582 1250 348150332 348150337
    0x5030405060901020a02090f0109110c10110409050709052805011d0904081809130f0c1512060b0a020304031209050d05010203011442070c15020c010203 67
    0x200201d030368076240c02801d80180e040042450340250303c50422410000714801100d81181624503a400030066441009149540e510651070203403850740c803501d00d03604202c0b00390700603000c0e080840c0f456a04180d52559a82c1c15210203030b85000220301030150a00c12810b005044201509040f5007148042441501c01c1f00d00da03016008050400c209007505940c8000c00c07028000d05a400501401080d141c1400c11040907004103000b411184001d0380c0124291800841050042c89280301e41010301140d60f83d00e9007400d400120440d0415a80c0170006850140d0850400b805d102a0300d41e003460f198094185002c035000c641145c030a50105014004001d6400001e580030b49030f0100b03075403100d900c0540c0306651603407950f8407141e40f0030041020001084011b4014504884c80c1014500040e40c400e07041010380b0001e250b04034102c4c1c941c1c85d0220b003541061642c075420310118110b000c810540780c044452141d84000c0b800d0350060960401040003158220702042800d041748050400c1c072043c040000c2d00ca1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 348152832 1250 348151582 348151589
    0x10e09041a07110706080612031e0d060b03090102030604060801051603090503040b371d0f040c0f021612080a0212071110110304090f14040b0906070507050304 70
    0x7601604002201680581000d01156101e0021203112943d6901e0081c50304c8401c880c0c0e0750040190040d044070051303000080d51002d50710b03a204003540e98600030560403682c08c503400980400f030320f6002c0007079001c00620095001e031403244000340c0d9030300c2d10401744000d4510700d40c04241181c1c500b000b000510300040380407240e8100c0510b03021a107040c003400c142d844d500998000603446480042d140c0c1904070803c111074800c5803600d159140c01c50745011501c80400c02c024000c00402e00a010f47c4074030101405070010200d0000b0280072000b0601804034040750340c2081c903680441c1010066143e101e40400c00c08490411a04500144070f040000000080030105030040448e180800c10790012402801244a686040340311243c4685290802e02e4011700f8441815014180801202c40e5807071141a41102c1c886180c0e0043d407401d482e00a01c0e9008007130781214060429500d1800b0940c401c000156540030314002c94800700d45041c11701446042500103420141400300401c20480010703030200070780f000c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 348154082 1250 348152832 348152873
    0x40b030f1905010f1401060f1d040b01030e15091009051209032107061823010b040f0b01030c05070b01050f0d020402070515010f08060105131808040302010e0904 71
    0x101800c2c90b281c2e0150070f0851090315254282800c034050200c07010344550407294680e640840104001e0419554100148102030310f6176040d950301400b5061982084002140c10325000030b1100d51403a8541c2442c00300d690710b84030640c1800910000107801c06c109a00c190b0881030800030380d4444d94880360f0f030f103800d06ca80c85c088660200c0e0f8403030566010b00c4a810902140c0702051074a40c4e242c4458042c42c0c0c0400c50403141240b0b00003806114810f503036031924030f181e40311750250034460455644251301086030088803c2503490b55204d40180d212801248032011480f14080340e050340220016098070030141c44501044000c2c82590f011803004500c160440b60143c4582c0d85401c106008102c07081c4c0740c48800380d00640001000d0082000004038640345000d440404070950b604c6034501050021a881241034039802400140601c2ca0414000c2d403056800d1a0000303185008410352a0020549800c1900c480d003003c1420410f550b04030980100b08103089544003510300c0c00d40d07506685184400c5d040b400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 348155332 1250 348154082 348154123
    0x313080403020603090c0315090303040b1008010c030e010606052701171e07081311040219050a03240b0901110709061805220f0209070905040b030f 65
    0x24065528211005150090001a0780340790070000c250f039074088042e14602900c01c40c1400b541154002c00c1d40750103168214051440c40e02c454550400d00d44014081c01c0024011a10005070381e502445441e00e14000c1c1e450102e9450a014120b50842da003e50041d400e014003000416140c100070b540003190801800250051403400d40c0049480c1e0000b00440050b1525139801d11446525070300018007400d9068170000400d90301c8000031241c901c42940c03071035200c28001d24410000780780d0541402c41102c016000606000c200c5c180c10802e0b0030202d0018010400001c0c9850f0329a41c58000e040c440d41c00002c07440103081c4c000680d0710b010406441004806400401c020540c1c0c5e204035460401c0c22251000c8a20050b225110400241250300c245190316520200701c224080b59030180c50b118486844032202050025100e800383ca5a00300780440c2c411020b01e902c80010794807111114042c4009688984031141880248000c69500d036000a11030b0384090b0003000c4031b10b000034600f01200007103440f004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 348156582 1250 348155332 348155371
    0x301051f0c02061215120c011b020306010e01060207141c02131b0908010504050616021002030a1a03030c070311040b0303071101020d050309060112140f0f010605031203 74
    0x756a415480d5000b94028800509445441840d00825000340d24000c618440070b00e0950800880d1030074500c02e4442c0c1c0d004480641e91941c06030400300305c06644210782d1154089c039170b80044e050000c02d03000022802c9100005004207907040085d14064546942c0c0f21501e400380c01c0c00103615054442c140001d00014803111011511041e80c98007045488480070710204d9000241c1e01d044225070746500c800034011400004040300305009480c0100d030448094446611045548402c140e00c5010f04e9041d407244a90080d0b164455100640c428052000c00044e10004801d07180310b1410707811042c9101e90b20030b100d41e1490f1030011654104482e40803286e03001031104080410080c10891b00c200750316000c04107205003400313515845c800a0a400340e094550b8042e13809801d90302030105aa8400751540b00600503c14420104000e0042500a18400101d8000407110710b291904030000403026810031035030300e41110400d0007410003801c0120050204051080700700142404020200c510794903e10b0b0000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 348157832 1250 348156582 348156587
    0x7080d061a120c0c0a0c03030f0903030e060918090102180607021f03150e040506011d0c090102030f07030c1214090105130801020309160f0b070b270c040e01020301051f 74
    0x120307402042c120540c0c0003141a801c21b00002407041c402a00848d1040030110051442020003006503036064545d04500d08492091252070381064001580014405d9020107002800d104210f00c1800356500159440c0d0307045510100781301c529580c0d1f50240350288400401680d40f0f0300342154042c0c041d252124040400e42d0100c010b0100d03610340f40c00c4030a2601c00070a4604204a00c1403060b40110304131050759980b442c209680081c0700c50b002d401c10820700f002c1124011020b004040e90101441181e050548080da04002507002280450224017018444401c1084600102074003034103a0070304032311031031741c0104c1c40c80540b0900c400581000000113945e0381d1200110540006440b103c8021526403034001c2405903220813203006007443c0c0800400000354030307c001c40030f08180c46200f0102410040729603260035408034003503c1103011107841d080c3c3c08071806940070b48960390741c00d103401400782c2d0180005210494910b402c0d036070502c0e401000184803030f842c1c0c9100c0041e45400c9000b0502e09580c984800c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 348159082 1250 348157832 348157837
    0x1404050405011d010204031b0506071403040e100503010b0111060a1104030c06030c08010b0903070303050702040219030614090108190206120a06060e09160e0a05030307080d061a120c 80
    0x142c8180f0b02503484046000c0300540c084c0007661302c80c640300e10703001400a0300d482085405200380d039030064081040100140e4142c164050141140b030459003001d0301d40b020240406421507207500c0c010b0300010100658030f13090048480440081c2050340700500001d40c100d8542100900c840b00d40360305c0340348040040c4c16840c03c0310015504000302c40042511114003c0103050644081000104040d0000c40c040901d41c04440394104010010000546180c0c0d09541c0c0e6005400700313070780c469800e012150748a190042519200caa5640e00050300343e04101100051440601c0080e010303001c1c100042c4480d00f00050038031103107003039001e2608580c0c05500c002012881200c0781c00b0303822103074038003030042003012034001780d05456541d10b03500742100d02103042c446048070031a2010080c500d0784c030700d44902c9400f0700e40407080361740c025205104141d15100824a5a400010f040f200e8000c00121841d43c82d00c6846a10301034550140d0300c00f40c2c09400e9008d0307070440c010048856640c1e07000c3c402065913420305908 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 348160332 1250 348159082 348159101
    0xc0f01020c010c020c0315040b060604030218100f0f0e09011d0c130207230102040b16140106030b16030b1c17040602071e0302211006140405040501 65
    0xd40d51000551200d501070501e48982c0000b41c0300c0c2500e003e00720701e8080755604a00b08020301040303c1c0d035115200d040311114058085a0011000c00000c800341e101d200d640d80d601d100f83e1000341034a003445038035000040126446011042c94070700c001e000f4004007190b800300700c44121052042c652610940c450041c0b1480407110f1048100d00c403080b01d40000400e0340640450201ca075001c101220688850503441110002810000307030404041c0d40070b0a204642c1034088a1200050a1030340b202007201e401e601060342c065031241303013107054810070270482116242d40807108000d1080034a544d80e403488040c2c016014041280940b20071803038991083d40840c0014600901c0c1c0310694200c4481c40c070240164210684094515601e0310b5181800c4000f00d900721011940108813503850301201e14082030b00d0102502c400e1092020000c0569212030380d84402c3c1c0d408240080030880340480851a140f40603810300b00301c80c204a070401841c1d00c0781041c4216044260f5002c10a907907145030841c0100700004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 348161582 1250 348160332 348160363
    0x71b150c0b04060f090506010305060718063e100903050a0c080f1305030c010914120a060c0306170705030a03080406020909010b09210304060c081912111e0c 69
    0x4070170006019000031101d04890084060f18001c1e00d03515070840d0200c190b4840071001c000210001c10046209005442a07000707640341109421001480c07000d4564003512501942a281c01000000d1050620500d400c2c01c0319480200129081c81c0d40140842c00f507030040e0b005002980c0700741d00c02d02002004458400711001700c42503454005504803a103420060040b18000d2150340303183c01055000781004416544840b51603c503000d504020031006001c0801403a4103409200d13100300010316280603d81c6295441d89010039074078180151102c1c900000c14142c101e03580110001c0240e51000f241c0211000d40520b01030003540e03600d0134004c010380f0690081c80c1e00a03903103400000da4400e46001508200c5070403203950755414803200001c2800c400c0c450424219800c20001082124040c007030301c040040c0724040c034904180986546942e5115103200c0c4902042c0c0410301040000303003900c034601182070114011404d010284840716000c502e180320300740340c00c6000541011902800c000505080d00c202 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 348162832 1250 348161582 348161591
    0x8100306020c06010306050f060d02090c09041d0f030a09120201030b100903260409090c1a121b09010f18030f171c0203060d08071b150c0b04060f 64
    0x643c3d03811003440309071001840c08003c143c0c540b403034403141401035800410840c84100c098003003024980015201501d45c481c104032841c01c035295801050003007a0040f5558040e0580c0051190806802d200c015003244c0040040010f0150040c0f00d02081e1346c6444501c820300c9425100590007450035400607540582c1002a080c0100d40c06071114090342e100e84200f00c084106c0055a034080081d00307030181e003550000e000500140c410760344a1081a800380c030800301c1250391049103402a03000300b04591200000083c40030180103a01910640107441c070842403a0490710307a55130b24514000c03941e00504200c0300a809441c600c0c0304031400d115141054090070412030f9680f90064415405c0320040b2121001e04c3c107008210003201e802d88036004c5600192000500010086070001c0d403008050700d0b480610105d103800410303180c202400c09c0c036100d88a880b0900e031441c00130080d056000c2d406880f011017490280c6404c00e0b448002d484085911100840c0541c840b840c00310086c02c95809459542440d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 348164082 1250 348162832 348162847
    0x5130209150a090606020a08031015020f120306011d0424081203040201141b03031608060307051c26090a14010525170d0b060306030d0810030602 64
    0x80c414020456942259000780b0b180c1d40740034800a03280c6621403200907820229200012030007090044d984050b400c02094079047c0c4682e805003002c102e070450b0400591207080240c812050400000c2c00c0b084c2c0103400a4207500e80780b0002440c4044441a100094100c50300680081e00c554010210301c103d9110005c0807002803a03000304081980384a060700912690f06484400b81201707080702c2c010fa40603510308890019032140e0400682c08611003207000604240c1c2c2d00f16400c010703c080d5001d400480402203070151460300c001c005080140c601c42c8030390001c9004208e0f55a445000c94070310100c1e41c030ba081000006081c1150b450b601c02c01d0209404042c1e420722080c407841d140080c05e001c036003120000c030b180b40c03213031a5980000a0001c80c140451010030924102c103c804200070315800100c1c440d204000300310369400f4881d11029100084100010801c19120b113094001c1a003142400c0d65a98114a0280c000a56070f02603a203140f024440139001140460340c840d80120b000d59000704066658496 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 348165332 1250 348164082 348164101
    0xb070e010e0307080c19030c0e06010c080408030318030a120e0a06150801150e0a0b131509060501050c100e0f031303030f0804021003051504060909050c09060d0605130209 75
    0x407030310f4a188240110503480800014986412087c0c80d04040c0d014600750070101c0e04140500040d251905010840b004140010040b1000300060032299020315140e0034400222800019203152094998001340410864554000000504014290300c0494058864880141800a0b03003030060452410710080c00907000144941e90101c034600c2c2c0c005c22168100c14101e0b8100c1001d40100d070350009039034010403400e803c2a04141c444100040c190325183e1002300c440421142a08500c000e400e60f401c0c020046180c091294000810007820043d1516140101040d203a08090860082546d176034441d0400f6403104101a01c007130000c05045950369044900c103a100c130f40751444110006813480c800c0500091050041c5030003141e004d0318005910700050800d03006030500070615030706402d10281001182e50b803800b410005120110000480302e1003410401d00308030301b120072a4081c2d1040400d000a0b61103035250300d011541c000c000007401d40c0352440c1c52410100441c2d00a91300000310814000c1a20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 348166582 1250 348165332 348165343
    0x10f052b110c15010303091710020a031509060807030b090708010c0c05010b040b0108010303030207061b09080105150f091504050a020c01050f090709020a0905030304090c1404030b070e010e030708 86
    0x5006608640c0e0401d00b020f98900c40710000d010081c0054480841000a00440c1c0c181c1d0700036551030000d440714081c0801118040f03030000703c440e4002a403074805080d50380410301c1c20300c0f001e0445241d0512285007440c4100c1d50729030082c440104413415203000503522403030038004500609020002403000092090340100030b050b42500035102e07540381c44024810351070a84a1610300280c1a1182002a0700c1c1d51010740007900030070401d4130281e403a40c03640c0324220080102e07442c02d422a80c46825545080c560300070700f1030300300074009130303405010b0001c8011130b81d140034110790307601c0044868030465900c40e9034140d5009640c3d00e01d541c10131704040502107141c02c02d802511044811070002c00c41c44d540d590881d03032222401c6d1041c00b8280c000c00300520003504c281d00108082c45c441e04110241ea651000883d1656116038441c568042d5202c5800401d00d5218034070842080e02c02c580035007800c3c1180c0b42d8051865001d0201c10500100e0690741119900400849406100082c250340a01d036a031401c1c0d64658 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 348167832 1250 348166582 348166597
    0x3050f0a0e2d060a021c0807020f06090601030809130203011d06010f08040209070c051204060e090705040522090c050405070c080702040c05120c04060e010f052b11 72
    0x1030300703940450090280c0c40d024180000c0080349800b80c0341d1101c041480525442040200d0440c00b801d0318500703c2103029105010420300c02e40d248081c903d040c02c402400e002c3c0c18440d00c10546c100d00c01f404031440e00040c0d503a040d650012441076581e1359042c0000d0f0140103407400480c04a0002c0000900700d480c40700340b0251080b540c1e5140c241540d80c100111040c120025900000c5441c0034081005400c2141200d41d015009040102044d40682c44144c0703003e000c0d41880c4001c0000240600c0307000e901050116680b14140d80d06e04203814100005844e07030086014950281141d10780c0d04e00b43d2268140d00080c02007004008000d01c10050826110707501d10340c016980114104008a120310340708610364900d02e40c101c40c81c0d5040100c10342c2084080e1a100c01410204081232058000125514026a00400e880801180e4491502c2e8001c0c1c04400b00c1c0d82d14a040c000b105142070482e0f034101c0b0840c0d00790320710f043e1803440c080e15405a42444100002c40c5081051030b2404201c4105158002031501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 348169082 1250 348167832 348167839
    0x40f14012003030115110a140c04020d0b040f05010302010f0c080904020d020d05010605041d09030405120304060e0607080403061503080c01020c010501090b1f03180b01060806040603030207050d03050f0a0e 90
    0xd2602d0005e065540c4a100c0e168802c0681c060440c0401040003c42c0a00c04030b10224180c950704280d920002d4281d0b0003800c1511078855840c03602d0031003860184503c1d009608070050602c030b0ba62442d0006065441c1c070f41440402e1040c40ea0b451030800c5148400c554030309400170700842d180c14106030100d009401091960794043d01d00000407074031602170070590381102c003200c00c280c000070301032107031854072070030291824060380300c01d00001c1350680c0c480c54401c00c844c141c07800464543e85898030003058a40520700721130140c0c030f0400c01c0310040b4420070116010383c6d801110110b810580164a9021a1000d901c007610098010031210386942045d0028281c0814550007480503980740e07203820088402c0c2d440c0d15a4071040e4020840035070200701c2d10111382001c0b40e00700010300c01007401503a2000c2e91002070859a04100c0c2e00148607054101642c55003102041e581048058150b580c065510040382c06030724411402c040c028410548101c08517462142c1d036280c0b0b9904c44600c080003a04103180da8156a22 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 348170332 1250 348169082 348169109
    0x504060b0a03050a050c0a030b0f1503040b0f0708061e10030609061a04060c030504092406020303131407050d1a0c13060804020f031b1302040f140120030301 69
    0x24403401c9000d164052800754286600c1c7c00d503400e8054009014a00c4160b800818410000140d66a000c10501650312030b0b884090b96842c4c94074040703003100d60060517802da106451040c862055800b140c400c2e4400000d41749801c0402034244d55008601d01015115400186140b00c4500d840d410b4000c1421102139041c1400096200ca525030700c1840d000e0a41159000188402c02002c0c2c0300324040c440040c024248030789019126001d400a88000b4440e0040560403506000c9040c0c09085d0300000400051000c4d60450412400c0c00c13604207136074617003d8803024690015507800c51041c842000149002069003007890568034041c0c201824108440600f0b115140c0007814010411302250300440d00e410f007400019003081c00540e0941c0c07000e4030580c6c0200030302c5040035440e01c2c01c121681d80000c00c3d1222604000151741041807000094207880e102c036005000821900f8405500703001030300e2030289022080c15101004a803000021060654420201001c903030303255801000030b44c10383c0c001c41c44450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 348171582 1250 348170332 348170341
    0x90203060603010c05070b040602040b0d1b090302060912011805100c05160318031a0402150c0703020402070206120421080f0c03040c0f06051210210c0504060b0a0305 73
    0x14200c0d50380680e0400429410410746e030014817000c0384a94058420440103040a49a1001c2c603816004034031114840c0c0d070346d803400c0c04001c004645500d9240ba6036262820100d81158007042d603d000b4012080d014070403100401810400c2074010907541d4a50000c802108151070a09659400515110390300c90740c585984900f960f4171600c101e030248580c5040110f20b40380c1569045550070b4043d001d4407003407075945101200080f071821f68030030591503402094210b41000d004018030040640885551550100518000020080350380801c998048a0050301c4039614000b040740361081691550601c06800d0404c010080350444514662a40710151004e010702c101060740c0240301500d00b0a00441a1000100c2c102941d600035a03000344180408000c541d83e540c1541c2015910707802410100e44041592150381f280e964a16500c848525402d000562402e04078980445102c3c4400c51182031860b03074030090040802c056001000c0180c000c000301a41c900b43d9501d00c1c2c001d82c140d50000303401e210229 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 348172832 1250 348171582 348171589
    0x90203061008150a0e01140f01230f040b0301081005040818010c120201052a0304080327010c030506030303091e070f080313061b15020705100902030606 67
    0x2a4825a005004a031000d0000c0c203094690040050480080c8901d075100c0318059100c000030400140702d420945802c550514214482c030301d05900d2001d0041d81d4203020f0141c0c9aa200001740c003101022101c103903841440c0c070062681881000a4000c03084000203001030000000b00c002d6040724155800c0d240d40e07007068a480d8064602c1928003030b2210f0000d1104040c0f441085401e90f030980014100414180e1580c1da800f181c03020ba80303d003440944d5441c1e080203001354500c40c009094079103401e6200750060300c00c0b01208503404007410141c1040404000141110918583d4120a40d00003201c020b0325400802c4060203407140100b00c0d40007a051501140380d500340042628003c803c0c802c0541403000e2200d5210a40101e480d01e028041d210340c01b0b00140000480b0710345005403d12001950713a501018004a4250007207600c000200081103001640e440c00c3e0040c003481465001884610403840d42c00184064001c0034409021400b442d00f400200786c14a500403406a8402d805480040e0740306400c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 348174082 1250 348172832 348172837
    0x6010e150627100e060a09081504060506100203030a0c110f07090c0503010e0403030507050d02160b010b0c0d080403231c02040501140306030a050d0207030302070e070507060e150703090c0902 84
    0x300c0000c00d440010503d071300d14200703000e049100f1907031520740780c2a0b94464441d49806c5802c400d1a403c00b003050244810b106180c028a90300c15015619a0a030720400f0710020340e40e21000341559507055070351b6204d00809101c1c0c1c42c41555100b48204032042503a105031078a440c2e503110700c203031480c15180003401412640101c0c107403130480303140351140100c50350786480580250100030071804c2000350400540041030914809452000100c1c801802a903070b452a11b01c601e000180c00644c004201070066005045000800402850342c502c1c10f04003070384840c6130649601101d0007421803254005071072200c10340e10031009043c1d03110303241070b02d00c4402841c10044401c92146016190004103c41d03105c4007030b9020032000310340001e009000c9880c040c41c5c0b074465504101c0e0349140140140c10002c420003d141c4c1c10441e0794064944880b404100741402c044c040c10701c0c86885801000f4523102d0b402080d100c0424044030810110510343d000d814501107400400030302203c0d0f802c6909d0000c03010086541c51440c0709 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 348175332 1250 348174082 348174109
    0xd0206030906070905011805010e04140a090c05092e0b120603010b0d080d1d030304030801060807080108280c090b0a06020a200d0c0b0702040c020d0206010e150627 72
    0x1801031b410380c03c200c011102e4ac820030708441d80068455601c0c21001501d03054040c810000040300040b040120310704802c2c0b201f91a4042441420800c040c010b03c00c03240052119500390410101004004003403040b07868400780e40c4088001c800c081500b42c0182080c0d0070080c45a2408c50003046010b4040c002c1001c10070310603c014116400600101c151b4161a40c0040301100c200c01e10100c81340c840768643c62031588212404ca0014624000402c80c07150810403003508014181402000da6043c4428507503030fa000c078400012100181c0385200414441001a010f400e904100410740264582c0c10b600084c0010a0b28a8041c000341180010325034801f24a100340b03903a1001c4400d01c86088131492a0b0001811140a41d20244811800002941826a8030002c0001e10142c0b51140700c0c0d40100700455003031440312800d540101c0b94400b202c690100340f150540e80031820390401626818841588030481600d03640c1c11250000f1183e0015182e00c030501707019291100e4000c0e00c2a4001c0070700920806014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 348176582 1250 348175332 348175367
    0x50f16060318030c03030e07080307080702030d14070308040809090907060f0c03140309160303080103063b0102041203050904200a0e0f0d0303090b09060106020c0108060d020603090607090501 84
    0x521440001c1c0310f030300a10012240d1008850234541c449400c0340c2140d001c0c05003281c00d2500001c60300c046040034010034070000e0b0242400141071403034124040e0507104140c0014200b280000000b01000620b4040c3c9901c80701c003130082c6449161400c085135459a11b800751001148002500d40015071181d20002036107945a42c800401c003103448100e04036900b01034042c0041c1d0045005c03141c00e0b8007801251800440c02035a41034219451400c015040f140c0c82400d0380301d24540d58880c090600c505071584235494055018404868040703112a50080c000e5800a2404000b01d6004005055000010b05030301d0f0001c0780d00f00030507c2c080b003400095400d0104070fa8024142405a01600c038040d08004440010182a45c12120510000114410038451088011950b114400e0042c4030540141c2940282d449000742419414080301950f41c040c101e14480c1004020400204540c4913581d421002507400f810150f00d90800100d22034a07044101e80b030070002550a14002640c0d0321400201c0c0d18020047e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 348177832 1250 348176582 348176597
    0x30115110303060a0e0408070f031e020a0209060d0609170d0b030c09060d050a05060703020a18051e03030903030d020705060a0501030803011701020c060c0c0c0303090a0e04050f1606031803 83
    0x85c0c2c2041e0440050064031548014000c0f4400b09003054480c82500c0c0c0310f5030700d0707540c0e0b42d1044031100c6e8007241c10a42c4408552000c9402d40050719241080344d000a4219290f61007403502740b030486c2c080c00119900500d04000d156280c07040100c0078000c0d1a541d000d90806200100c240350602d544c800101540329031052511000c102941000d80c020580180030b1001c0d1940c80b034068560901c2d00e0000e1b40c0c502c1c00a5400240c504561b40c2c00b0054080540b001d0040b000100d1502000514011403881c610000f01d44098009042d540c0c100101c0d03000002c094107494445641c1d0715888001d400c40141070301c85d0300a17900040d56134411807098605980d840f100190842e401c2c0400d1465140d0f0452082c105907508004c60740a9101c20402181328241050603160b9805910310501c1c02c018460315003d000b6801400506c0700b550311900000155006007400c1c0034a95224141286419094103c000c3c136030041c684000e07082a80a502c4005030303a02501d050280b45031000780f01c80c4503200680e010700026400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 348179082 1250 348177832 348177839
    0x130e0d08090c01030b1f020a02151c0513050703080a08010f0806040f0309080f0606030115180f02040b12100e061c1103070611010e0705010918060b030115110303060a 73
    0x1a5104010141014164141303202c4854000c00743c0306d440034035010160707000883e61070441c0b502c601000551030610300c130380c0c0c20540701002600303003d0342c107003120841d5a4850000845c1c02010b1310200c400c8a40107801c40301c5582d50390400d60050750144100c84000744844001084491201c240710045651400050000b951a52980c04040c0c0c00b091084007040700030600041c03403140811441b50750f0980c030006041d59003003060030942180c0100d5004601e01c545001c04010003080b05401107410a108000840c2c54200e80c1040d600a01c59038010b404010408030307401d040500e00041e054800d0103882503248605807203542494403180111039031b40d030042d0000c1b220326400304210318040584d482044031001e88072007803000900705000c0350020000145090307901d02000d4424041c0d009081101d201408440e03041c4000207101010034018007a88807100c80c20741c1c50030992139000c10b0040a03c60080fa442e56105d08040c14503000a000860009094046104c2a0440802242e020b40b000500c2440716614 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 348180332 1250 348179082 348179087
    0xe07140409020a031b17070327020d170406030b040504120507060b030316020f09070f11030c06040f0203060f010f140619030518030703050301061d130e0d08090c01 72
    0xc0c040030010103450724400e04203050642100c03e0080f48507140c0358440c1180c9031b092440c01600030580c0341050300340408542c14040401c15010060100c20703e2584500141c0045240c076070103608001c2841c2908075140b00d0000c00103001e4002e40720255000d0103124072000130041500d00964001c1d001c0107940c1e0b1070800c0036009000900b0824455000400e00c004258002070560300042c58100da00c28003000e44d001140b514000140c0b840c1e00440302d00d041801d18102c001c04050703022000c2c030140200702c200c4070900303e810400d8813004400c0341c0484e02d40d80352928085021007030702141240603205110114100784c2c0f40180e61070585620542c0e0007001d0b45010740b403250f200d4050300d286803c401d04100c4287c03400d03410400c024140d62940c4000c6a9401d00d1000d018000316213075103039043c0e90002c0c03080c3c0b000642e012045074111443c40c940440d00e40c0f040c42e203494803d001041c92583c0a4820313140e007029583c05400078901c004201e015140d1404620b074050f900c0c040225521032961704034042145c0b00d0760 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 348181582 1250 348180332 348180337
    0x5070210090204290109090e0309010305130b010b070c0605090f060904020708120402090906040b0a0b150c0106091802030c09070c1505010e221202030c12040e0714040902 75
    0x340024000b140400e11041e0740004c42020144802842209819100311035030045192002440040c4040065120080c038180d1a8000c901c02141056258004111500025058140d502d83c00c90921203455940d44141e0200381d010b01c004070340000c0104000560726000c0d0082e1090000058a005102d085001c1040070a620000c4c0c0780c0c1d8456030910104000c101031402800100419450500107400d043c010046660303401400c1c032011f640080200400960180001500500b015601142180889001501c110038840503000150b0000c60441e210080541201c800c07203585140070440103a60444612038065600c5000e0b405501a102c03490940c2044000d490388901b980c50a5289a106555040e98002c00d1041070700405440d8001440741e82d50082900d6000340301d0a40700c0c1e030310310040d868011042c1440705c40507040c0c41414007411003aa0080c0212407407148500140d41611440020000d0545c11900585006121031000105181d02540c0804041d840294003141020300d046020701c040e6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 348182832 1250 348181582 348181601
    0xe120c0d080c120c100b030a080d09080705060a050109060f0303180b0a1d0d020d060905100c02070311090603070b2203060b091506030105011d030f0607020607020105070210 76
    0x492040080c01020902400800d6010700d01c1c0b0305983d40e9100203810907291020f204050f031030030303071401b00c0c07400c078550780000d07102c21496001640c2c5846038203014221009000400e000340c03007104009106000c02c400411091b115450704101005242d03210045031003150681c1c001c21695803400318017071005c20b001d1000085400211510b800c00c09864200081003a00224101004500d001c403003a40040c141e180c17034882d1410140ca1104041000d0380016107184091200600070359034a00c25401889018000051403011104061140480d0f110000f561580903110503114125071040504607880d10740241c50280b07500a00138442c85040c0003e240045c0d00051160000446140071440c04d465548100001940038507030000c0d41e016408140003c0800c010100a810410b5076000c070b905130b1311f100959040d22800e18203911100c2e0729403034461101e83d07103081c19030341403140c82d03586c2d6071940000580ca80300310503507030a8640548640030240d098a0003603c1100250708000e0761082002825800081207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 348184082 1250 348182832 348182843
    0x50706060504062903131202010e0604110f03010b0d02040b12100c0806010c020a06030203060120010c02010c08090601060c0f02040510092f2b060302010e120c0d 71
    0x3034a544100080403200198484560340c0c1d080c00c01e0b8542802c3c00d00044600c0e241c82c802c450714500d840c0e40349150026044d00c0082000d4291040645414800d41c4600c1d45003a403c4110780701400e09081004c9441d691100191052008052040b41130406004070f005c1136401400c1c034801840d20380c4c00c110203440c842a030141c0103240000da008031488100807082c1071512078180081c1031183c400000f048034500412440c1070002001c880740041e100d04484108407001454010303143d403500c8004031462944d00ca070300840c40080001600182c201944290f6055529400030030014564840c262211042100d9001c1c1c19000080100700603802854030400f014490007404428410660001c0e00b194826a102c44e6007002510703081c03104450502c12a0700b0211304d00000800095a03140368050040400145100600c02050030b031490061b0701400903064104403608180300062540e01801003850344070590010304400e0ba03030000360604020759007141e080d02c00900a441a940c05100308501d81c210110741 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 348185332 1250 348184082 348184091
    0x41b02280f060c1206050607150b0a2304090b1f05090903090102060609012709020622050117010302060a0c12020a0c0509010e0105220c0f1107031101050706 69
    0x4011007688040c0741c1c894840040d0052044400400e64620b503210111081d1620000380042d13a0345000b614040350b4041403105006001041000140201d07449454101c8686030340030883d40c1d100e00c1c00d90121482c1401e40d03805107140301c0c10070043d90422840070707140401032400304150150b8a800c1e004415270340d8401c0f04100340d846c008501115012a04076a0030303040403900d04a19039052204980001003100c47c081c15505001d0303840841804400c070410080b514040a8032000c01e0b9030490b0007100d400130621500e55032001108010784480b800c0510b840f8800043c0410158000e01c40324140c0410780c108440c0b1a800c41d4240121a4404011300d0248000d580c4100b001440c81c0c154003e612250b07038050000d20300d5230b03d8103911451f8560849842118494018092615441462411140d00301d520071f000f81104000c42d40d134100100c01103a241ca0a00100c0100359403c02440501354076a5511221612141c0034440c1d2251003500000741800300d8550300c00d03010343c49840682121405941d0008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 348186582 1250 348185332 348185413
    0x5091605040503070e0f07022b020f07120b07020102160803090a140f0f0a0503181305070f0e180402010807030609330e040f150218041b02 61
    0x2850f240c2c2c80e17400340c4101a0750b90b0401c6600c0c0401c00d07049402c040d460005102c040300d120300030300d03500b2000e00708503900203850040201283c0c400c2020810700b100180c00c0e07416440d1146410420b00c46251002d40c0c2c1014a000419000341c814400c45200380c5882801c0b032540e07003407603039066440d170300190401da2944110700d81c80c03010ad001040b02494100140d001000200d551540301810001074440400198002130003902c0452004402c50310849040420790351600b4407400000c081e4400c151200c46050303d00340406c240c1c940c21001200007010b0503120640a115000c040024405c8a0426240d0300342c40c0101150065005070380c1c0c1500300020b8107021a120362140c001070b0444007403c10f5000740b560350f03045200181400140503440004842c10041c0214203000d5407442444000d000180421074000c007110521004070242000010224415540c50203100e0303c3d90340141c0a101c0b0b840c802c0e4a000c0004121049c1500120882941500649480068090801c05440c81107006410f19018001c030b02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 348187832 1250 348186582 348186589
    0x1706012105100503060a2c0307080703020a061d0307060510080f1b1903080c031207030e0f0102034302030325080411040f11120a0501050916050405 65
    0x6a1041410440e0004620f2504007058503014028119400407841e04045810600520307442c03c03016800c800d030815500c003070040400c1c0303184144031015120003c0403504004150380801e48100075801000140080d00b1280203222140c01c0b038118504d490ba00821a1100141081e08515401307640d00704500030003551003490b075081c60202858402c56400c20150040032070b040b001625826001070341e1404183d0384040c407903880c400940c040581b85240215049601400804c2101c9111004150794002810310306030284c05804003c04860b000e0003080425070141030b052007070f80c2c41030340714a030200f0505041c500c1080140450f42211100e8003120803c95404107500d0900f801c100d20307581c0c02550380e490403981001c580c08a1855582100740b0102c00403100c582c2c0182ca291300140c001175804c0e00425240000341c010510110400c400a080910b0015019041405020003201840380c1e002c45960785910042251800d000b1164081844004a00a040300c0342c05c403500b0881906020385480c4d12440003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 348189082 1250 348187832 348187841
    0x20307350106020f12040602150901110409271511070c031209060903080904020a0e180604180b070c020607060509030301140103050f18010204050a080307050d17060121 74
    0xd5030169111001362088000c0030880304001302d05a42d921418181070000007074440d41c91b0300c1d145101860000125500481c00c1d40645040d4499041142d40d4035501d0466030041e203076440030000640d04001c60314040c0995811060301d11a444400313950380c1d4403403400b058000c1c83e0680c03042c0b0b074010013849203000080500ca1014055802140712042d0000400380041481d1199000340f4200004068204001040c42c3705945451108840150310340c134440000f100c00021180707010713a011008503420940c00c4000d036021405a1170030b960610444035160720b801740070b4451600c01403904141400084480d449040b50324422440209250710700855a01c610f405e40e9015a030b503c4d41900000010130050b10311001a030702c880342c203007030601c02031070040700c090903001300181074101c070082d030b010300b513094134802e504480c00781c0001801032030700c5601c1e0355000340d0369080030b1411946407007a0386a00a0766070081c50f00d210f0014680590819564551004680601802c40700004030200131a11300c03c458400d024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 348190332 1250 348189082 348189089
    0x60203070c2009100605180f18150402070510020a020313090c0e0d12081b04030f0c0801090c060f0923030d0e06092803030c060b01030203073501 64
    0x189910035400b8000b0044035083c082c0c001c44112a901e1001c03c80690420142c40c210034600c122000c01f00c090390040b070709a15900850a6000314420241c40b000c84400311680d00910b298050140b00e10380700c80501081b0b00c2a8540601581d009042c0100130110f15001010003e50610680b82002c0202100721042019a040180e91395102c0d00452026940407000d942d0b54481210400402c44080c3c403100b48240202d141c4104200d03200f07001694a20301d2442d0701c184460009900b99803140d40c3c1c1025134079000507200840303d034602c2e020300040a00d01401800300c0c0316004085550540d2501e44141c900340c1c9106502c600380f10782168002900090000319a64a00c140d91441700c0c0c150741501054140122000690301703002d1610460750b03c0f621100d0540d40081425500340b00b021031040351642c88052121080d03100c01c54805004400c01d640080c0c41d82c05144214030510141411000540c280e000480d2540009038a0860500b05a44403a2991045000d000c000d002004d842122100001c9000d81 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 348191582 1250 348190332 348190373
    0x30405040e0307380403120b01020c03060a0c080c090f0d060e071403010b030f06010b07060603150e150f0c0d0207050105010308130e040507030602070c0b0a031a010806010804060203070c 82
    0x4d490003d1300c0e020a41002e18800c60010a810910780359030040c200003d440e0742c2003901d42d80c8401c0000d199000f0000d4480c045c10041c100e0b00d00f403030516003140181541c011400d0014080c503000c1098000e10b00292580440010900046000d0740d03000c3c0b0000040c03003c1c1c02e441407070f100c070080c0340424014070000028021088005224901010900d820340381101c0a540c02944904107a10380c0350004500641510a001034075076481c00641402c03409004c13a0f030805050300a80d85150110308450b9480401c0ba6448241500d402c6900748001c64080711080319115611001d0b0000500c11003a0b240052407400301c42c40d001410070805803982c1d03003103907801d800455007614006817010544004c007814800400c4200b03400105840c040d034070b660f02c504917880002c011075004142001049500310881c009003e24012854503203056100040190000d0310b00121115a80e280e02384181d4400e401d030300c3c481c54041e16080e1654545603511402544010410401c20000f04101400103511071074080540400380c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 348192832 1250 348191582 348191633
    0xc0e1b0c0312130c09050604090503030a0c09080706050f03040c12051506030f0304030209040c080f0a060c0906021c03060b12180f0a0305071b03060f0507030608030405040e0307 78
    0x1099403002c030000c0a400624a4403009401c080001c0c1c2e0312407071a0079101c02c4600410b840e140e185c01f00e03010706903138200100907001c04010070000c4078030342d0b200103600d0711503660700081d0960b1054050b896080d00e004010008030104006000340380094010b5400511407048022980e42c0c401e00010004541c900c2107a45030400c0c0c4d01c4100c0340c3c00703444410786c006904901038401105052036050b40d138803c500c8001e004140044c0040c0c14004600e401c04003c004500546105113040d00155403106020f907002c803125407a206020f001039104915000c1aa061a00100302c4118203002040f0000201d649200801da158507010411075003a9001d46180311000074031041c1c90610170084400b44415006850030341c1d00c6041c0c264000000002c07840c0300c154050502503038900990412024207548014414099844088004200656070f030254010150204d400c00140c0c0300d410302102911441d1007606034981c0203000510651900d6848214803001c0641180d140616540c0c504803801344620640c0a03240c800c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 348194082 1250 348192832 348192847
    0xe0402130e06180c030c0103090215030907030302011b080606090a080d05090a0902030408220f0314060714040605340309080c060d0b181519030c0e1b0c03 68
    0x422031903903043c02d40c00010340400506000425a5610300e6003202e410503443d01012000e540b6905a10b40b21039462080700f994914bc1294090b50320401d61004400640c40d08800007548d02c403049269180ca2407e5903074032051b44403101003006940100122541c402c0010708001140282000b01c2d510010407929000d440c0c40e1541b003001901c194581c40303091031034010000c00001401e43c00490344000e80324091070280042c014030506540d8005e80040c8030180c540b10003c400d04c0186c40c030180b1080c0441c811200d465170380d600c0c1203d48005000440b400d0880c240402c0c084d16010f58089c00c44805840d41011040c1071074020b020351036494409800c19082c01603051410700d80d1084070307000504490b41c0289900201d04000c076019102c3c000d189801183d44050030a42940c070f426569200c00c000040304041e0b8184058071580e121a21442144954915480040e00160f4021200210f030303003000c1c900c600c075460603141a400c81c200130b0401140030151060341c0c44800d15103000d05030348120800216240e465 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 348195332 1250 348194082 348194101
    0x1030b01170303010810091511030411030c01080a05150d080702090c031003060b0105070803071701090c050f07140706020721120c020f0406030b04050706050306010203040e0402130e06 81
    0xc03800801c29140d002040144401c3d140081c6001495400c0c03000066040c00314200398a080311071991440e9468200112000d01000f03900c081d50203180100520200c528840d010195206500b81038540070405070000548484400d034012640441161000c610b01e95103480003c48000741044204c500c0200414000c06504003009000d41c440c0000641e10f2960602c4828564841c22601c80100b0b1561a01906480c036445203055a801a41c8041c8a40d140d047c5071901800741e0158012040c03041e039100c40006107440d607500418120440a494942c9030000541c000403280e40300d08010384131030580d5129074140382000c0000e20020300059025107400b40c20007a0714800844070f007262003071001d201510310000c2215a00c024207914094242600030400502c003140029022041c0550f000385031400c004184944440024401c034891800d44c0c44003500c500003515940425211240141c0c42804103100300c2100c03505d55130304940010540c820701c0d15241100e03c299904072104000c42d800c480b05004050a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 348196582 1250 348195332 348195359
    0x80315030109050604080304061103010602010b130b22060b0f030f0709030210082502010b01090801051e0c070203100b031605060d15080d0801031b05060d09021801030b01 75
    0x4104030000c0c40440869203485a8819000e48007800030000040414104003090340106039150003036440c0c03501c2e50f0f5540406402001c01c1041c0f07030f004125031036154030403490510540340503803001000c070280000710410041050f020081400c03030f12561441c3c041080a07002015020648018040696904e0000c00c3d034680d001c4d0140881c800e101164a040c0010f944070820340c220a0103900d420700b065500c103803400c050102d031801038000003510301d009a2205036064001031a180400e0303e860518540d925070f818203e03031003110a206440051200c03480c02e811015841c079000b8840c00101820003c40e43c00190411801008491220341d41d8001d04d01281014805900000c0d10302d403041802d6032905000c03a00702e11401d1640e01909540d418003d00802010854101070000c4c07208440301c1548000000c0c00c814028007095540b10700010b1091107002c44020000140c071006000781c0e040c42c1082c90349202500c1021012030b48615040340c04290300000b2400f4900943c004c6140420f03951408034a00e5415 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 348197832 1250 348196582 348196621
    0x311060406150b0711040b0402090405090303070f090f060e130f0f0501090b010f050309010e100903020c03071406030c04031b050f060c0a3f14070b0411120a0803 71
    0x254802c4c8410300124071168400c0240720001d560200310156500300050092282c04140c80e0301ca4a000d003800303840c9500101a51040000b516010302c07008282c8015108000c0300c0c0301d11540302e50149400d0245078800e5400d441c884502510300c0042201e503812040958003011310b10280030342e448490140080b0a4040c00d030040201c00410010310144100003000800355200e11024000008040b50441c1c80c02d41c84500020300c1007041d40c0c8610003201103c40601813184040d4018854580c0780402881c003c1418021901495500403601c1030103030910465410051507040009400d00c00000071449a074030f0742222a5207019084403040c28041045510307800a40494041c10080c0100c00c6031450014444d14102e80280d49940180b1200041d540e508408400300d0b01c3c201c882c1350b002c40c07403442584048030400d84581c448028074005000044814040c441010f48100500340110b0089101041c00d048240405020000c0c0c134454044101d2038001d08240c2261150760001c204404891000070f10303100c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 348199082 1250 348197832 348197849
    0xf0e160e0d02190503101407030501120f05010204092a08010f12060b040905030c12091f110102040639121701030c06021e030313031106040615 63
    0x3100d844034007141c404900110000d00070080c07003404500c0c0c0d0141d0020b540003002c0c01070490700c5039202c604050000d85440c0d55103000b043c5040000c1000e0a000b8001d06059542201102c100c0d6505600c6841a00041c1c840541d400e550811010807407428074050111410b400c1070415881c4650b03078a14208121180000303070708204e141ca0040c0070038083c0d0070040045500000e281100c1380345a00b0564010004541910b601920302142c2504120011000e40320012020013501d007024521840b4041d14030071080403c0e805420041d1100c44883c10140e03001d02c07640c0d94502040414809030b052070880e8005d410420101e25a5080d03400a20990004180035907586640c4c2d10b2041c0c0700d0070a212404020480041400103910441e0310158032855444500341400020240596502d00700051035901c907015190040c0034131900100d4401502d034445450020a8006514540da041255496802c0d803200483c10003210481e6144003d0b01001158043c074080c0400103000b0f21386100001e60300b001c991104c480f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 348200332 1250 348199082 348199097
    0x1a151201110301060f050c0106060305040209070809030f0c0a0c09020c100204080c0f180103080904050711070314070e18010e0d140a030b030607080a18170d02040f0e16 74
    0x30300c07000141500c3c110f60032414800015103030004151040c2c012800c0c1c0d411198600403001030400da05070801400f950003030f100904651100b0000f2202407004aa481120380e1041044540040148000304400280e0501b0b44100c0d25603695414881003180d4020170a2030380100303000c1000c80c814804a21100c090502c01c500d0300c0d140c0b0601039102c0501121142c031496100c1c3e04040282c50f00c1c01c90240450200071103e40c10340c0c5030f20341540150081c14000b8007542ca0200010b101a010340c0165449840250081034030174503540d01d0302a0200101007001c01d41c0242680090740d01d80c0514640c1c09000c590380c2200c1d054070f030b000c5503d0031076120149101403503002007190b40c449034221034075803a542e004a80c0b269445a00c80c0c0b054000e089006a0250580320311420000903e0b48030726164040e41d0b40c4181406204030f021006050b8184030700000c0c0c12a0000800c901c03600301e00100038165485549000350826580f02e803a55000942e0780d102e0012140b004c0d00700014100138448150bc4910303207041204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 348201438 1106 348200332 348200351
    0x9190602070c05010f05091003231509061302030c1309090b06150901050702040f0c0c0c0501030912081e0a0f0f0204060512041a151201 60
    0x220086400100403d42e98401c0360846010000c40d0b54103800d084a440c01c20081707441c400f401c0800d1650ba81c180f000b9541c42c07000c0d2112800200314500d07610345810a020a03540560030201440f030440131080140320b54903440c7c40c40003482c612000507120365810000c001036105900350b0b140d00e24103444000941942ca90454646284601c2c0104c0c40d54850300284107404400f610383c540d800c101031024410b154850b402800d411800144040ba011005200c072404480d80c8421010004d18519041d2040c048203c1c1902c00804081c602003040d038400c2d8a4280e007103941c03170562201b00988440800c0407800c241d010041c2a00c02140494214100381029900405510a4101c4041d090400743e0300820540c0c0709440484409454007464407440019106112400400849010401080d0800030010388101e05204d0080175900502c3c2c1001c8004000c5100c4031052407030810b80c10021a42c = true := by decide +kernel

theorem cover : BRFrame.Cov 348021582 348201438 := by
  have h0 := BRFrame.cov_init 348021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 348021582 ≤ n) (h2 : n < 348201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
