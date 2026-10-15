-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4865
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:59:28.63879+00:00
-- url     : https://prove2.me/submissions/c17663ab-4e3d-4179-b6b6-bccbdb6ae001

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 874820143 ≤ n < 875000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 874821393 1250 874820143 874820179
    0xc01090b0a05090601050904110d0303061a0415020106050a12060b09070c060c08010f14060c16140607080f07060b06190809032107020c0301020f0405240d0b0a05 71
    0x40b034051005a829180d05a80b41d20502044040032100541149050701954616040621440000d140a886c0206071642c950408420072180712000095501d000036042100c80d01a1103100303c08417061000f84462864000007032015005030240d122510511882e01d001c100e2582d2020f201503d018044440b2894840e43c007034142d42c800ca8007591050b0604580c030307200602c50341d05641070700d00c003a8081105d0360800511144442118510b075130406820451940e155200f0855400390100040d46640b07003a04049800d0344600207400003a014403c01d1240c400010510800d03140d00109014a294548400c5d00f003550250030310b401102d401c00c8000070801c140c7c0960300d40999094045480720360840c0c64456030140e40c1d00c038801b0301031444440050051403481c400a5019000915072046448a483c0003001a089900511203408511400a020410307414464601e1601c0d501140842102042246840e0161702c140014080700c0c6035107400b042a16581c40c4038081c00f07030001505c3c110029000b0086 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 874822643 1250 874821393 874821401
    0xf03081b1b100e130b0315010b1b010c0507060902030c0d050d020f0f10590705042f0403210e1512240d0203030f0c01090b0a 55
    0x603032402030340c00249101605010f11652550190060488180d0071a5802100d004001d045613240e03043c064035803840c00c0a41c0001c41d00f4040d00300242d07002d81d034154561585514003803002c9c01d104242d051600b050001c039006010740d81c0c0c0d40d8000c0342c0401d40640610000b41001d801c078000315031100c2e41c4a6601c0074020300040e101142991902290540382d020207010f40e403210012480700c100d80c044400490074140c00d4125121324091848d51080c8008900b42a80d2103031001030301c0c05c0c0015045000700d024010407a07007207062a0504003000e110180302d90680b07600d91005016203405552582e1034140001e1411030840c3e5007500c0800515818018203c0b4284c0350b5002d4801030300e1080040da400200d01584655582c4098030a86641d400041110148241c032004201101016101400200e080c0650042c000b8450030380da4040001d0380c1b62015102000903042981d003400b40110116550060b1000422600301070700101030f41d52528a10900313180540b10054005000000750810f010340c0c220b01b500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 874823893 1250 874822643 874822693
    0xe0703032102042c07141e04051002010c0311030609160e03031b160f1202040b131508120406180b1c11090d03080421050c070e010f03081b 61
    0x80c0b13844050322900c10460340d01a0b0148207040f40681004441903000500b4185022903e1641d034840c200f46d50341c0300142d41d00c0405080180907035168110050074030390500c00c41070b0904840c1d46640c294104003000c1818440700034502c04034541d600c2070001090f03008031040d80518000604495803560880c003100145c0b081d1280841c0710348508002c010a211303040c0300100c103a0f52040b211aa1162400c3c034000795400080800303a8010b0781ea502d02c2c5115407030318080c0c08001044c0100100d0b441c061101801c60b036510a600074601ca41040c0303d096002c403280c030110b5044442c60301d0000c131721000c40142c079940700241c1d030f00405111400180c010310300350700d04804000c00c9805441c20000c00501c4011100c45100f03440f651f07540862403040041c0081e0040b80400e81280c0200c4c1000d0406012002c8a000001c0d904103600211b100481c00d00500e40703081080d0805040415241d0003194500a500b10703a60b20207004c018450400072513011034070f2401403007a00c200d101e680c088a002c902e846650050000c3d80c1c070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 874825143 1250 874823893 874823969
    0x4060c030806030105090c060f070c0308120f090c010f12020a030506011d030c0d061409031804061211180109051602011a011103070c03080c010e070303210204 70
    0x4001521501c1c2c188178882c8140310000203030081c3d000d43d070100806503010003403c60344480140016004104114104009544aa20020b60f50402412120380301140200160b0810350701b00100034030320f0000705142d0107000080c00d0101d00c040c1e441c941a00c8c1d1079401d41030a140f00344007048031310030154541c0200d402040300b81c0310851101c010240035140c4c0310341021a2505980040d080c1c100c0c50600c0d0a0f0381ca58240101000942074410702a1040d02060540300e6083d50b070f202003954516074030803a00310a60b00d88121010841c0e50300d064a04a803041800307c0203013507c0f40b4001d40406c2500c40080080000002c2058140d641da1240e040000608007a5000c0180c0c100184040c05080d00511404d400101d068079a403440b0540071004550068000d00848064003040c0301003000203803280b5046c80a50b01c14005561070310601c0c3d85040c21210f810140c1c64203940038100800200b0b0700b019005661900b01303407110800048201d00d0710040c0c41658001034801281c060316203407440e02ca0300a0a851000a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 874826393 1250 874825143 874825157
    0xa0e1e071107030b06151209070b0414040e150702010c0e060324010e1306031401060b040e070c020a450207020a03240501080a030c0201030e0f0304060c03 68
    0x2254044510721103400c1d2078000d5a112010503c00306001014080c0c0c0034100401c1c42c1d070400300754903840529800009003841c00444100034407800c0c5100b485500c000e4a842d0f51014101860b002c40180f041c03158003402070003182e4400000c6408103080c003440f1000800103105004a00b01160024000c0c00410102c2c1d0000300d010f13814030b0603450135100700d17401543c41941071242108103201d0309140715469680d050500c0381398119046162120321f41e01180400c40740c0d001901c107241d81084c5600c02c00e03071540c2000d140d2610f001800180b284106940990b1452200c07150b0903954001d06903071002d81c008029501040300107001510200e09011103400b44900b514240c10b03050384203480c8007080c1200c0342044503200301c0f001c441c1460710340c1d03409404450300060211421560381d8a0b142e424003807148003a41d10804180c212100034030940202401880b203040101840750a0352401031000061000c000c0c1015146c0d1503190441c001000084842c030840b1007039941c3d0355901c03000589a619a800c00b10046201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 874827643 1250 874826393 874826401
    0x90f070206060904030509190806100f0807060f0507060902030712031d010219240203040210090503030d0209060d110d06050909060109021b07080c01030e010c0e0f0a0e1e 75
    0x48190f50a01442c2c1c0b60f101c10303080c035680c0c40402180d0000301d00684030455424100084038401003090780c4c0518a10440c9007006810b210303044500010310703005100d00b41e0101108200c0d1035030100320000c20300e4843c90510b41710000c0d882c010018162001e030103940341c4221040410500e00d040c0c401921709109840d201c0d242c40d40780300102400008280060301580118420104100990040c0d00c44244110240411b600d0300c0705440801e49800c00382e812790b00c0e070301100708811810305010315005208181441e80115141c040001c0d5644a4001680c490f070340c021078840300740d07141c180540d185052207039000d1010500c030324003d00b02a0081d1812110352420110005203c0c103000c82094010070100c4050592a8203008408002c1c3d0700090f12560740c022036a8101c00310500600508000e85402c1000d8100084080300050541c0c0c0065401403042c4d00d4070514000d6203800c04032042d05c560b0255003100400070f12038001b950004255000070940c00c4c03c0000c001c8011401d03004c0c400c03c460180c50186094031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 874828893 1250 874827643 874827649
    0x4031506140d0c0603050a020c0708010603141c0c03030209030a110906120c09040201020c18060109170303060f15041217042d0b0403030507051519110405090f07020606 74
    0x1190750081c0c0f09a980b45002d0250500c6900100d81c8802240030141c41c221000c41664504403d980c4000c002d42d40d105030070700811680310030102d05108030a000780031a034240c40d1f00745e01e2504007006034000d00074261528030400d80250155283c005004007605c072030001c05d0600d078481d0050000414850403905001458516010307445130140341725400104401c50544017400004140038005078158425040782e1001e680e100c80729006080112071251002d0300700031001520044443c0c002415014080099060f08035000003940e81c01138040b6084601341030501701040c042c1450b400a403000800008021400f015101e0024a001e0f10954401290418920704688680260301507400860310304c50b90700b1800180620621040a4030781e00141c0345956034281c85605500c1540118046034000c1a8181400014404540d4034880e402590500d1310b040010400e40440d02d04042103241c0d581e90741c6041146c0c0f00e0302610042d00010307155031280d05201110040c5018101c50200051003602d0005034103003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 874830143 1250 874828893 874828909
    0x2d04090c0207080f0a0f0c09091a07020a02011704020a1503061e03020108190b04090b07020105091b010f05091201090c1505040b0a0203090405180c0603040b070806060403150614 78
    0x210b01d0501030720794960761b59071b259422001c940094580560072030340492036004621a4803030030b611030034481c0118480c403c841034903800c000b04103d0031743d001101d005002d80d820000321900e0b10300030540803c1d966114400500c1c060b00e035411001d4a4112013010b00340c450340541c025070130303a2219900d429020f5400c10800c0d2000c0d4a502000b40003c040002103401d540e81503d040074805940d51010a03e17000001c04030301103600224003a40d2545208060114543e020310556401034607040c040d000ca5080c40c1203020340701e040300c0d40356030400c50400042d114a40c80740007600c0305454000c185c0090380310840a1540601969001911819001c600c000f9010f4a40040c981ca0311500740c840e24100b51610700290082d030800440d5400394002000400d0b0540c0d47e504c41c1c94410070302c042d400d91245050800341840d04a0000c022401803504000340400b10702107448a80d4801e105140140c42591000c020803014021680003c018030100c4030348a6100e2615040034094a50346881d807070070703442403500f00b003102 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 874831393 1250 874830143 874830163
    0x20d050f06011d042604170c15030702060613090525150c02010f0c05030a080a0507090815040224190c150c02011e02040302040e01020c032d04090c020708 68
    0x2185035844207903c209421045d540b414100b078144c03424190342e042c144002045101d85480c0c59080810302007041d29007004254001c0d107400030a18258980010044c0d070b941000f030032641c0f1030704200c170906909482c29008103103859400010b035aa075500c4e0b4005011030340101c81a0702c0b030074845a02c001c80c4504000010b440140b00e07543d41d5003804040d41d0015101143c02e10242c404001c8080004030100f0f00400050441c00081d0b0b441d0210b5280060780c280440fa0301034101c00070050580d41c00c01c0955070020b16021502076030908281c450f2624800a6200d0542c81c04203030045242040045d030300130340c0741c1c060b0480a12500b00d00040e080594000c42d01b00a425078000c04031a032061064400c03411503800301410b40340a000004291544421045182c0a000004000b2030340005040c02141000d0107203402c8820a00002d505003032200d80b0743c689900982c01411090304001031200c80c220101a803400071125019851562161114015400307001500640009071052070000140e00d01c00040c10008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 874832643 1250 874831393 874831403
    0x1020f06040b0a062d0f0803040e091005090604120c080a210e010603020a09050f221b05040e0601080d0e0a03050d020604170909040609020d050f06011d04 68
    0x3a5519a0b880814484010f4096149141c0c4c9410220b42d00400c906650440000945d04454090b40720f85002c402807495081804066110102003102145c00800d9500741c0348446a401450394840e11114503140710711841d101528205002c4c04904440894a01d004600400c00c0200c1c60358030303003020784e030f40740700c01400400c0b980007040400d103082d01c94140500b0452804100e403606d0102f000a001c140c626080d800445c03030755034410802c110326040703040000a2852503800d0041c0d1501090f40e503140740c0028007240d4544a2203c482e08541051000c6954065000f0340506082c140b005080092622138001c071400b0b01d18001d80001d082d600000c1007412070300c058006083e00640341004032011415201100d0b00801201d20220000d00148400190400306074020503252405040045103508003289155801c2030820880d00107448580c0000e5210f134001c003002c03807181168404034103030001090025205004030303002d2602061010501034106c85011020044403d2010381890b110002504e000708 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 874833893 1250 874832643 874832653
    0x803030f04110f030f06070f030506060a0c020607060504080403021e100f02010e07030807031b2f060d1401050f060405041805030406030b1309080a0309210c060b01020f 74
    0x3001512000300c036030b40d440d400b402c1c40182480c000003003490548070740298200c3e40c001a00700008143d110003810042c03110380c5410b014034100f020100c3c400744070b85441282007008003110802592070f280200c403002980000200014501424200e1050300300b800100e01c00d8a230001e80100544040140d00000b0030b000f006080d84840e0b2000503030300c841601c0380c0319055540303a44020100c8502170041e0307001140104080d80d0340e400c0c9c038a0010300d141e1517502e4600c0150b40c0941c240c004034050743d81d080d0784d860040f84100c184800c0b00f0443e4983d40c0c0941082e66000344000b429050394603060300b05100c2e000580d004103281e80d0320740d820045000e0f01e5801c11504018240010031440c13805420256021b4803001480200904641341d00e410340d07003d5041000803a8403000041c481e4103140502441c0c40309424020442008190b58681c1e041c811103004004060b212120b030010300035210109103a500040c0301c0d0704600d02c4800c1d07002d000e00d0094602900e070b540ca0f1444600565001081111803054580c0c0540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 874835143 1250 874833893 874833901
    0xe060612041113051609210501020f040305160504020406270314030a1404180c030b130905070b030105100f0521061201140a0207021c030f08010803030f 67
    0x8640da580060090b030321001a551594031544070403200b240c00c100c03000004039480c034129140b41e0124140c01c4607201000b03a4640200308441c140590340c10400095402c00e0000380c3c09003440c074003a010382c01c009014a10700260010400c039000907210040310031140360450907070361481080100d009600c64180421103000400d0b802c1140180880310f82c1ca0840703400302d03080c0d46035103400280c150000c1200342260b100284410317445400050040141c2110719800345403a003844138031102c000c5400c141e24005601d50803840f80b80c5000703820142e4a01d001511034a03005002e40d5080700a400400780940c0c490042140118a0f646041e00700c0b03058070030207030000c00700d030040c0202218110514080e40e010004c2c14410001c00c0f0300e01e000d42c21208a0380b50381461090a082040281401d01460240710a0b0b14080700903044284c0500c04641c04100c0290040c0c40761110700114040e04902c640c3c1085d5040840c0c000b800309904514040900b003115a241241a80c841c030788a81d50707110940b01d135540e081140b4001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 874836393 1250 874835143 874835167
    0x11b120c0809060604020a02030c190b180a0605090a02090a0c090603110403031b1e0b180706030506010e04050109051f03150c0e04020a090602011505090105061b030406020c01090e0606 81
    0x1481f41c40f1952045a28280e0019102c3d0700340b81d5940c0c040c0b40078524441140c1c051096001603a07030000c1c03031b20200b19a5800f03a103c04a9550a20071002090b45498038009507440b01c1c10b1080c03002003500907121900e030b494000407e0004108604500000c0780c0710032030102c4c07007501c24032980d030a503600101e003507281c0740c00c0d0b403001d81c4c50383d00348524000d80c40040c04407000000c0781e401000e514807220400d0202c04108500c1d01200e882c50080c640d01750ba42d101641c9403480d0000080d0a022506d45050000d900e868440040782c9000010030310302d40080c10540000380619040e0b000c0f80c032400b0040d00b80c4100310384048040701d8044152002030180c001d514a11400d1298503401010b07000c40b18104402d40030203250200d41682c0003421320a012807801c0e0801c009054080c0641506200e0710810302d03000354100000900c0b9103c06010780c5000798000700e0000c080e0f00318480e400b034807a000ba0f0102c6c4d0301c0325130380c042c000d43d1a154642d806001540c00d0000103031260000300c0a60240c0c1d00240402d040411501d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 874837643 1250 874836393 874836397
    0x4110a060228080903100b090106030b01203f07120e061608180f06070f060b041805070602070608010501030e010906050a090b06060313021002011b120c080906060402 73
    0x1095a0000c02002281d007150740c104040954410700d0307080443d803180ca1000300604140c2c141cac4542c0601d0f04120501ea21a80d110300180c0d00c11440b1112482403e04078544946002100d0304003889003007581d620004c004181c280c0ba01c050300100f059150070103208549026850007107180003800c03840003210800e0080d01031440301210b5030300039115a061601002c802e0224500c0f2007001d5460b0300c0b000407091202a1202c0d007008103e501921444401c142300300128105200d4004080c00d9664420b8003130f001c01480da041086032400040007801400521080c02004041502e001c0b500c0c0e200d0940001406400454000c003161800d448084040c0e00c6c010065003d455081502c034965540c400403640003503260701c00c0074080c1c84003800003d0400481e1800d070f1b09011001c0c00c00e9110340000c1c0100141d40a5080c01c1140f09541036404c0030303d4080401c0140d01504140f688812423020603a040804141d022159485411a1a20030301c05c00c164501d068a0540e0b064880728542e80007400080c0640c01c190300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 874838893 1250 874837643 874837723
    0x2010c030201090c0608090118240f0603050706120b031005090a0f03090f080a021302090607060f0f110703020a020613170318030d08011211040504110a0602 69
    0x441c04605070795070400c041030380b1340189020a200c1d1b8144140e1a6092040741024990385000e4801001992940c0c103480448140084c1042440d4601042c0882c003074201c000340d01c08126050101c69224505240c60344401d0103040300142d0802c00100003024035004845040310058007600e003c1003150007203009090002c040040700d01c2402030350400103502220000301c00b400fa0f9200010f550070a01402d0619890380d0144e00345500c420342c600302580d5401d034100e0a500a03540b00503a60703000c0001144280c000c0040150030380e0700e0000d44010b01480ba0b00540b032100040c00301000108800038400615001d240c00207130040e488003600384010b04082c0700034180d001311449805403451343c8500613035907804440224000e40d0070101c2c6858284221503040c80c1d800c20110042c180300c0b552842c00800c0031405203e03504142c070104000101780300c0c0c481254087d500003e0000d20491410b810124180000d40c00d44c9401080d500c1c1000960502c040743c4a400115035841c24030303900c5c40c000c0d00a401c1c02d50080c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 874840143 1250 874838893 874838897
    0x603040206190c0209010501020312010b03090703051906050a020c1e010209040204030c030b0601030908121f060512090607050f0304020a08010501180f11031807030611120a110702010c03 82
    0x400314068001c64030b04101a5555030382c020404000340306001c42c1c07030f0b0181e0240b030556000344240690302118035003060540c2c1e00d10009540340e07038824070f1360f52134802c1951000d095409205107000b648038100c1031100c0d5040c055501070001d920340345541d10803881100c43d14100c1d90441507489032001c003204002400b030085480058240481600003400b05d9000f94000c994106141404000308120101000e40c400c1c02400c04022000721602c2e0150203101e80c0e1885004500e240001a0b03031141a1242d034003100c2d074030f0411542d8460b22003401920650200c1010045124818001000a60001085441015590b4038642040d8084282d68072030740010b441241e110741d401802007262502441618006d202c100d11407540607052041c910301b210404502d20341038900740f110b03040388041c858040340d803c5000c0700400702084030a03c2c0c41900f81061600000c2c0710741c2c06c002c000b0340012605009400402c80c54043c81005465a190306c404a60840c86540442401808a40050b60040096020a41c0a4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 874841393 1250 874840143 874840147
    0x30309052b0f0209090a110405060906100c080a1d0406050604060507060908030405071503090b19020c060a0218041a040203100e04060f0b0108152404090c17070e0603040206 76
    0xa03030300284900310b0842d000c08290340100800018001038009030300f80448180c40030809d0f406c08101086101030018103139070159800300b140541c014412400c12200c2e50f007041103a5160801c0020081c040ca030404480d600840b80215005800d140910a1204484004155602d81864000e0a5138260080d00c016200c007940c81c00d0744000315078140c0c0114801d62042c0c2c0035051290a0916003498404c041c52448209448d0408140000d01c04903221a001800e540c54000c40501001488003e48140540e201c40781c010181884440c0840d60090144541e0910580440c54140c00512048a600c054021081d03184180d081030745040943c01542c0220380c2002c100c074400e40b1514020044481a07500315aa230382c0e24803041c1c840b100c2d503129070b80c0200d00906c0c00c051070782000c0d90200c8000c0d900c0c0320f115200380b4507901e4008002943c004544000d4489911098a655845139240c0003402c0c01190440414030200a654080d02c0c441e07100d41c411181622001100600b100a000554000510490f005281 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 874842643 1250 874841393 874841423
    0x2030910111e0f01020c0d020d050705120304021519020609010c02030d0b0109120c050a0e04020108160e031b090a0b01020d14120c030610050c030a03201201030309052b 74
    0xb081c0014100103103400e000b03101f0000700800013031900549420042c2004003c0c840000000e501050030814480c0031000c03140c40c2e440b1400001d038a05a07040c0c2070200b1100004038510041840800c6c6005a625502034401560303460403010300782d1700810881801a0000c0007615015003071580000c1c05040107140c0b600402e07484980142e80d0200e06035040d0350741000c1070810040c61408180b400c0c007411640319942428146540068040c20001d000d07049044114007450b4411441640c1582c0040c20007811968540c032450103036101080080c0b8058024026900000da42000034000c0d41200c52044c0d004002070b16140004450600700b4004020644138100f124512001c20000018051051100003698909110b0f080103e05401750211005008043c000b140f40c580000c800d03034005240302d06010900030603000c070103c401503216003d42c814071004215000c0c1038800d1107006c1d041e02e119440306c802d900e031a40f04220484880b00308900c0b12000160064800c4021040c0d0310451510510b001c2140b280 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 874843893 1250 874842643 874842673
    0xe040f0218010e0105030a1203050727061b0f02060309032107030b010801030803010501120209150a20030306210105240108012115090302030910111e 66
    0x4001001215000e01c21005001e110000c441203801048214024443d140c201c1da26503907140348c10310244003070650f1000080d200600a1421030044582124031350100d85802c4d2060400c0e60090046030006144e4008412540654100c80070310140c100310074403600350442d42000000e40c03004001c001c50340020310000188021648120900e035640960100c40b80c5032244006088a000c1007600b030400540c840104017181d840740803241074810a00c2c0205500c00d4050015010748908000507400861801e040c82000b0225006441015171a40e200f025011101e54841848180a4140400b54004001191182c6044044110b80001c0e0400c2d02035101e141c0e01402e401c4442c1224801c907240340d500c101801b041c05000010300140b0013420300b00750a5041600c1604881440c08003030075560751149100040c007000d079541e41031109031840140085501c9140083d125044010818081c101002d91801c0fa5805216901c8002100200034202134440300c221f091031a002c055061543d010341802192411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 874845143 1250 874843893 874843909
    0x1c060e0a0209181003120c031d0d0209150a08070f151707020a020a1a07060f0207050a060f0f0209030319030b1003050f15060f0307020c040911030706050a090e040f02 73
    0x20b500c131510585a0b407550928841041d6048503407004c0003070f000c8942002a80126441501c0584a80e2556800c040c803404280458000c0a01075031140c07203041007001c05004090343c0c0e1003030715064030740c1701e030065403400103955600d40c41c000d00d41c0c00354a1240604c910142d41160302903400032803a02030300c000000070100c81c860038140ea43c140141c006030540800c0d402e09a070f0820050100300988441102841c51000e224020010028401522101c0d8400165503c0d0140c4a0654014042da442c5804501d8440010402d40091000d15410703d452655240300501c01d841000b00003802031440c064880c050f8510911640c1880b00900d43c1c4c44181508945810821030115030322510b0003e15803e01180032000c0e12401410590010110310907404c040c1c0f985010741d21071001c004c101d10740303e460709082a42410b11002026800525040480c002e0010740040c41c6e0064006809440d0056101c1c20215020303c2540166408140c03a11002c000c40ca41d54064264428000c40702c4030000c04e210341c0002d800c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 874846393 1250 874845143 874845151
    0xa020a060810032003151003080304170f0c100219120e060c1c09020a03020d1a040f0312060506160807050a120f020703050d030b060d0f021c060e0a020918 68
    0x84000301d0411441414200500f1952285d410400c2c1c1b80c52500481189101a06010041011102002240400c424002101041501202190303186c030501d5003035010300c0d0070441d045036240c03083c0c09a81c40005004c3c400c1360307030040b503140c109207144546400503118a1202e01488018503510f243c520203003c03052102034054140c0c500380c00d964a000f480c90000c0304a80c1c00c4021021460610401d00581c0d403144144103c990585a00782600c0107402e082001d2501080303041c140c4062070b0104001c015049070000d9007a40320352038840c4030b007145001d141d0458025004a942110f002c10001c410303407180401c0701402c24840c814052a207503040d41c03106c1c03c110001d24100c1d045010b0f103007162031090304501038440082441c8000d0181a14680f505c1ea0703504c600c4480030050554070400310603a9142d4008550300c005070703114184a005240016840294800c8415a0b03402190b40303290b410803041402100d0440c0d64422820000d40c4411a41c1c078025400012501d91096120250329100e03880405d8441c89 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 874847643 1250 874846393 874846433
    0x30c02100e01052d0a0c12050708010603050108210c01090213020405040b062110120b0114010315090b04090c150f030207020127080a1b05030a020a06081003 69
    0xf90030002400c2d0303d003450136001944404030708001461034040c00242c4940c40340038804042240ca600e9a001e5420740c032520300080e1b4550500c0c00300012a60020707001412204595410000c607a41c564160780c031080342d4a03140c0e4400c440003140d0981051044050040c0d81001400050400959070004800d00109402d1000c50354012400b008a40750520420040700c1003078520628192040b0203105c4c2c94410038040384808400f820102d1200c1c818200302c4809400584410b0f46454154185080c2041091041074184466081e010046522034092480e0480211103092905400c1483d0034019080130a007140c0c00c80da4502a400c081201c10740068000c00c5104404508048068801005620f4481c148800d040c0100007020060b64088a040ba0060107420aa40010410310070714420100b154003020b40d52003445842c0381480581c11100441c2c00d000c5007503000302030f901c806041e210503510340c0107035104448403401c02599014030b40e85540320400301c0051300c0700b94a0b03070364040c00c18010002c001a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 874848893 1250 874847643 874847651
    0x2250810090c0503060709061209080a05030a0501050307060c02012a0f0b1f18090b0c0a02010b0901050306190b06040906052107060f0203070203060f0f010b0c030901030c02100e01 79
    0x601245400c844003030f100c1a00941158a0302d510081c0102644e880340d002001203060755a034034501c55601140c4e840303a024a1096030b40780103080c02040d0b41c1055801c02802454100005818a070000d0034074101c408036200d03041c040c212a00152030501d422410f5844607500e00c0030a41c181d07880303640982c0306948240054071042c80b0710309141d4050364008118602d059811945a055032200b80c0c1c440c4101c40350800314242c3d48914130054005800b80720401402024044144042403859030041d04d528012a8000c201c5004040304018a41c0020702c1141c1c1c00d42c00c031402140d24034030b03c0307005108110160000030031070b4901c0f900801e9260784241e218240080c0c0e111b1003840f052405a045c070002c2d0803034090031001c00c540c1d4003949484990b1803140d00c05110321107405462140c001d0080d035410716001030a6030707080d151646060884400450746802966075210021441c80600c3c000d0303a4040390100d00840c20300418100660003803040500a10940c8140003c10004901d580510301b521038000380081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 874850143 1250 874848893 874848911
    0x5010b0301061101110d1e0f0506030d050702181b03040b1012020a06080603070f030807060507020f2508011d160b030c0a09030209011502120a02250810 67
    0x2040f440c2032005440c1207904041446007000c0c41030f000c2d900800150f140000c1c003008500403444103001d203003251208450810744041c0d180d07580355100b148513110035410b50314025580300c0210b0b03c502c07440100a61100d10591650031500001c516185d11180300e081e50300e00c5c3e00d50081d05444940080300c1c00c640140c0842c00b080652994001170740b000b00a18000e05440c075096600080e00d00c01140209010401d181000444a9808001400c01407800da01d04481e400d032a4145000c20350b00945042c0c1d00e00781806c01258000380300140f4070b8500c000140c0501600f882c015001382840c3c45226000410b0b00c404180810098800e00c16140d0a1001d94500c0d0b001c44803c1e2040b82c1041200203141182140142d004c000c8290028100c4e43d211100ca002540d460201d420140d03a0070000307410107504028984004244c5049103100504580b2503034088986041158146c81040e1145401c1000141c010844400d015141e4484c0c80c0c80c1d00094000c159911030b110f5203047e14003800012651141d0740c542d1070034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 874851393 1250 874850143 874850147
    0x40807150f1d1c02070504060f090606050310090207020310020a020a0303050c1920120d0b0402040308040302122b0e0406151107050901030309030b060a050907051303050105010b030106 81
    0x3402c003010a4406102d901030345002003600c4612000350301801c880b10190b40202d0318420311081c000b40400810401c41940c032030102c07890440032800340f5600646000c2c40400e40b01c2c060000e03644540d0000707080281a900b403105040c00794101d51001c81e058420300c1c2821100f4049400540f0050744158002c010038001402c3c01400d54401408e11460318104105240e00c143d2a40006082540360b410500006002c0b00c9503800c40550030340100b015405440c02d0340c0381404030b4500500c41c0c41e6036040e003800703040d0301101048224407075440f00600030a0100002c0005090100b824080c4824500aa41b007001695402c81c642c01c00503104a0321030301d0154441c504094000ea002c440e034010030b076400c0000701e06080080b0806101c945084080c0542001a8144100e0400c1a00040d20000d4407600300c40d41d492802912124403404200c1d003010000740060f1090812150344001c80e1002018003599071500c100036a0075612110580209051071840030003c034000b409014000d1010000d00c030350706d616210300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 874852643 1250 874851393 874851401
    0xc0f0215190804120c1b030b1608090307020409261c05090a060e030403140606120a200112090c03120206011211040204081f1b02030d0203040807150f 66
    0x6060034065400c0500c000b01380d0044e10720010005a00340380d28000c0c41d81c02c0081d08600c2599911030b10889212000c42048051600d1754080c040902c00c02c6d003030301d4400c841550103450032500042a1790040c0101000b43c54a0740215030f034580540d2903070602e800d44403017100c0740b1a01c511141140c040c001a00b20f009030841c1c40a549580035a0f64100140c1c18103000341078039410500c50240565403100030f1084032003002d2017168021607215030307008190301c2c1700b6040e103864250454a45102c5c80b0200c00403054282c02252642e511a0700c0b212100781d0717507654075408030700e61603150381030b810055001c1c0c5514941748240b1450701280c0c02007404260300341ca58075008102c1c0790784040c2d0340d0071900002c0c01008180003982004803060341c003894003601d8201040104009010f2079000c88098030619001c894143c4a0303202d20100fa0140d42401d0101c3e89103848510300a0f608428100b0041c0e104004000061040e6405980c01c81d20810340305240903642e4076002c01d00c00f0b4041c800e0115540c1e4110b1001d040d1031900c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 874853893 1250 874852643 874852687
    0x80c030a0201050702100323060a2403050a0213030c030b060a0e010b07050a02090103060b090c03010b0405011d03030f031509061c110a08030d061d070c0f0215 70
    0x20100e00c12658002040c600489000901a5110311101d0006074061b400606c0400751407030340e20b44840130201903619100011303115a4000ea401700f00c00314048070b9032039814059020912550b644c81c1c1d0b4a02c0214000d110007014080e030283e00b808844110b607480020680114003819038640e03480d0850a09a840c0f800c050240343c41811f041e001041076526444000341150016441a500d07001c0c070b41443c0b13080001100c40254416081c00000c401c1001581c8403404042d800c1c0c0312026180c1e02c0408a280c0d41c032007800f034112054824801000150312a285001504800c4046003800380e04c54000300b85507402143c0254450741020082040c50000d41c100852042e000320303114055414004046000030340e015407415098a1411503070028401880401070302036038040d0403188110369556480c2d88940118000b922245c2c10000c001800806161600030400c00c03025410656032280d00701901d400c18002c008131f1b09a0304a054050260351a5501c1d0f00b6918801c080d0540c1e03414031041c0c81c440480d0548 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 874855143 1250 874853893 874853899
    0x31203090106081216020105160b0a06030b0601140d0e030f0406050406020f0c090a020306011b0302010b032a010503070c0c090518010e0607141201092309030304031d1207080c 77
    0x405126840c0d11715000a001183e020300300fa550303410035025401035142c61400f0260404000c0411300071013003150b030300040032280252400301281d01c45000444640400c103070021114078080c0400704031303080c8580c006003000c0f90200860b498031100d6040703252190000d0340482e01180005c10308001c80f82c1c0501c00741140014001c007a052414028000980394000680184042d030b902000040f0310303900688903004001d45000055050140ca40f4009001e84040c0400034042d008014128408200680220005401c409900e07201c0e250400011079413600001c0941d01044111030710140420b420714400c00240c5903c1138041810300c0d040410a20030b40c040c0050a807241c0c90710042c1000b0103400b1900c0d980055052803c43c840300e4544100059a0003002c20608001c0009400000c81d560a60703c50217074588c0d442c5408404000505211041d104200c401058130342003003001400003440b61140002e03010400080c4650004a0b60100e200f0310007205115605501046045c411403108010300da440c6c500072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 874856393 1250 874855143 874855147
    0x10091703041502070b0f031305030c0610090e0a0609060b06130509060105030f1303021f0f050c0304020102030403141519050a02090d0809060403080a090321050a0e0312030901060812 80
    0x1c00d0030300d006841240d9240d040031b1404400300c1d0480d40741c00080a6400d812008030f9407154041110541c441e04103446200303800102c100002513000c0180508074090781c582000d0060b030344580d282d403005400112030440d50140c0d603031642d65541d034545020305001601500301c200240d040109000e400140a402d140c140b0000b442005010034823000f0041e84100c1000b0003c0c41141c40303150680c5066580d0258008245060120010340300641d400320542162000b0180a1138440541e000c00c10300c0b0949010f030060b001040144007045041000342c47d07610044080346e510000500c400902d1200c00d58114403032014407000e042090425024042d0041d180740b108500e000300110004168a907074900c0142004d201003110713000c5a03034503400d40b401142c0003400380b50744410603200149502c0742070008841d100c00403442100c042c041c1c0c442c50012804140c88552914130b00301d0007070310041c0000140d9030381480b541c45100101106140558050054040003003072250611aa9908000f99000e11030128541 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 874857643 1250 874856393 874856399
    0x912041e171005070e0f040e161d0a02120c1b100507080f06091b070602030c030103170405010c0305070807051c020d03090209070c1401020301080d03050108011a1009170304150207 79
    0x40c0500504c0d01da000711000140d080e0b003403072000c0c227080c64a0f0307800300c800d03901c040d0010706607200a501e0040113000c0030180396240d40322507544003240100c80300c2202c882001400100b4940d501c1c00200540010000c0d600d11070741480b1001c2d407a00e004144602540764440040c40303141500940429001b00000c0d2801e8840d28081c40402d00320800100501210f00343e81c4285109a51100119000740350801e4080d9070380c0c9800010345403a80e0007031008071136504100244414003403108003a20141d5a05035500d2400700101d1f14222030981040750b06a4016030308204140000e0410451a080380c10008040d40c4500392500010b07040403510b90260b4240340c02d115000c0010307554001c40036480b006c18100b0900c10242c50800c90b02441c180d0340200d00941c40040041440b8200146914001c1c0c210758052100d41c1c0c84200f0a070036203280010808a56040c40c01c82200d91620f41b002c1c503501c1e0014984400e446907960304860b9450541e100c07100b61a00001401d02c50082d50703503020702d1002c0d014001440101c0c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 874858893 1250 874857643 874857649
    0x903082214130b0402070b13020307050d080d1d1014090a02150304140a030e15040e0720100204050913030c060902210102120912041e171005070e 64
    0x30b00e880405049a80c50038092903039640c99054421168000e10a190146480c0d481c120710743e40c110a040e4460b2240c10000103051802207854031900740d21008060500c0c980e020008098041c85000c410b0303482400203000c1e08000200982e0140b040461008128804074072511043c041c4060680c1880e60840201c0303801580395030b403007606803c0e0798500300da80c2c1e942c403420504102114107007a6000340c09188814010306030700c022160350002049903248007400b020340d40c12400f88138900c1194070b411800350024030200c1c0034075440ca01504110760b00000c1003500350702c81800c1800280041e1300c1507070f01180c140f205082c40441d15500004e4030000010300e200340d840192150500d10300081c08152240b118508640b692000c4504048010030030001124080710098046e42111807400048051040001e2102c031001894602007040030b03005504c0d00d41054000d542d00c40d42404002c0404150800c001400d40a6000000c41d2100000c0038044841c54910590b0039198040c0540e02080f6549626410581e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 874860143 1250 874858893 874858909
    0x60f0d0b03070602120706021608030703141e0a0905060712110301030218090a0f0f0b070207050109060f090509010603150e04020f1e0d060c0306060504081c0903082214 74
    0x1601172001d2500c8a640f8a0148003901c01d21203409481c2500300340c0003041100b100e02171801030003a6203050044002242440792031200c110782d4030307102a07045029025034980709500280c0000702c20502046041e140d031901482c20000303840c101c000921485000d0208103041c03103134041460405000900d15455a0000b80315203414041411081206d100407841c1c070001002820b030f18550111a092031240e6030704096a42041c400d02c246e07074031080480015840c40c03010540b1010395005840d80b0791040c1c105001100c0b42248106598244005001d0200300b50f5103010b01070b4024940d0356070200381e0706103d40b80c107821468a94002040b41000d48207100041c0c0d95040c3c0d801c2055030a54458485509503102e5149259501e41c8030364101800301c0300c400900255800150382c2140c070b52400d001c05992480122401e21451103884080e40000d03000c640202d0302c07449200280102c1e41380080c0c2d01034030b9441d410159404403c2a0881601e503841113060b04001c01e082d88002c0c02c1350703080d40340794595940114581e1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 874861393 1250 874860143 874860163
    0x70807050f03100c0221070b0406050a090609050601030c0609060914062205032a04090203250311010c1509032c030f010509071211060f0d0b03070602 66
    0x508021280e14030039281000440403100034410103101300d000482010b5154160303031141d41c0c8488003500c220580c080c03101c4101c840d410344c056102e181c182d0b03da0b1502801484003500121101d6281c44036031300411158015120003500a001819071945185003801c15070051307504c04030500810341d00402c141600301180000301c80d000301c5c200c1551001071001465500ca0f40c0500020700c0751050045520f80da2034441c0c1e000340e40060303046544103407500000c0d405200300c8901103d05075042d43c4c074901c0d583c01d01c2c2d006150101e2001c1d00f03c412040b060002ca0031980d80ca5004100f824203100c0c400c10601001d502160000791080c04c058092443d540c45113014008241d8103070f40e40e291281c40b42000c0501c43d0306400ca0141002d48665208500100e60502c151a40d000c40c03407080c814113440c203a5110040c4202c40c02842c0c1080101500707443d01c6190a000400000141c0315000c00580024540d00c40034000c0981d5041c40d02e20360790314003100c0041000c6849040d09030303000703900020050141c503400042000003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 874862643 1250 874861393 874861399
    0x2010506150310090c0e0a0501020606030a150207050706080f130b040308090c15070c0f0f03021302120a020307021c092d0303050c060a02120402040b0d02030a0b0702070807080705 79
    0x503d681d600812414440340e030f40108400c9242c000803200072580a4420301c0440d008580c1c24003d103a59500490345c828003901c0c546d9040d00072040c408000341b0003001105800081c080050f04218a030b07290a81000015802280426031a00c2081070280b200e81006038001d000300f05002d03010310b0541399a580c006000380010240415a408982112010840e080e0b00010080c00c24504158651034801d594124020031281c9401500d0301040e0703501c80c2c0603100103640c0303a07507a424201403541c0c080000b050322101c0c1d07010740300f54200a501e100455806480d481082e0074100581c3c4e9061030640240703402e03407016061550001403603080c1c200d0b0780d1003802d1504984044403402e0429202004190b07400440310900345c510340c11140000205078004025020200745d140a86000d56200040701007a441101c2100010f045e0081c002001843d09a028001c0100060900640f207100c0740d0103c1d10706003020200b503542915241c10001c4c0f0315130401800001d800250080c0c51120303c0c00c03000076610181401400d01c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 874863893 1250 874862643 874862647
    0x10501120603034e20070624091a03060405250f0f030b090613080708160609200901090c0c1208090706050a020d0c21021506010201050615 61
    0x54950410044c07800d6203030880181460402036098030392180c0b108280d00c0411107040c180c41c00c0101200c1445041c5020101020910301282684c40800812141030f046003019480c030008180030502960310009040500800a05c0b404459a0040c1f9401415280e83c801c0d448042000002840801c14001244828000a0380a0b25032030420740c81070340fa60040f2441011071000001d02d0084e50f94100c00b1640540d460345c3d1992294407540d03485540c101c80e0400c8005403e000c0d80c0006460b500145600c6001d040300c5410000480714540d804442c0071020780c1c095841c1c00d1396209201d4820300980754101041c0e104204201000c01040c440380051003444001a5030303007102103005000e59042150558440c01d04120403d41030780150403400107944807965407003000c002141b010300a0040b514404c605030014031100e0011030040701c560a22800032070b494010b4080540003400078180c41e0442103500d801604202d8420544032414020090216045a040505002117611b8115003d100030070b40307014030350b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 874865143 1250 874863893 874863947
    0xd030804140f03091201060b0a051c090f060e030a1d0d0f080301150f0c08030a060b0c0a02010e18070c17030a1b0809030f0703021f0501050112060303 66
    0x354980400520745501d600511041040d1210084020140000c04580c0c4103004041091041d00300c0b0040e02407a050001e00708070244030107000c3d40c00b400c8420045040103500600c100e99907015615620812901d40300158504010445a4060300042c816140001d504140312180024100490384c41420b4148091030b40d2020700b600c51507445604150000c094110182e4145070410180c2d100f48a007003281c2c0c0c00703011a107011a12450850b2891340381c0c1e965410b030245142c1c072400c99552000e406014035655800b000a0842c80ba0f101500d040315882016003900142800054080c02031103034014070503e2124050103088543c0071409800480d14506104030702520301c0d00b102c1007070710f010b0200c1c1e6401c804400c10a2403445034204414105003d06036000070511030000b901c0c03800d810780300f80009030000c1c00b581c860b401c00b10001e0445140070340304039250000320340240c0030496100350389060300949403001400156040480706284426418042040e03500d1603d00038144058401203428001c00140c0b00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 874866393 1250 874865143 874865153
    0x6070806010e040f1d0601090207050a081b070303090614040f031b21060b0303090a030204111201090b03190305070b0a020d020310090b010504050307050d03053c0301050d030804 78
    0x441c0311449030350304000300204005c03401c0b900785420440b40c0b500d11503000041b82a41c024000d641d692944a0003d12102d8044e0b0303038806442d002810815102625406080d0790b108082060200179800790726001d031414202800102400002003658000300c400b00000c0040040b9844900c0459420228a12442000d41c118822600c91a4000001211012405d1040c9400b8101c044501c501c907820810820400c0c100303050300d034003034a80c10359801220520100094140354008510b03940c1130f8810f82e850007000b01c02c65207101c407007a0004044150303641760304180b6050812010f030310680d01e0f03145291501865035004109105110005105211200c045031407c6201d4050b265076810000c015901c0346040b5250b044004441d2040003011410040c255040354090001c031006da54015001e8000542804d0900002c0c030907a190490822100300a907981c7c1c0058407000300c2c1c1130000400803442060455401524188004611907030240080004114517035400700101c01081d4035081c2405595200d0800d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 874867643 1250 874866393 874866401
    0x506031612230706020f010515060304110102101410050a050604150e0a03030e0a0b030c040b0c0c0402031f0603050f0a0905120309070603060801090302071e091b0305070206070806010e04 82
    0x10548103120342ca5000c183e145e00416030b80c40703510060340204500d580b40000000c10007441056540c10032410008103004c80c080c54501c2d0f124400600485c0d001d2001040000e08039140641109880f0000d80180011310307542800103c01400212820380030542403400140951003244991151f030500281218001030207070807031400141c2c1c01000b55800036500d08015041c20502c4010a1003903004400100300341c102e40007070b00c0c0a90a980b501c14105400c5c4061130b1041d9006200c04101c034030415981018982c0e4a000451040a490000c1d4a00c5280403080d81d0040307801d500140c05160805007040781080581882503401210a58045840102400e1890500c0c0d038003080070741c4003500081000742c011070000380c0c00c040350110f07542001065a200f101a0807920581001001030300404000c0001951002c10f0403040000034100c800300c159540906000c0340c0070651140880c031160804600d11035018860180e0015640c0080e0402d45000100203003036000040c8864140300109000e00000d0310707aa40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 874868893 1250 874867643 874867703
    0x8160e06090f0f1f030c080f07063e01140108060f040b150a0f05130209030706030504210f120b0117101a04031209030506071419030506031612 63
    0x103107140e075544900745950078010074050101f082c82401c06c403210b0b901c40018200216000c9079258003049000400d115211581c039601c0c140440b0103000346c10f216074540b004115200b480b0500000b40380340000c014074a9940c05900440c0143c00c65020030000b482c503000320a0381300d68480c1030302c002552030302100c0840141030044690001038036440803405510301c40202d000d60303a0031210384249010008221051303109808189816400c40032040150601982000b03400c68418150109013580d0342e400307600030186840c030f1280014684d03220702418503001590303000b1291039001d042c80220000c100203031103d541e51054414084e900c1c00060904800d144410005e4004c1c2c07001e1140701d81001e40800c040e03400a00082e01c00004070102d80c56118000c0c01404220382d0b026010341801d50380d8007400c1d541c107030000080c1d480005040210348224056801362046490951b10000344905040003490f15201c0f0341c1d1041c0e5000c012030070307007403000350f004a582550107036201e00e90303000d6084005050441165000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 874870143 1250 874868893 874868941
    0xc0409021c020310031e2103020c0a03020303040b06010c0b040213020f071a01271113260102130b09040f09080703020d08010f03030309050708160e06090f0f 69
    0x103c14030143d80001055041140d004c0d540ca2410003820000703408500c1d6040100070109020143c0203660350f180c0c00f0801305c1400c400d0400504007250880b03940d0038444002c10490050300004200310400900c01c05664000740c0a18210000c120541c3d5164900b010203071020740f280c1c0741104405070f500c40c141c0440d020810000c1d03606445a0799498640441c6402841040f031001c2e002e000401d0811405516070410344a01c0310b08031030301100c040c00d640103206582552406036810481020a4420071000700024500c0403411443e00080b0070704103a0061002c051600075034010851880c0c0038040c154054191001001102d0342c5414880008008050503c00d6410036401c0501420a201004002c0c0c40818000d8096552506990303000b1500300c002400f4000840d030b040c61060000c244254072001e4a103100d04203c1d00c0c01d0b500e600425281515410140344400003038503051003020301b4003020b03541014058a203822035091030040e06204003070003802c8400d002404c0700090a00c845130001410000c10301 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 874871393 1250 874870143 874870147
    0x30f0b2a180a09091a04021f0207030c1404151a09010e0319030f03050702120a0512010e0a0605010503040c0905191a010806030f0604031202041a0417060c0409021c02 73
    0x3d060f902d01511401078180e074a51181101d400394000c1c4c40310b18620403580102014440c110800c21024074841e5100c04a04621a05c00c0110018000468010103486103243c82d05154a895041009803000d41c41c00304480c81c4004403c1107200c420000900160760b02c081700a48030558032004a070810000c0c0c0c06d10350f0611801040301980060300003d07038041c40c001d41c1d60120403286100141c06032941503603000c00591008481318002e07415080030348948001403800c01e182403c6030070030316214442a004012942880c4061000020091240e20014602170030600d086241945503036100c0d130114818880e03496120342c000707900800c090300f21040400c90b0030380400c041c0e00c881814002580b500404540400e029202103410307460000b1b00d003c446424900100250b40e42c0344d404440920440d021500019000e0002041b54409605800d070880840131f0220780f2545481010441d260a00e46824100e8001c00306000340d400c804c01c1118192007009402690348e40072003a20003221850742001d0540e0a00c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 874872643 1250 874871393 874871399
    0x30a0605010e010608041e061103090c0f041413080403150f05011a0315031e1c03060f03030516020406030308040c05010e010f0813080301030f0b2a180a 67
    0x540c80181a1140341a551030640e890314015502c103801901c0107000b01008010030000b45040410b10f101440c8148004240b10300584a1814181c0091314a080a601326420880090400148aa80c0204100e4003808a6030698041521f6003074050508120301d80380f0074041090043c2102168000c1d5803080398401c2e500304000c000d00c014414040d180c0042420a800021201400c4a113081d50700c05c2d400689243d03881c0e100c50301d585641010b88003500344c025542850303616206070303089800c0d100080300034040001c144165480803400c40d807428010305282c0030040c09801c0010a44c001a40e40c1070501966419860b54090400d50300040001d5010b41010408410180c0c041007650041c0e04c120300c109030950305c9400545085e800f9154050010302c2682e21740440a1048040c0e0760441034688518000c105c09880c0c40034154000d0b0015a440000e0365940000c120b0a0a92564040301e403300910804181c00601450501d00c0d8483c1080200c000c00c1180d0040324a01d54040104401000b20300310b2a0303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 874873893 1250 874872643 874872653
    0xe0312030108062a04060c0f0c060306061107060801030f050a0602030c0c0c030f03180a150309020a060f08070c03032408100926071b051c120f0e030a 66
    0x5088595070340b85082d003422034206184101c0d840302413080f400d5004c1c1c10681041d20031650a0b803101001e03909050b0a424003400301e00d04000000261041c1e50b004144079007031500140103a25200400e9040e0fa01000f0104482540901917178192503210000003001e02c142e041591401c00c010300007620f074a200100340900024400000c1111101d03c60a488100e04d030181050b4840b2609072001c0c1d080e400070010b00b0315030fa05049121050b510300800700312171140c8864950a031076040c0303020b540100b543c2e00004019071900724005002480c0b5450440ca6581e84c8500007040044044d00420900503424113035400c150081e04030b0401c0403c0c0c40c00c4079034520203c0d42442d04040071391242d40800d001d0080b030160090550b00900d081c454000040380305444403061040c0e0f4842504c0880300550b102400b0071800a0312409002c0004100c0b6104110000d09000c10406100801d10030600181c00506280e00041d25210358481100202c3c10445075016204806603044151201125858041d482c02242001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 874875143 1250 874873893 874873903
    0xf060c011a010e19060e0a0905100e01050907090303031107060903090e01080111030408090d021005190c030e0d0c08030f030405070803031b180a030f0b091c0e0312030108 75
    0x401c090b654410035000c1030003030080144082c0b01c6000740c2c0c124034200f0321425000b42c44401011402510100c00c051b9100034841c00c03242c050b40c803100c0340c48031400104222152058928050041110384140608110001a01041c00c41c80000d062648503510103125005100c19116103a400031018002c41d003062030014094040b0740500072101c6404000450121014440c01c500c1c0c81807941c0303c03460343e211500d031a1040d401091007207901100b141c42090058071041c00c5003220306c14a0302ca1030b464041c001c20042400720b602d18000100000015503c1c0840c1d40f099900506c02c0054440c48517003007280c200011096103a4000b80468400041c51124440e511401148103500079015254205d4444492545910050301c01900c0c80490002156105013004010820403035a400c9040f059104074002c100c0944503548143e03502100c0074982c0307061120b207020303451b03100f5042005050000c070f00030070b04140091180345440030001c5660b041ca4013914208040c0903a0104203c215489682d030b040229558 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 874876393 1250 874875143 874875191
    0x10207061b08030a05090f0c0f0108060303130605030103030318030c08090d0b070507060e1b01110c0a030812070201092111150106110a0f080d0906060801021306090e060f060c01 78
    0x26201c3c08198490144000c6188000c035440104019271040003840110303800000900300c90740c50300041154403c01c601250000000380515150241c4962640c100601154400c40e6070315500407281900c0800a544040c1200100e68840342d400d4a41c0080c10219181c8602004c00800e022207850900c850760740c001d400740041c103110745818041a03005001190b02d40c0c45500300310620a40c4020180c0da50340c000c600700c49800c88840111452005540000b4000303002d2a4026210044005120326918400440f103175441452400240a440d00700e68540d4a4100204401252072244898402082d44500550404014071404403104010809580b0281c28001c1c41100080745070328800444003100441c42d200304941015800110103416100c1700301640c40154122490356030b0b12003010010b01244503e0010300303a4000010303103600c0040010b802c2226990446020b1221502080000c20a481b450740d034400c00036243c41803e80030040101c0d04c02e0060043c941481d50800702003004824000d0851030903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 874877643 1250 874876393 874876411
    0x3070e040e07051201232e0510110709021605010617010e0d051222060c0f0905030a080c0c0901150f0f0c23101401060509010207061b08030a05 63
    0x41d84020f0b00c0440c2c00c076003484605c507194481e862803124410b840c1515051f441030f11110300e050007215401042600000c0c215001e144001c0b410310601042c14504000c1d419011035003002d100807481c8041003070b80c8072068032410032465000113480c001034241544407192181d120000340a0a41c4031600b8001c21456452081155880d2400942c0c0c1c4001c0040d043c200e201d2907850721854038581881300c0c01c04040c0184a80d0440d4215401d07005119003204000c505a40a40340000f4103424103003000302000f1103961007108004000c1d0b070500c00350350003083c1c91080d41d0b40560307546d1f92034010f455000d00f060500c1c182c2d254000586000000c210f0b00c500f020441ca04280d541c1c1d40c00c200090182501d19004d80140c03400000d0328464041c0025180c541d12400055080c03c003050612102c4c81c0c080d01d80208000c420620503281c1070484a02c2600c912030724003405141c10034a080c208070070f00007542c41f085441110108802121001c6950100080d124069600500b0590707491620cc800710000d04015240501 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 874878893 1250 874877643 874877659
    0x22e030204051003090c1e15020c01020c01080c0d150902070305040807090501060804081309020f0904110408030a1d030d0c150e0309061b0d09030203120304030e0603070e040e0705 79
    0x3e445101c1e115502d44240d21003007071005a4184507051556012491001003441540d00d4042407088104502c0c40003251294010080c1204a000080c20f0110501016040c0511942489a0703003000b981900d07840d103200c00e000222180c00544410724900c442d8081ca0443d03200003554000c0c198060b000f001a504417a00321021195a480c8900484200b481800001518840800e0000f209100103003605000d8511111003541ca408400c0102d0b440b80802c48861031000410003000d0406004051408010300f4200341020326242c0019180d208444c0200c007008a5182031030940200c1c000420341c10340c0c010b01284c0625003000c201810002c0354842c1a5035541200304118008003807400b605958200c84409582803403002014401e040d0440312140c200c2d030f484007010242c40031040100c419a200141e071042d250a14500515040981007002401800001c1042201182e041804007064600642d1030340e030b42e0790705c00c07404482340c0900d84685030b07005081819007400c541d80090700c0001d840342164120 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 874880143 1250 874878893 874878919
    0x227040309061d120114070504050f0301020f0f2a031e090d2d060c110d051210030204090c090b01090806060616050f011e020412022e03020405 63
    0x5281207800203540700a418520107001e002e410013041c1040e980090328008074508442d9102c20750900d004560001c001017010604020390315002c0003080007804280c000314a40786030303440703c1170300f900c100b551021241c403000134403030b6003092071810005100400f03424070440b4401829403030b502c0c1c0d40250040c200300210162503c50441c212401c807560b548000b00442c2050786d40d0b40c1c41850000c40a03966200c404092681c9110b480c2070591982056032090f60b0002c0c14005011014201d0001c0f0b0a491050740c0c801000c641707099400808491400414821800700f40d5655005005801c2c52a08002e41283c101011401044000305610003603503d039000074030440070304000440e500081e034402e01d0440e52100c804034015003802c1008010120108941802e030240c40d1303d640b440d000c1b105240c49400d0707569802801440c4d8061002a140701e1000c1019481c181c503100c14148158001c000183c42008103558503800104250f09900c820721040c4d10002880e000c040300900250810312510780a212400640 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 874881393 1250 874880143 874880147
    0xc1b1e022709010c0e181504180b0109020307052b180c0618031b24020712080703030c170a060e0c0309070e070507050a24060f12022704030906 63
    0x117081e10000544a81c14400300c0907250070071a800680030840c0c3c141c5410000b505519180520300d4010003849080000c00c4c1d080c03600e40180c1e00c059015404442c070501c24400190741c072400b00e030110303600e81601e20032011340c410f410502541000d40b0035003028a00302019405580801030141240d006030060a8080d64598050300c404c10182c0c1d05c0300c4504200c0c0424400106411801c021100b590003c68111343d80302c2980840b0550400100c801c840b65050208404941c1005142d005d480c0d0b40e00750508090566a0303100f00ca0150520040615494000e22640c95110f03401c3e108580c062150a1011424800140002407005000b005094180540042c0c130010040701184c1c0986e0f4150002d008903484c10303500b1342c4480c0000d030603002001010400c1c04080341040009241d89800749240d81c2d22030580004a5040076819000c1c121901e00f069410000402015113002c220b80c00031801c00c3c02d0420a200188028440c016034991540e8008a00c000860504010701d120354030980341d0340c8290b030701c0783c9003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 874882643 1250 874881393 874881407
    0x12110a0c05210c2803050127050c0405072610050102010b030601121403040b040f051008190b120f120c0d0c15020c010c1b1e022709010c 60
    0x701c00c0080d44450224829410101031383c01241074483c046181c42040e4414035032010215900c26a202d0b17445825030106490340d500d060030b0b50b861301d40e450094010144e99058480103030119461045903104000707207036117000300b06620101c0102001c1400e900c8614502941c403400907500034841f182074a001003010b50052044010201005008212a07803901651035a0326003010002c0303401e41100c00c81701402400c100080c0c0087c228035042691203504203181400d1f02c4100d94082881380105110000000d44c1000c001900511981141c004a0408000c8500500440040181c010450392081100e01801103260226070685509032440002600c0025046024004e450302d01034110341c0d54083d440340200d03900395500344100702000820a2001806080340c00c850a90700303469454460002c5041d80c844003048001840d5501e13420000b00c02e844000071244034050903e55a00c401080c201507507100343e10b485403070b6803d008545007081240c42052070201c00380d0743c000c00c81d03082024280903c1d005d540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 874883893 1250 874882643 874882699
    0x31419020a17100e07090e0c03061c060b090f1e070306151218020315071b0302010c0905030d090603090f0f0c0306060b03060904020f0a032003060f07090312110a0c05 73
    0x206031429803500052628662700183c101030740404290200c1e40080d41c49800d00c2c0c10a03000704000207800ea45030045c04500039004040c00d1f00703100c81d602080b46c014190310100186140c5440004500d544a110542c02803840381c02040c0170802240b00c28140c40d078007000741440703a03440300703014072001803d05400f000741400342c41d009515401050541c0100840c1740190b692120407131401c2840f00e46000301c1860301c40704101041c0c005035141d4030b01c046920303002100e8400074201a0020410b5680300e403002848035482c1e01a1000b0507464600c0c2d501800110102144c0c0c050b000300a541d00c02d1600e183c043c16070203007844101c642c0c1f41072500c000741007a110b60960b8458500035145102c9640c8980c20400d0354541c0c510230b02d1b80f01001c2d01c804804079a44560035092032032611030f4003032840c2c028400c043c644100101340c40c0504000d4810015442c9d48a645601120307440740e0b202c0d142760b80607201929101080391110300e003445030711300107000c2c440001c4100c01154000e82c2c0407207190350a0402802c0740e0f201c0740 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 874885143 1250 874883893 874883909
    0x1917180a2c1015050f03010b310603092a170106050d02150c07030b0105040e0106051011030c03031f1706040b0901060b160201031419020a17100e0709 66
    0x7040c10003a0700f07030300b2000414903841442c01c0362a110b83c1019400090f00203170001284140040f400c489542e6000840e482c04010f040c0d817442154041000d122001d02d41806024200760311041d00e4020800203515165180356900c5200411166140c0040c0e2268242e203d403401c1c2e90b09186031404244818400c01d81510000381048040306002c0c0c090109a0602c096030209040c2c1c104498424600140800d40c051440b9102c01d4009514100030002540d4240028100a034503241e001c04c210340c1d4001070560103001c5d90500c4008100c034500400d08500613103400700032078000001000140720414141d00200e00c0c1300060000410384401400d220740040c24003094860340150081000f007050305010740d921030008000424140d031140406841504030308000082880594441300441da00350085000f0280d035001d07010414038101007003c950004c808802c89a60780d0000f000071505100b0000310710f12007050044443d5904002100c0703079280569201c1d0101e18614070021070060740c03190b20002d0848030700c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 874886393 1250 874885143 874885171
    0xf06081c0e1804060c0507020301090f03140c0a11060909070807121b18080102070b0103023303100323210409150909141917180a2c 58
    0x5903450704c0040420400d01700c14001c082c499000141e40901400303071141d10a46d071102d6042c00c1c61034041d0000c90011044808440140078100b03101c403000600804950304980300d900b0300301106004c00c91521402d100300d41c01224010400502d10717007100601d0b00074443e559540310081040c408020480c2c0008800d2a0170302d2810f0020bc0c41f4a21842070351340101e0030b03d8200700b1525916804036003242d001e51700448280e600d035001081540b818003c034480300d5a0440b03082c00380800100c8414030340c103d10108910440f9001c0040b4040700800ea03d03104c045c5501c03d10303601400c0c0ca8003048450511010000840d94414521700302c0048203d05d460010001030104840d00309424503034040003410300c10300c240c04000c1285400048147e1139020f84290f00c1e0080b1208040741000780e2201c0d080001344083d0720801000303b42610009a036800618800780489040c1c030b500c2d100148039144541c60300f000300359880032103c10080b542180562100c031400c0039508100615030181c0a840d52404411900c0d21248421 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 874887643 1250 874886393 874886401
    0x9030c0d0c0f141f0b01030506030114040f0f0b24010e0f0105090409080d0903020d080907061d0d0302061029030408120903040609140906040f06081c0e18 68
    0x740d10198406070440305442ca14040034120310841c2c40e054920710584c1d901e80c0148040c0d075800d4454160442c02c290002d020451056904507400f0002034401400000300403685001d21074030b004050b041a600c901d0501c00c9092500300305428501f0080c00c0604100d00321005001c56000719520380c452000904184540c1c01440010342d001e0300129034064005844e101e0110004192000400d205807090400185103505c41c10000d141042c8070be1044148100c000c28006009000603c110807141c4500c1c04891180204140006090741c1074012504500e18105110170181c0108055100b03074038030507041111550714008000e024201c0c8442c5146541035070302c15a44400e04a00a40e8020300403401c40d4603001455690369038518040350802c0700ea0700003141c1800070687c0140140e0041c4030309485115103035004000150400f40c0a400d4a2013940d50b11606000b160700354008400410031601aa10a600d00303000d40000d801812072104001055210566068580a89214035810300000080b600b591 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 874888893 1250 874887643 874887653
    0x4030804140a0e0930041502063102040e010c0804031d13020a02031207020307020a270905011e05100503010603081c0b0a0b070318080316170309030c0d0c0f 69
    0x40c03040001004005c015100c3d28500915001000102414805c1c000702c804500c000a042c0140a020081d0130102c0302400c042d0342106c080c492030140c01d40580000340710003030320003e0010003841038405c082d0750070000034540c02a007200b4a144a40d003c1e44454110442500382078105d0803204100c260310070f019040c0e040c0b00d00c10a5025200c0c84640740112031030402c087d0b94207801410100c80a00040c2e00005201d01107080c003245200082c01540c0c00c20b0b03c0800c041c000c502d42201c0003603030712100030398a10040040c0320094200100c140b5030f2440c5d150406d00010b40101c007404044905489411244e400003c4c0c80c20148610300850340c01140301c0e407d11523201107050b42c00f211001504038154484902e50440d036561506403004141001540c1d03610801c034a0080c18540f24808601301c04d27080081c08104030b07940801229004e80c1c061103210742078240742c90000810808040782c1d02980c0c6000c801c200c014100000105480c00e4400c040300c0070800c40310030403224110980b20003082050503a10800001e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 874890143 1250 874888893 874888933
    0x110f071a090a03080c061504050f060607030917010c14130501050706110f030601180b09190b030c1201090c0e0904021c03050915071a0c04030804140a0e09 68
    0x65000b821205415503a4882c1c10041d0002480b1740c02907041141804040100d00d40b603448504c209a13014052031520002900340c08000622060150000141d0401058415a5102c5c00350108800c100d40020440601c07030300808100c1038400200d0041c0312605000e0100d0410b48030100081d614201c80c66090400442d0f0343e0300b04040c200d514030f03243c4640318406940103001e005000c1c80740030040e84a2904000040c92400ca1b03100c4d44401101c0004144903c01c101401c6032801602512036154003045001321410382a0164004c058103d000300900c850000f411000740810414041c0c02d240b640d80b42e403111021210079442220204980d82c00c19003207801d0140d80582d0150005042104420180c2c0c1401401d031040c00d030440c00940002103aa0940c0342c003201c22217003084d03810800380c1400034a0b0b554458a5080700c481143c1c1c0c508110018403100161350441c2d010307607401010251603a9584444040070003101000610491034a074010400800e101010741c440c6e6214002401301e91400e5a0b440944 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 874891393 1250 874890143 874890157
    0x206090f0328090b030c13050f030a1202100501180e070609031101170708091002070302030d051803040308030406111c0e1204240f0207092703110f071a 67
    0x312488201c00125482e40b100510b110b4281b9604441e600d48250025021910442d08031503c9a40d03150880b680d19100001c116900036802039104050508061040c4d20702150008004d6480f41020000b04411a9000f004078004a110000780b068038810071449032155124000d00000451080040020039400482c5c0002c440060420a5840c1140001c003c80c24100312030250114500d0701c203002100404009824030002d425004508000d815503009480740309280c4006111070311030b00415903403000b0103500c0402c10316400c1101e0742c4507501c1c50a030007950811a0203813001b80c03400b1154000800c00d041100c412130703082d50401c2c013010201581c00c1c00034030f0101c00c01c041c01e2291407150080c00c0240c10081c00601240340b003a0300d05001262130303d11070b490880c50324810000a0014100e179141c00103111420b80b40b00a4000c80c020b07083e295007107082030031000142460b61501108000707150308400ba07000c4020b0b251040c4c0c3d8030321070802803c6549003003505c42c0b00a04503032003030502c0540c040e0318003a281d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 874892643 1250 874891393 874891397
    0x1110d0c09050130020c03031b13030206030406110c0a0b07080c12190507020c0307090b010e1203070206130905060d080315040b06040b040509010e0103020a030201120e010c0206090f0328 82
    0x44d0b010070403956089030800000d0b540958000010b002032280582c034640b03c60995041030314502200400030300741030a4180300090107060007101042c00c010039030700025107501500d603800342c40f1003017002600e96407851580e0a803070b020500004110028443c420407031003221074803481e03841d01c84003a41e842078916000f80b450070b05655200c005000010705020341401100c4650013002490344c0b00042500348440c1d940850805458409440c0050340c2145401c2c1c41400b0841d2580784d45003241d200c3d00d0030b6110700c200084d401803000920003519050032a11500b561a18442040301d03a0f039a2003407002800302c0071005044864244002000a491001507a21084010b800803414060810110304140c02640200135100401710b01440301e400c208500500400001c0c0800449514607000b0461401890102904000000492603150802600079144009507413008029145035078034000e45a88080d101941140200781007000302003c00030503100c1c502e902064400001d010f01c007031044d100c01307000d180100b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 874893893 1250 874892643 874892717
    0x41a1b2107080d0c02030d27121b0615080d0822020319050111131806171c033608030411010e0a03050309150c01110d0c090501 56
    0x1002e503c490080366031340a040c0d0002c50722140030603509415501106240b2200900c4100006c4e00c0c3d4048003018480c56070400308030342c810380c0c008004480c128007052001404c13844001d0448104191075106042c8404001c211907101030b250641b450701d82881f07021660006040c0c1010451080c1c82d00048004e00c0943c070380001015060740d010030304240440940d040c40498155024080c03100a01505140200c00710001c0c0c80d14003001c28150418205010300d03044900b01c1112410407190952051000e0a00fa5080c1d40e08404126400c5990741842522104110b8403201d00c20082030080c05141c44131894003940041480114601320342120160100802c1116141021804104000025400b46020f508c800201c0c1320311100240c105841c5200390350040d203903290704002041001c070940340100c4d000ca50241600708030040d02e903001d01440e5600d003030039483c0c028401c502409220041c400c1400d110828070000000c10b10a07502030b081445100d0101e01040c807040090140000b03240c0c0e032941c20a610036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 874895143 1250 874893893 874893907
    0x6070215190503040c0806190f27060b1e040b060d0c0c050606060301060c1121010c08010509040203120f130e010611072108041a1b210708 61
    0x341800754150484011074000000e12050206244207000600450307001000c4034200019405981481c0c1d1186640f61640e6020404000b03183c0d410161080c0c04015041d40402a00902d41c0f10700d481c002030844006207481c000c21100d04240d03168a1240054240c80a201900d010510001d03213200c0c0318096101d0000c00c0343d40c1180056204d24081690150ba031008561502e1030198684403000d0300861160f013040c00100041d99000e10f0249480b503012142000084400d004544030344504070200b11980c545258140d074180c0154400f080741120769a41c801c82e644d072030080c443c00b030009440203034054120b281018441120f00008115142d130f85412546403000c00d03141302ca000c41440d0003805003501c1340d0004104481e0b0240c070b00d12150f018100904042c40ca8201344c5100490040440392042081c02c0c40b54061000a00640d0010702c3d04c040045900c03031075184402410340c070011188031005180d0aa40061450005032582070b030b41820078400031001c43e0301308c040b00e0307400c8a08210380c00d900c01c000760 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 874896393 1250 874895143 874895167
    0xf2c1f1e0905090703060f0e01051c030c02031f14060f010e0a030b090618030c0c19090905060a18050706051303021c020f0d05120304050f030408030a1d06070215 71
    0x10f413144000c0d50b0001002401c0035814101440305030721201040c2d46180c014005d90b6181c000441d508a1000e19002d030301596032809507003411040ca806540f501030002c0481c1c04040d980320b043c010403d69074007080031501d01c00108448000a0b18a41d0f00f1000900003000154090300e00d402c0050801842c00c4505031f9680d44014074040e04480c150b01310b0f0001c2c418010744000725081007042a40950103182482180e4003c0c5503a18242c00b40c03035124000210310035020100c0264560041d100f0984288030760243e508115569400a42d220100076103800505011081d506826001142d4004003908030b641c54004102d603c4e801c24410b402e80502c4440300000140c0c3c901039010f40f00c103e2940081e40c0a4030900400c210090410300c0305004a40e41c0c803216000030008203460305500007500ae06500c2c0c0e100c0d410040d00e00102c0e030fa4100028840001c020403c07440020140c86182c480b6604d010391310459103170f6841012001f21f00d141c0c111f01c05104190052a010102c441c0360242c0c1a00607003881400044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 874897643 1250 874896393 874896409
    0x31803030609060b1c0c110f07050a0506040303050f0901051309090512040b07230d0903140703080d1a0a0f0603060506070506070f2c1f1e0905 63
    0x4501190307036000100006031050040000800f0354070011414201a0942400b1101240c400000441e5440112240d110302a0042c03003c921028070443d426000d6289000b65a01828017482e441102022800545450500111004c1d694599149070800103440310540080e00072036212414448140440240c1056680c1e0027002070070181004200c2c90101c0c2000c40c00d10100c204843c10780340c4200820700c6400040c3c0d0450341c2665001480301d4080c0318201c80c22a000c0c0e00c100600c0306034000c102510782844c0d808030011003509d00541c5032080e02030b10340085598400043c03200825a25003440f0344a9403c0391540402000000b91080b8164a20610000b8039022003680200340e02c50740040040c0075059141c80351101505003078611520709019500c85903920b0700b0081c4160f0400c842e18151060140c850310340058410810fa084540c4e405614126180c400c40881400d4000e05441c0031880b14464000c07400c007016a032a85036015403070841180d00551010b0050400203000c2c035042d00260340c0e01d440306 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 874898893 1250 874897643 874897691
    0x1140a050a0f06031101261e0106030b21030919080106080c0901050f010909020a05091f0903030806031e07030c0b120a0f0e1e06010501141903 63
    0x900103028501410244101e4440361a1440c2e89443d115080c00011a00c4028140706442400c1c03032840d140c00b0700001c0b004800c6900704041d0300207a5500340481d019440300d042c0d04400785503035031504680c0c07100b01c101c1c02c170743d00e24012030f034460865000300d0030700031204020040342c0562505503440d00c40084082050314074003883d000c080000041c0b00f00141c60003885908040e03d00380000d81000001340000451110041c0106071049440102c0c03884c0980c05030000c00010701200d034003952244000d00d40a07246070051501c05000d400080b5600c0710707540401d6408002048140c84000b047e509603202207502140041c2010f805228102c280d41c00170201c041d00d420051040c100070306c001c50451034601c80c8010030b81e00106e100f180500c001040565400002caa00c07185040e800200b540000d184500a07054103003159945000e200f201c05024514480042410b0442e18100c1e44103903600d80044030911103801c080b40d0000001d011498000814160150500685140114101071111451178403140d82c40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 874900143 1250 874898893 874898911
    0x141c0e030a17060f0315060607020d0602030618040503071202101a100504030321060b0a0c06051605040b160204050c07120203030c0301090f110301120219060e0904050114 75
    0x701004690b40b8001921a800750060b10440388244c502070101e507a51600040c4070155000c0c200006541c0c0c0c88990a40d401903070018a180c41c03030051401c1c8031000707500940c1c40c1030060740c0c4480c000885110701001035010b150b01c0001103150041544900d4030310045450b44000b1401001c0d5034105021190044040c800030003580070403880c400408220742d411901003814180320040c001040802d8100c500100400c0310000c803c9012560701b4262030044c0000d4005103032021005c00c008404551081c00030705810310a040030400380d168000b03404122041105401d000800801042c003400903031a01400075288201310680e40804160300040030381d40120307009141584082002c4040c45030121120140c0301c002d0000d1850360070016110a02807005010b1030104503224008802c001c08140e100344501383d8005d0b019616961101240c0010a0944000b039211700403003400c00030b44101c52401101262025251500d00402e940c0500a15210041c41a82c1d95581c542c0c0304902d580300c506805100301888 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 874901393 1250 874900143 874900157
    0x307050a0b0936041b2d0513021c050a053c090a0501060801020a12020f0414120d030506040f18141218010f141c0e030a 53
    0x2040c2408803240310183c1c0c10321a00503c0c0c038111507901d282c501c50360307140d2090960400583e456050400c101100008480c0d030100b907000300040c0c102e100c2c040c5800001511410074105188078200b40ca10b000e004c3c01240d9100140c80e100d000c008502d5801480128050311011000c10620070032181102d0044801e0009540c80e2020822005904a901c000d00c4c0a02129000060f0701c902c3e91200c41c801d19103035401c1c50b8000c20007207640010100a07040040e64000000e11019440700e2816002c0d4002e5040c070008a001c42d0b44490f40c2c02c900c0d000342c030200380102ca5003508080c0741c18402c0c0f8400c001cac00d0780d550700283c0c030750b080202e0450b080c050402c1c02c20706510081200e0030108140300468600109000c5d80d18035140400b100c550342c108020780071581010300303031041700d11104a132414001040c02c3c1d05229940080d0130301003180c08a076441ca9911098903944030490303031400c1c250390b0140317441c603400c00c1003100308078020a1a4040b20304103050310b0641c9000a1102d1201085c40c6154040d407006808038813a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 874902643 1250 874901393 874901407
    0xa1406010e1308030c070f02031c0e061206040c03090503040e22050604030e0a170a140c0603010b0a03270c0603023603030301150906140702010e0307050a0b 69
    0x501d0700e400c1d810010000c400c40d00c200098540c4800c9020280240241ea50009041c005014103003201c924000d40007802d83c2c4001e82034545000b81c041d02a0200c07004a400c80e03040301414038006054505081128441e04001c0c0d455108000003020407009074024559124201c50201c2d00410203400580b4400c43c19150900701103100e20300618509104ca52a180078140120000d607000c282c1d2034001d907041c00c00e400b4007001c0100140c0300766441e8105106944130b6000b601026540081d02c0b0708254000d0901c1820b60490a0060740c440c5030009500d40c10034001c00040241d58600f01c010070400400d441d0001c2c000c8940e4121070311f14480440c510b0002c04044040c001030180088220006106604003180b0b0030440c1000804249503000d00c0304001c0020714410309075019900b23100080200002e042d40d0743c81d038495031120305500c001c00360040020021540800d03001d000d1410308a86007800700c0d00360700708140c690045402c00440e0f02002d415014503000003403a9110580c0035009000f129030038a0300c0d012 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 874903893 1250 874902643 874902659
    0x40605030912070305070b060a030b070201140a150506210112110906030705120102070203010603031e0801140607060b03010c030e0d02010209130b0114070606050f10020607030e0a140601 82
    0xd180c2001482c464420020240007a40040440350000d031701c0881c6082c0c5035941800103c4042c0c041c1c0c000b5040c006644100084542d040d40320f007846450649140140b9290030303144008a601d403484030f070004205a5030a101620b0410064600c21140401001258400c030318485840c0d02c0a90143c01b040b00c501144000f00541102806103102069640070424a400000240e07684030a200d0a4001d240b0b940080e0029502901141d0196401070002d203c5250b0b245070040608529214040c45400c404580c00c0e640703880383c0140381c1294000041e030050340000c2400c0060a901104080751036540d12443e0100c01c1e00c007802060781000481d03c0c005030014071550748071308200e0910303410821a481044651a42c3c0e0b18542307020080c0c00c03240f100140c4080c3c1ca00050380c0c012a242a44040600082400d004000d41c981001d404d49006441d03040620ba4a1014011a482c2642d03035500580c0001c40054246031095025410403465a4121108040e03151603401014a001352044007030380002c001800180703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 874905143 1250 874903893 874903903
    0x507060c1101230913020301290a050904050a0605030a1a01060203091e0d0b040b043008100b04030302070e06011b030c020a0f0b03060414060d06090203120406050309 73
    0x520a09200405526814000440340440c01245034081c2c00132410714100e07100c2d00503490030024103038021540d03940c442d2441c076611012140100184414103203181e0700303111f01c0c1c02540d107403100d00d4035240d00788a01d041c20071000d80b070010010810641d41e0780c80000c0542c1d040000d64809800340d030200044002030b40e08025240e8050300b091007590f0040248801e00e4503100041c960440100580c0101c01d6804030008040c02c000f80c0000c2c20055000040c0300c28002c6a005a500651003200001040036490800c000c5c8080c0105051100b65000203800c4101030045060517882103030600010b044607150704000302240c0041d0815001a0311210081c1705101031141c485130818424209100c911080702d071800c851100302074004042101c50f80c00241152200c003200e0001d03002d858865041241c0340c1c05810300a030001c0b43e189104071308040d42000e80c80d0f00303609201d01801014083c0d00760662151515009400411001c9801d4880c0e00c00804005551201410140a8981d50280d580c10281d060794545 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 874906393 1250 874905143 874905173
    0x90d0602180423040c030606060f0207060e0112021602150703080a0e0d0f020f010524010309110f0a09110415082406090415080d14040614070507060c 66
    0x8500d0081440340107001c100820b04654905a000fa0b100c1da42d6162503000341c00103602c028145400c0005c04989035070170200017516030600b0350898444580c0d40c1c408a90601c80307245000e02046281518055024142c1c00504156030b0954005e030052041c0c1c0d01048168551424202c2d4150b000301d860801c0603804002c086e08446405014080c0701d5600f2406515048501c0b0400c0900c50f0500c000b0030464000d1091160350014800200158500300780200603216040c1141d4030161818042d0300038642c000e1042c0001207402003203c0210030141c00c1446150002d003200f040d8490074070080040c05014a0042d103a030f103615540c00350744880c0f400c0300211000c1110090030050103c3c6000b04802080c2c20482d103826245d803140c4025000755581e0200320395100300002e55030894103159207101e8140c040c0f008101181c14260071141ca01000300e03001c5841d003440c1c0d10000c1e000720080004120042c4550712101c0c12a00c800011460f100c0350380e8406203016100da11000100355a41e9000042c4602c001c0302c6509 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 874907643 1250 874906393 874906399
    0x11100302220312081003061a040e0d0f030e07031722030f06090c0e130c0f05010c060e070b0c060115050901301a0a05030706020a1106090d060218 64
    0x3682d041d5038030036608180f001480010404103a000491710086000c02c4c00c002c581024040048422210f55801c54000e0080324501950a04041241002000070318201088083e50389410800048400f100541030b43c2d805540c0c01c1c0f08118000c008543c1080e80110a09052010155100b1842581085510b80d480c288141c00840d8142000480c0f0000310401e007266000c10000f800b62528506100c40508a07000040c0540103201008028021100400c903ca40a55181d841042c0d80b014510a03803529070050301e0000e194500e4034800240030340c0008242c40200015108110b84800e00c40c0d207503801402e002e070f085074080c0004100b0780c8247d01d454000240d49181151400c24040d00107001c4940c42d00c4501c11301100d100305500e007400d00c0d4403540da200e2072810041c0a5610599000528040c121950030703c11100d10b0340010b110325002802404888d81600039020303841d029120039609090780d48426410003820014075106a954040d20010903104210058450040c09000c44840720072180b402c0c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 874908893 1250 874907643 874907707
    0x9060105190302130b0418090c12030e090901110d050c09030a08130501020a030e10021c02010608060903130312051c05073c030b12010504021f050406080411100302 72
    0x414400707031144d00040c7c01009400840c40f240b40307183c5092511195032003200325410048403030702059400074080510180c212408034113a00c1d00c0c20b00078200c6000441c40100c80c80100440740003244c6582100b60703c050b808680d24200307a075000209003041d548803800c072650b040c0003414080300161401c1070380260000303200078400d855066038098040d040c8078002c940b00d40c4207400070003840c901c01c01c0b03029050104400d04410000c0602c00103406042c06005680031030240e100001c05102001054962203102c0e0205004518919103c944c54840c05030640706c2045000c2246441400b1400329116684c2d01ea090005410300d0012001440c0a02c005520a90054000100010f80b00990103400e003070000510b0511201c6902101a0300509207615115080600c09011240154040d4016407103a0700035940c2d11040d10008004181100000040d0f101081040c0f00a00415115100003507101d4401e0800d04201c4007007000007030801c4030b01c0081000183e00000c401c0100b803140314024030004800d6561b0f43d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 874910143 1250 874908893 874908899
    0x90723041b0c15110324040f052202060901050c071203080411100c080a200304051011100b010522060908010207021c03170c0706151409060105190302130b04 69
    0x10b40c4c03c0c4006080b1400d00d0500c140d91030b0302c403030440303c0c0c51b03010f20801441004207844035449003001d050101c51a05030b50a07907060640700c180100b0454044254010440340c07900c0440c03001502d09401441e0702440901c41c51102085003124020301c5d1809500946030708101d882c1c1840c0c000404100700704084d0044045001c100c8506400a01d040c0b081944820707000d40350304403214212a2400c0c03146c0c1c20b0b2040340400074050421480400244140c0d40d0640301404600b903480803d075000344081c60301054540c13213580d11005000440e445103400d1401450100d1900a01c0300500c0c10f00f1450381c0a0201c0e4200700c00b410000d164000980d0001042414029428402c1a40020742151030b0051304a040c07050f003103e940c0416104236298201120703554004040390034140211040e80d0084101140d006240204a045c41c240180c00c6408803034200080c880e280310b205c0144801c0b21009000745052000600c01032140301240d002681041e0229500183c41d0002d0a54026000400fa03120301d000510400080c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 874911393 1250 874910143 874910171
    0x50f101407030c050d060b04031b05130e03040b0d0b040b0f01054e01090605220f020301080c2103040b1c0c0e0108090723041b0c15 58
    0x46640001c4074200003c4418841e14191020310610303603071300c040c24507110011a8406041018209690280b1850098003030640440c012800250140c84d42c00b06162600600c12020f5821010386130000400b42d0b41010340e22a0880500d030004484c156480b52a17240c00c3c0c1041c202407050071301032030b011110903a83d02810400640340c0d1203003440004040f60040160480d29085507403414044194000c051011462200040b001103081043e86980881c260000201084a801071206a6000805c2100f400100c492401e661862443e866903645072a03004280340d00e412403028500820340c0c81c1c0540f00a8140400b049031051145e00006030115580a00c1400f10303030000140e600b550900c400d500da4441c0860000207201c40c1c490100007580d41000501c092295000a000108010030b8841000c01e84036849426200c01840c06200c2c000c038032002a05002d84030740d0302e00d80040b9001030000240f00c034024800d4440c8041504003040410b104400c0c007000c0110314070b002f6112074070344441009046600e00725 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 874912643 1250 874911393 874911431
    0xe031501030209130f0c080a0b10051003270b060307051503010905070210020301180b01030903020d031a0603040605010302030607091208030a110c060613020a0e130605030307050f10 80
    0x2401012104d100a210170006078051240140790800b12070f8007456581c0c4112030361490b8050080f03601d2100da50120740c07880c00400961040c4d1b03000420301c801d03108000c40304800a00b5000d85082d03034202e5921b440c800220804002010a0340101c0e03c10200d49002c00030300d0315000b00e0b58403444c011090202a444c01d803140c00144d9054401000d408901078a44c000c04034074100025481c0e000340b03440040006890803500c1c20180c5200035204081c4108d0751601d0040d422a00304e2803015015801c111b00001b00c82d4460b90110002840301002c10501404520104030f41d600102e5044410b07656450052080d441e0400002c1d41c0f001ca02d2401c12416800d101013040410713010000107007802e20100c0850b103450003a07044003102c904c0a444603500c0705201204107079130340c506981080c020b00402c0441c03020303003400e8002c507455a6029101c90051188036424001a59600c0d9210341c1d19a90781c440c003195a0390180001c004250052000744400c0002c40c00607402c1c103007001d02c1059032a1515010101e07010100344 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 874913893 1250 874912643 874912651
    0x90a0201050403110102281e030816090f090204031509080406032003160909020c120c010608010e0a03030b030102090a05060a02160f2d23040c0e031501030209 70
    0xa20342444401341c00050380751116107102068a034080f014001e82d400c42008543d04070350300610120030a00c289180041030211900005000256030314000f402c3e0300c0c400c4505202c100c3d901d00d00700704055620246529420321540100c0405034000404000340501c4850152010a4049042206001e6561280700c5c03882603115a00030306898030191030f075000300b0461030140300e4840d030055607803450400d2011080c00c200c04092030105100c00300129446200340f00351070b0301805582c01040030440e01d44041000350405904106e5640d00d440020484840a000e015207031b4045400400100f045c5107005000c0c0d580c038841060027684140801c0140369a11646681210400c0c1e601940d501d1690704124140801e484410420080f14240040d0180901d03051034200e40410720007180c5c4020314030f0705c0d18002c040921402c202c0c2010030b0003800000404004040d10f4110a08807a82a04030200894281d40c109003403c004070740301000c841540c0c1401d004022000f84000c1c54a0025811170f4002851998003070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 874915143 1250 874913893 874913903
    0x312010b25060906060f26071211030a12120e060705030408160804080f030405030a020609120141070e0d060f0b1008100303081e1608090a0201050403 66
    0x100c00c1c042804180d50000340d105802c400c042c0702c0c80307071100c05610518505100c4c460510b00310f04090040803000e48010411103640c803016000c450310307140502081814910b81500c8002d8010540c60517a5010407160960500ca500c01d007921001964000d01a504c000c88401d0b00541000080f20741c290b400302cbe69650120107414141d40741e07282c1c0c1c1071050041c09940c04154200340c001040209001c604009001101c103102c04441a0070b801e07030401d0740c890250f132041503015400700c80d1010040c0b501d10003505001c2006810541c59122a14030340c1e007036840301400054801130300d84011040400c0000e9000303101550340d500d511003460902a0680d03010300140450100440072030458541e50391900e60100c140d40144042c4126401141c0c000010400b11140c03612440048030f050b1000303405404198894840141c101c08094a552020f8804810003051340d601e501910205140e82900c24000c82c1c044c84002c10414940220341030081c2010784040c103815507607800a00440d0060303030300a04940175240d03c9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 874916393 1250 874915143 874915207
    0xd05030a080c090607060509060601050403020901150c02060a030b010e01090b030a09050309060715050906090307030809070f120b010e06100e04020f04032108040f020d03200312010b 80
    0x104200c1d0400d01403d00d64a42c01003000031800c0a004164100c240500c60b0714082e655540c42e4840191094403075880000c0d00100c0c50750040103070701d140702900c1e6000781984c01e00081800c0070340c0c00550140e01c85050701c07004c20f9032030368464019640003005ca4240042800d00455040c240130740c110003400001c2c407104a03141c0b1441c0c02c0e81004018002d603220001c014240e030f500d03450507162864101c012200d0a1a40c2490000001c0b035162f0001a114000c8a18001541ca00303102c41c0c40464450800070701349400f9101c0d4840c00505101c402220000410203030140c01504a040d10f8800302c00201030340321742c100b60019410f02a942e80c40c080b03000703c91072540c201101e80c12100c002090280c0a1021000c50741880400c002041c0101c0c4024040280e60040b0f0030740ca240d40c100c1c41680c846400392001340c03c268000303612030010304250500d200c03010300030b0030101640da01c0e0881003c081096000030a01d6a08045400c416020301050391901404206230340c01d04000014201a40c912000400e210b080c401c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 874917643 1250 874916393 874916401
    0xd02090612010204171b0127030f080703030c0f021b0103091e03090608010b25050f0c01020d02060402130510080303100e01081b1203120f150d05030a08 67
    0x1030241e001c80c030380307a080020b6494035aa12401000340ca142d801600160280071210118400e02200755114100161a584540888090b000120b0720b1144200000e007554102c010011a40316482c00b840c6502c02e0b0401d0b6558200d80c0307030050035100040700e500c05000500c0081c0700301c0da4002c1128013102d000070b0b402c211240100170040b0094244000e0140000b0041c210344020410100200110503000c1d0300c50b94001070343c461080703c2800092203003824680c82401441c4c0156118045820210140c00500a10380c0f80384d22038a0400b00352100c0086c09502c01d061009180d6018001c4440c000b100b80043c154510386a0040b40ba42001d0003040c166441d42c6500040d0f83c1007144c81d4400180601e5400c0701e4481c038090301e001c0707080b40175402148148482680001042080001c1c0b07581412688140051801091420300000c1c01c860101554240001e0040403610036172501c41c14031604405070380c5540c40c185040842c3e03802c1c0c013402ca40750003107049108140201d0000000c0381e8100c1450b107005011962 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 874918893 1250 874917643 874917649
    0x9060f04020d091506050307291b1c090f030503040308130f060504050915012c130603110d050a030e0307180e06060306060a0603091e1b05060304020d020906 69
    0xf6594004003a040c039403052070380c0704605a204c08140c0c0c00540850304d03810788606842c1030140072440d454600302c401107441000207156102038410040c0c5281d0400c01315400c541050309101542031002044002c0e0740d45113a01c6030380b0a1084001309100542c1035121804d5032509905d0b445a4000034112040003d00394484040c40c04654005150030b11000103503a803103400083c0554058400c20344104050780106801c449040d000f0311407000c058451000410240d52a00d145d0301c4c19048990030080010741000c0c80f5114044000240311540900007190f90661403c1481080e900d45440c0c099071a0071020b100041c000281c0d84100da80505083c4541010080003d19002d6140c01481c4e90091124201c09245110740100c2040c007540e1061700c03401d507243d409160f40c0700e1080329195441b0b0140502002200d02035408142e65500441071a10a11440400d080c084c0300444001c03955000180554040c40c010a00880d0103010f040310220f2a508040d000285200024136001e44120344820100d0b66a503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 874920143 1250 874918893 874918901
    0xb090d080c0f0412110a15122a020703080307050a02012901120e07030f0204050f06060d021803030304030e0909030703090e0c1608031008060907031101090b040b03070e09060f04020d 80
    0xd030b004007040c6e20951500c069a1a0358003101d0400003041c4c0e0300219002d800c01a0140000800e036043c5000c3d00810300c0c1c0004994440c0002e844030a6000b04000403000c85c0d03074800118411003c40e22080d58520358800000e00310b821131140c0402045e00760490f0040f4546c0c0c00e079200c02d68502440e1038001d040080c20360000900b0a52079043c001e2084034000410071040c0360034440f425000b01c408000039a41c002e00c6010350081110070550098040204a05407041940906165900c96043e180d034020f0302d00100e07183d0b40c4140c4068010603109451a20180b400041042c3d0080700c440186051150aa070007612100030b6010301c1032103d0603d00054001e044100550300c10b80101d0b11402e414110505105509074000c3c0c0f1200003107285110040780e89407000804501851a4400070003109183d9203034800c8a4a083c1503182c100181f19000084d0b040c80d0300050801344c031501d0a081d5580c181802c01400c110911110a40a120314104220065a0b00042241c1540003a680541c1d40d402640c0844018 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 874921393 1250 874920143 874920173
    0x501050912241305070b16020901031a0c0a05250506180601090614040506040e100c030f060b1b011508150a14040f050a0b090d080c0f0412 61
    0x10b10038801081c409040300c890741c1d4140c0c030280315100c001d511600707030083e0550209000600b43da0710840081001c1c2104000601c241c260384144440000c01a60001302031f50130a078000c0c1d8520f91903403c00040c120744c10550355000100c40b01168981040740d00050158014030b4803038004280000e1003400c2400f18212460302890740301056900030319103003110010644420515010511507880049402c1409209620541c3c02408031142603107401001c00c4090800207012031b4102d40c548088940720340c1d00304206400040c400d6000b0482089845004085425480f42c2980c561308011003040850000c400700c0382d8150700c4a00300701c13840700c07082409801342010018801810f50700300c2001408103c04212076005264502025001d42c40d207010340c2c8252800031280c0702110401401040002c0c111490465101d88660b05507400c2c6041620380701c1080d407003119107058540048050340d0400c0d91001884d5031001041d420786042c140f0030542900280698058400f000000304040070502c6494010401a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 874922643 1250 874921393 874921429
    0x7060f020a080403140a0c020904051603030215060405100b1b0316140d2c0306070c020f091017070506040801020403120e060d02030604090f1101020708150105010509 73
    0x901e400c41c550082030007004640603070006000038011024140588112040000150350340d402c42c803180d8081180340d14001d0401c4880e40301d0342081c1581452502c5011000310b010350040d100140c07042124404d800002000c881c883c4d480c0c1400c01ca0550464683c990903205030220315610f821060881c05142c0030300c901110007511001c00c1917003403e24061900101e8600c038000d40c0755207000b15081c80b55a40304003900c2e50042006a10281070300c51a441d1038480c990500200ccc4039800f070500c1c02090400105441400015040880c0c2c541582802403e0042d0a0b5040d80c03403685a20744502e1481e264481802034140300030030286149448001040184054040240816540c03581d406040f8002e5010f4882203c50031084120784207000c2c000c10441500700405003003189010b90740b0803041c0080d40000c11856002c1d130740f00343c4000403510b404908242240f10360320400c440900c05001900d00304041d488141c2551040301024100900f141e5418110307070302030800c075403281d000f1000200301d10410229010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 874923893 1250 874922643 874922647
    0xf04080d0501080705040f02030c0414180f1e0402130528090605060603010305120a090306021b011b17090c030d020106051e011d010e03010218040f06050307030807060f02 75
    0x205900080360813022130f001202c04103c0381c42014003040a0340011a0b01111044051008000c0b10400340384d444410302009112013485200004038026100041d41e07a0210410030b0003c020880201c8444046910751086081c0c0c1b491810341c4c0002c48051610284c46086c9480c0e134003180c0e0041c5115184880120603144138080250030301d0b509001080503d8042d518141000040f810034144001200d050300d412401624a034021000c1e80c03885580b060340034604111203d040000402e00c1d43c40603200081807481c685803a00d200c2440300c0d0035541c0c2440400e40400190f070084070b40d60303033120a021070340488518582e819562101460308000b1040c0030144c0500034018103221040c1c0c19401032050302c00c111360040c504050f0600c62100740341150f2840b408109581100304003040c2051010740200d074149440144c2840d0140440d09a80100c900100080219040303c1c070186054050500c0220b07036428208111440c1c10002943c2d00c005100c09002942c0018400f02440019000303080801d052502c155 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 874925143 1250 874923893 874923899
    0x8060a0b120a2108040f060510090603051b10450f0f050a0e0a0b040204120b010e04110d0f0206120402010e011e121b0903021305010303080f04080d0501 67
    0x1c03100210046583e060f90072076114066025018803101406250030403242c404d03031206030740d070b1400401000e000608040740441c00001c07000300c18007402010754800d00c0135140d500c0d00c65440458400c01c1c110703801c0c42120010170720040290301c031900d000041890540303004d0304140c25808400821050054030040240c40ca8510f19240030900208101c83c001100d58045070798401220040c01114011307582d2003100c4d0241000044003581203107030850b21402c070000710a8241c1001904980c015071011100002d00310440052001c0b82c515580104000110101e052410345c0e80d084504107040c41c11446003404c2c00814007031007810a142c1000344e40c09008a07998000d1300c0101004c1101c01c0b0b40403400105040c01e0400c00754400c10b01408902504e0186040c038562415090310103261110090300b40c2d66440e0702c00123181d40302c2e000750400444907459071200b072401d500600942482d1260313290001030802c0c00400002c0d03404540564400301c107414000d4540c683c0c0c50907613500c1c440d030408041480d00b498004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 874926393 1250 874925143 874925153
    0x2a0219030b06130b0319050c031006140604180c1b1a06040c081602101103150616030302090d0b07110f07140d0503040b1201030501060501030608060a0b120a 69
    0x540503603811182c6050f480810200c40050790704200907590140c000c651804546148861090200c40c400d500740d5002040344d001180c9400c0c0113107801c11080340c4461080204c03881000c20b01c0303803000080c0e034814907207418081c1541d410784907204c00803045681e03044c041c0c0580c0c1c480c1000761420b030260216803804154500b01070701e6842c0110807c00d2600705c400301107042e0b80340601c10101214010f480380e242ca0b945a45c2d28540034032072001804150700440d0720342640d000e40f0303125812140e598818869224101141d05d041c507040e55003440c1d030264104201545e0910507009407600c4541d85880c015a4804c4d4170404a00c8020030064020000307070412050082c015088040718540c01c000c1000c032040390000106040d034800e40c43c03103000f1098064400d461503608001c001803244e1030094085a142c00c0d501c90302e42c0500d511a00085003003102e03410061040120038007600c002803400346000c1c09071071300b00240507444550107094800301d559101024200c90302c8140821460700d95007015151800424281 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 874927643 1250 874926393 874926413
    0xf04060e0a0b032a0409090b0a0c090b030c0901300515060d23070207180501180207030306030203011b350414060411040c2a021903 58
    0x600351180c012030750086205000d90040d28031403040c2c0c5074503818001d81d141ca8070f10061070104881c5081d40c010017010820006034080c81200500ca45e6a6800c58906a690310b4103d0b14000356000800840c001d040003801c1c211425a0707008a590003619550b0180a0b005a40041d000254204400f40301c1c51402005048840700b03046240171200148016503035107074040b00e162190300300315a100c81c080c04103d00ca001d81e030380170a44440c180090340c91b241840b46010f030346206080310040e00603808854148541d42e07908441c00f22807a801070040c003c6504205d007041d0416241d0b91401c0455602259203801e2500c241c204c0c000454001c0d0081040302c00407604140c0c0320700300185820101d0b11700031100807403410900d4030100b020240d80e012001eaa040003860f8503008000341041c3d540e81c61881501c0c1c00c1d054248050b40c0258410035203001480c00302000d000550f900c01d46020140110316034110364400340c0c514428007000c03d041c00034040b40100c0c4002600700c0c500808440c07070704030403640100402c0800a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 874928893 1250 874927643 874927667
    0x1203061e090a05160309020109092003040c150e010203040e040305070f0c0f140907081e250c0b01030b070c0501060828240912080711070803160501020f0406 69
    0x82180c90320b04c2c00f820194140d40181c04000c0c00248071200401001103280e0006400e00e450102c0030411002c0b2070b850b211303181c20540c0c2c00d9448c20100c040820203032244003410800d01400382000450316143ca0b001070f499008038481e0301c2d902c0c0032007000070f42014820070848140c20b44c405c0031483c1c819001d040c000c4200c10305016400788440010400f05000c10603080c0003240c106c000742402096030760181f040341d40c104080c0143c5552401c0b91304940000d024010300512880300c0040d42409190200911082071018403039170b2050003510200000030884081c0b8083c1074941001040069444010048820703c112210150031546441d101007054003010a50885a5141c910600c103102040c1c0c04407091031350250001420b51000d820650340e116100d039050499061129000240300303240da00c0301d17040849030018000005150700204002c0039009010361301c080c5885401400480e05000c29580d4078480d0541c500d15224818084404000094040f0f034000828a004c2d10b40700ea540e028060b0007120086 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 874930143 1250 874928893 874928911
    0x1030606080a051e0f15040507050a14040b06090307030303200a090e0a02120a14010807150818070e0103050616080a1515201203061e090a05 62
    0x240000801c00030004110310b03455080760190540c101800c1c4c0b4411580c840400c400782d540945207601400c0b440c1071002c40c99203c41400103030f4aa20b0580350060508101d0340002d4402c5140c1c1d50184044d030280703207013a000d0b058155800200c0508801c001089800360001150707161080c1003001c020154103401140152000c08054036844c0185d807880100c3d401101d07e01000201656070401c090f4103010b84440d042180103400514210743d03040c1c803030b182340400c40c1c1c15011280c03202100140b0095003c1141d004114880242c0321190400040a07102d000c401600010844194040750b2843c051103110306400d0190b6044498036a528101038070841402d100c20384e03080c0074000000c0c0f0040040c40b10310f01c83c601030f995440070315602d15890400402900c038100340384540b03642c0c011403207402040311545030010756110030050034000c4100345034bc00701a0301200c060f85c00c03006410660340d44200c141c03900300c102201c841c8010b100b14000c00c4640f00d484a0b05941c000c0c400420300c81100110341c001801500c0c04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 874931393 1250 874930143 874930151
    0x4051f0906060e0405150910050306040b220210030c18030f2109180905101e060e040b2a121f05040c0e120c0102070501082a0403020d0308010306 64
    0x58040101703d07102110740900b5803001181401749481c2c040700041d404400202400c00103a100c0300400c0c545001120100c5180d0044e0052120814519208400c00c104408800858020a034045103d000d02180200c060580b0350f80c0c2809014002c038000c8454071841c03035000d440203580c0d0409500181c91110180e4145851206c0b000241060318014503102c0000d1310343c100c580b460b0401000c42401e00140c2d0402e0300d507403001c402000a00078020f00701c0d00d441200e0081202d8902c00091142003d51480044000d441e100e03080024000c000303400e552050700300b240c2511580c0c5e44401c1c0085e81c3c0c1080d000029104032000420192880100034100c016419401c55410390368005002d501c00d460252800d9040649000400042c5406d401c14091340300c452415905052443c4040390350500c1391241c004041c0c002040303103442560b040114070002d00091a21240c40e007404000300503103014002924548000c044030141c0507003116000c0364000c5502520b10441001c0f50300b4010406038003030004644241c28 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 874932643 1250 874931393 874931417
    0x131407080f071a0c06040f0614151918180f0302060f01090e1527060405010c0906050316030603021003150f32030706050c0601060807090504051f090606 67
    0x4024156145900c2220040c211780c3ca4903118565280c1ca500002c0301d841da00c42d184015500c40b1a5080d030b004041301c0c600c840702c20320050104104e60390003010110018544820400201000e01c00c0351503000c0c0f0310407001800480704580c4c032540441e4414003070450040340107101c042640c0003440701c0c4a40100d03080340d40242d0f2502c44d41c2d800e172020090f041140707a00443d0358064940c00e84c41442e0b0050900c681005c0c001154826041c0e48400c4240c203c1095003020003040b0500800380560304207002180341c00d0485504101010303000e400094054039203119039024004031715019500c07140c05507030028801d450180070320700014054407101d00d4020f50190072a4002038200781d21480d12054a20004001031203e45143c00300044d0154200e50450310407140c44480500e46080c0480d401030180c0780c1c0c4e80d95890a17049141487c0440603404202045a00c13002c109210f9800b04149003690030485e008601512021255950103240400c807100b02d005040c800140e150984d40321008542e4103071030340e0b220485 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 874933893 1250 874932643 874932689
    0x61101020f0703030c0e120a15020306010215040609051f140402130906062d0807030b01170c0a150201060f0b0301030204092a031406131407080f07 65
    0xd556507414102009002c00c41c0028040e40181421491600c1d04000103040d100001e40c281d08641030703004250f040600f0700811300c00190080c85403903031488001e501d03500b00f19000035504c2e194515002d282d041914080350402102c0c2e0000b076680c0d50008c0440318000310500c40305540755030068404505500d41f1741003601c2c0304540b0740082d01c501d030002c240491408c00c44000d900940a04881101c00d15556007021501c4900f8140d02d440b491340300380c03548910300c1d64030040602c0003400307401410a9a01901041000072405d602c65819900c0052880e0303440361070744440a04d4016801146a0310074444003000c151000c109a440c51040ca4070360007801801c2d604c2c1c200c5958040a40034907100d80c04200014000741c00c00d90000d0805034807412062a00c0c4004100540380c0424101d00000d0b0300054034420400d00c400000d8138250710a0382c4001d01042d0500045d00e5000b0090081c0c000e04041c400000f44100f140280202402891b860056446000b0911481603c6810501842084991811507481915 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 874935143 1250 874933893 874933897
    0xd090e01033f17070905040506180c030402041d07060513081902090711030d0207081303080304020a051002031909080d0305340305090a0f080909010503030313060e0f07080706110102 80
    0x100c190f29109401c86c203140501c405000c00030304860b04551116040000b514450820314403c032400781c0c66079180c1c1040c0c8100402c0d0317828415100320101c5592003140c503c02c40032408404403a940d08206d41d42e403143d925034800403505a03000000a006000f50860108010303000e490100e442200c40180541d22200700381c901003807240b0704a80a60040c0b00e107495000031070b07005218150103800002c0c181028541c80c1d40c038020300e980040762070745400301c1407108509140c0c030f01c0d8000e084116480310f050002144d001750749005202e6580c02114844040caa0301e540283d00181c05480c260069030100c002c0ca40001d800b8000543e200d24074000c1600228240340400a00b0040300040645000f452003100e0303c00300c000d094050300400760340c0101d015140016040c24008040b85100c1c151007916509a101040f0002c0e1050380228043d4200300304200b610400d1a050b406040d0f17000d88005000303400101814a083c0071034042e1610351041c05030204944000040c00300454803141d03101d1008021510180b420f0b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 874936393 1250 874935143 874935151
    0x1b11030c1e0304080708070303120203013602160b01120803041b09180b0901060605030c0c07050d050102070b160f03020901050d090605090d090e01033f17 68
    0x158001001c04070010040400300319080e15400122428141c0b030360780d03c50528185500c0740c6c09542c8060000c10805070001d10404038000400d208505642c035184c0c045500440c4041c2455640c1151140354409100340440800d807a1910359003152200b0301d0b01c40c420050041d4030301c1550a6400741c000010300e02109002c44505950103010a8190703111a542d0152040078040b41d00c00801020748007040d066803038421070000c6651146044403400325401c0c040b20303810300a05a002240d05003030051241c81e40201c1240c2d00b003099a141240c0d224858180a0300304036554009540c08450b10490000384501500907250f45402407440701e4003500c44c1030410301e11422150403100441c0301d60300041681f41c0030b580944828034041c18024a0082c2c0111940101c41c1801e0741104c85c19502d4040c010400802c2210540e80021030501002c00b50500791400006113051000824591541000c00c221071404a24030035212089016084040c00200000c24041c0701c07400110f0000310601c0d4801d0320b110f4605401801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 874937643 1250 874936393 874936417
    0x504030305330f01051603050405130506030703081608070c0905091f0902010c120c151509050408040b040807030317040f020f060c0307261306030b0f041b1103 70
    0x42c0c61910418007001d0400d0248060502c2010f200040c2490342d40546031079502c0c46540c0b401da48600300000c02c03909004001e10b5841c6180380404000650700e0002e80072081d240c0204056032107141a01c00c037401030070010030060141760049420820050756aa1100c161040004103100c1c0ba90380c500c0b481e581d9048450001100490b0000103d164845513101e061020300600d00303c442ea00c0341c0c0e00c0709a03240800d0303d105000124403086403000d002e200111b1509c22000c0380780c2401105118800380c2da01d09405e01403581026650008035080100e0b40782143c0040120103542901c40b42d992120f2901e6102a210503800700e06446e8405074185101000c0510032980300a0280040110390207000a103180c007046150041e1041044004150f0104040d01c00c140c480c4030358000d2846841c00d1441a4018400325448a2005001d417109400d2180012810341d6850700d000944000400d001451440321004065002458010002c0c01e0070380210903000543c48076140c00c0c2e4241c020342509556441140103441c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 874938893 1250 874937643 874937731
    0x50105150a0801180902041a030d1803240e0307030e0402091c030e030f030405031b03150703111809100e1308070c080a0b0c190f020f010504030305 65
    0x1081c011040d0309084600c1d080c000020b41901700b60b0209088480106200b11010b03404252104249020032010548031080c0c81e0160851306070844401e41e40c00140401480c85203201c4000c004140343c001c0c0351591140d00d0314280802c0d070340c1048454132548507080c01c1e4005011054100b2160405000700c1d800120041e20380e448003a201c1d955030310a01c140507422000c0180c8e280840c14565000c101c0a0a65400b0300040e66503a031034001007625068043c190710210300f0030201c14038140c2d80c000c40c41a944241a072038007000c0d56a50003003200241004023003814124000310740c1c801c1451071107030f503070080d183c040e10350304025101c40c1d840c40e07c40d000900c504501e0701ca000d070020b00c0641e2002c00d411512031050704941d04004103581c591281f5595a0000780c4580d000c3c2c0482010311210105032500140014480341c5400d03030b2100411210624802c0041c00d108080c0f0700744c41c01c2c520802c0280c075910b02d9031000300883d0400346401005400c042d0788a6621010ba541113a100020f00381c0000e0300807040b812845 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 874940143 1250 874938893 874938899
    0xb120105100507170408070801090f030f0c0b04150f091101050c0a06091a18030717040305060a0c02210d0b010512070203030108010507110d0c021210050105150a0801 73
    0x46901c550a100d41d04024050103003a00140f00542094644510650410703260760400d200107180c60482d51103c40c0c00c1c0c0c1840c031000c0100366030180403200e5580510741303a40c10301e6030b404040d61000030601c001086401000100000d0003030300c424602c100103020209200040364440040d0598410710360140c50040303800040e54282d0b00400080085c00c450009aa4040e0340d19181c1608590030f060040e20700a0303d03001140301a410b01194540c1c848a141c4e90350003550002040290360b800383c10801820080c400700c0300174400d0140c5050b00c0055a00c0784c2119803910700340a00e40301406404101502502c0b07008d08441c503424100c41c40604e001d8289044030b05001200342100301400d806030559043c0070042000264210340f18401e03900c211641d030011952540b50200880c01c4031401003070001008000540080c00740c3c00410308046c1c00456142c0030903035603510300003c0c0c1c000c1407016100c442441860520b403082c0c9207642245049500450b0780703d405640b14202e2102c14410300b005070380024003940043c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 874941393 1250 874940143 874940149
    0x31d0d030c0201061205300f07050102090904050c030f071a0306120321060105090d0308091c0908060f09031603030b0411040311030c010806040903030e0a0803060a0b120105 76
    0x240410365480c0c800450300380e5817142212400d16600105590f17a400084804800700412036480d8503400f60301400a0074810351032002d455500408100e0340807040c000a107001442000d40544d80d00500c02080b204d008d060510b4000d030b8560401c0032060090058144581c1c5410022642c0c20440303902246411021800160013602030780010704441d8402e0718030142e180c0024040002e48042d410034030140c0001103861a41c0018040024105410004100301c0d50341d568480c1c0c101c80b0003050b894107041c2c83ea62100308100b4142a40c00c29015890f50082d00403840300c1c4ea122816100b02c0d078004054a1107030725035189040c01c60a00302c50100140c0d2003000441b181000791440e0244407802441c00003442d5515038001025600604d0b81610381110206041c024842d100c40608024182100205424031000c0c002030700398030008003118403465440685005041c00307908010b00040c00c0a05407580505103103403004bd075410a583d400d00480c02d8034004620340442c10201d5078040c01003c90702005a20344020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 874942643 1250 874941393 874941401
    0x10090201020a3c030c12020129041d0a2316090b06090102062e17011107050a02060f120f15060a080406020702060f0307030c031d0d03 59
    0x4100d046200c1c00c2c42c184085034644240d2007540100c103851000c5903c110707002244400a80c07150301d10700e461040c03d040009420405c1441d0040c1d002c002e40800140c100000d03401450b024507204000204803010355075010b16061980300854048408000c50310009928005890107050b80c0c603040d0740000c150801081041300e021700c4001444400301c500409400400f8101503000f581c80c00031150488040c03103290807a008280a640341a60300c58145486000000d60390380c406004104203131420704030b003901540940400c02050120f24070101070b40c0d5491019030040d603180c420b901d40551a00212a42401240007220441a0040010014201160200611035014465003a000e035000c00142e0006592030b108248035801c8201c100a1601e0400c0a4486808002480380c0c8174044c100b00c0e010303060341c101c10a203420540044005032549014804a4000d1054486408490801008104071b882d07041d00070303040c8003110341d07814040138590080202080b04c0101504600d0703084201d194151034484c0e84 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 874943893 1250 874942643 874942661
    0x406080d08180a15140105152208010e07091d031806092106070801080d0e03010213080d0306080703150e01200405010914010936050103051e10 63
    0x1500e1090045a54440c440c1c10304030740105805445050a040c03a01c041c85c1d10754010074094446603e210481a654080341c8156510300844d8440d505251466404441e0f41d1400740031008000c108e280341c1c11064a5035520707103100d040710b0310b0708004265424820011144a254002c1c40095003409802c54180c21182a2038031125009141030040c002140e8070007101d94909900d40d100c00e181407145413015401c0c00b000805000500213071400401484000003000d42d00340161b490f000f1707c440d240b4030001e0302a21441949008450600d0740100706494007141d4039860302c0c02510308101040e9038040d01600c69055100150903403a6644c40c41405019607044801103217407500001681b92040c1e0680124150b0025500e03081c0440403a040c050747d42c003c15060060104ac0c00c030849580120800203002c0f450302c1c0184180c0c14074885400d44807007012a00b424042103108140307006034080d41d00750350050000f407005440c248141090b00300034168545072404210981e0380a0705207400e40d80020805440301ca5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 874945143 1250 874943893 874943941
    0xc050a06051303020c0315070c050c09100f090e12071a040c08010e0105161128030912031403090312130b100b041a09030102180406080d08 61
    0x80120002505841082e204000e40784820a0140c080d0400900c0d0100404080d4060b0388810900450382c91724082035507016495103002d101008035880c103c0c3c2014141c00031540c018058205000004000140c85c500f07503070200600c07003401682c80340020306580c068840301006802c0000394a0041d9240c8004208550080403000414440c26450600e001401c45099400c1d030b541c100c1c03e000480c428040c01120341401402031059003080e607201d081d032100c1181140148100410450304024052000d03403a00703608001c130701c03104451991840148001c00d060440000d04448000310b4511201d0740800380d8544c03d55941c8920103060340c0070718015800980900880c1c40148050301401c9020100184240c00595400c87c2c8040c16241000384074030081d15585502441000911581d100c8505a0702201c80302044521010000428110a84103c40b1102d4065000003020000304204849a8403600340a5604200c5a550f44012540303d6501ea00c1140014900030045010008048249042003043c0c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 874946393 1250 874945143 874945153
    0x60c030420060c160504020414060306121606020d0807080f04110411090f0307030305180123070c08030f0a0c14010203071101060e071e020109021512010906150c05 72
    0x1d607000500c40c0e000301a58100f160b11401e4000b007500b9800084c0b030010b00c0c040d1819400c0509100e040080e2041888601d03011704000b200003510740d40c5401c460f0052074110030568110180b00040240c60307109034041d0030094490b80c2d00c0780300080d110fa607180c0c1c412011980e4480e0319485140d02510501ea0103482034980400c80303001091540d4441c45149441902e010045545140c20400d210444842e22051071098012040410119410004403050044603200b20008881d03841b0061700c203411141101d402c19400861000f104543c08001406070038020b412050000d0358030300c1201d40d6031060040d1a0041d580c10710025241c0c0d80601c0c841e907078007441004100c148030b190b4a580d508907001100c001000607402041503194071000e201700030150000c0c145408052a003450041c0411081d2409440e00243c0501c3c5040c0e540c0c0300f988075442050b8028445a401801c4d034810214030780010006551112010000003444481c500c1100d04903514002c940c90401d26a45050781c1e840b81c41030090301c0601807 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 874947643 1250 874946393 874946453
    0xc081909090510051905030c01081810061706060a0b071415040c060504060c0807050c150901030c0e0a06031518090b06040c0c060203070c0602120117060c0304 70
    0x5500a00f031061040900303041c080e80c9400c00f00310500f0390040e0201e4442c0d00055042c030a03a240458152541542800d0039a195111458044030030b0724655a01c85660159500107203180b4600d070004802c8030000d070262100f19510012154031140700b03035440d0382e204d4080c0364100322101c00000a05442e500a2018a0002c003084045a0520303011b10f41c41043e81c406038040004124a0b45a00c201034001450500c1c100750411401a103040444000074101c0d05000c6080420810300304841303280d1410150490600e141c200074010201d400140d0301c0340c00301e400e10740c130003404030720800c10039000d290700400180c403061800c0000d50040c080c4a10b038035007501d00c003000031407041601c4080184110fa030400000d11214941054002403401804031481241800f9040c5a016403010300301d80c13001d41241006035070340c403440d90580d8a01e4124a00428141c0040f074203001c0090b07000b1000f81281c00780c0802d9001100d0b06070205484079421603c1c4035010106202003004603012550182c100c0a116451501000b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 874948893 1250 874947643 874947659
    0x120105010e01030b0106050304030207180b030d0f030b0f1f020307021816170403390c06030212070315030804080607030f3608120103050601060c081909 67
    0x40980081540401c040010070401c4424840d117401440c05160103401d5042c40d6a00940310745042c401c00b00558090711414664030321070380c0011042100103085403d40c01002030054103015800185201013031a01041c0440c42c20140840c07203d412005041d0895500c20403107062484210340342c02400c502c0284940341c0103032114200d80040104441e01c901d01031602c441410039810400070000104110f8001c00c404a0141001068100b981030800c04c5a003c1c40c000782c05128400340090113156812515200a4410708030800030320b090003407500030400d585491007602a072040c00c070f8410418082800041c55540320340c0c0047e00e0340705190000c03031007140e07661503075021a041900120000d820200c14042c0a5406224119425074001000d120124080707401c0301d40341c0410050b40d07441d918400c200c0328066030200000905075030300042c003584605140000c0031980d6400d00089429206000010035258001d50300404d5056008600e42d15150301070700358a103c2c070f800c0d01c49078007032114010380460428 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 874950143 1250 874948893 874948901
    0xd0f02030f0f070903030f0804140d0905040b0a050d021909020304060227010f2105040501020705101e020901030207170c0d0e03060a05070516030509180f060f1201 72
    0xc0500300c0c2800e402c04010507440c010000e031141050001e0074a0800000b034011592030308519503400e1240c0d19994600700740300202000246003105028001828241940050000b4103031002503034204a0700e00054240407102900e8064194001d0f03500c981c101c01464107844a58900201d108007244107907540101409980082d902141c50030303000719560124602c11130b1110300340c07080005241d42041c032840000c0c141c58401c40e2040304124003030520300580e44000924002c800c28100b0100007902c1c0c2801d001c1d000b900988000c603501e014410340b681e04d40803940507440c04040707500e007000003044060b60485c1c001d60180354001d05154080c09008041007079200c004544441c0d041c407065444001b180d007242031501c00d040d0300048c0401014082541d44002940641c0401c040400103204d4407030040c10784440c050390030203948240000b200c01301015807010103460240c1c1c0c11341302442090650070b40e0140403d421510041c40b09070b90030000300300d45420101d4891a52000e0b00046a00d1710710700e64131b4252 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 874951393 1250 874950143 874950151
    0x150c02190b060906030c0a050103050a0e1903030c050c0615040f02130306151a03060a1205010e070b0301120308040305130b040503100e0a060506031c020606090a021606020d0f0203 79
    0x448404100043c00c114495a5108108134043c1c10003501110000e0030461490241604059039000004c0812100354089130805407210200c925101c01c3d14901500101840c400720300103410b1041038130340340b80074030f00781e80e00d80b0101c03006442c01c4d03035402c3c4003a4024044007088941c42500c552480e80280c40510040c102c0038040811880700e00e0450034820281d0390040b43c4005c00090071582004050f140521510b40c3c00440104990749031101c4e0009190305804d50070560005070072940f0303042000015805002480d4481c010b907550695200000000c50100b44191482c048150001c4400030341700b03944141d401480780c1042c82c280007086650140000c030503001351700d0403100054244054a03080112550001008a09100c07055452803a0780d102c0c5040540140181d403200040f0384141d41c24001e01000780e1103004450b080d94110f2070001c0d81d43d80155121406031954a0209485140500868203030803e580e600d40718040f56680e445000350301800c2c2ca603502c20341c0c4510403025241540015801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 874952643 1250 874951393 874951403
    0x20904090c650703030605031212370606210903090b030903070506011a16050c1e01110f06191803020d02060f1e0604090203062a07150c0219 62
    0x440c1c03941d01d80031701164290b8011610076403002e500c0704211190b010071900e0801c00030b4070407059510f414ada000c0031268031140e401c0300c00180060040180c0b8000716085000d212014050004a81e2400e003a02c004101c54a0020b604100c502c20f034800304440d4000d292258460f00d0b180c0c021316940c12004185810648030100c85804c001181011b03c081040800d0140c42d840312002d0001c1710a20004507540700c0ea41001c03511000c1d00f1415024080f041c040054482006014050500f020703c505000d03646804080d9070119800c0070402080306000034210414511610040c09142c86494452000d003541203c21141c4948841000501a8414812103a828841d80040c40034042d085806420184001d01c0000d0600d1404100111000516001900b515a014100c4d0250b182c100c041800f0740a10076000c4c1d0584524810f1101032404000e20424200d460f08004880c1070746810042440d04c24514040c0148104441c2c1c525500181c1d4003481d11204540100d4141900c40e403040343e00c00c142d242091f00c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 874953893 1250 874952643 874952647
    0x702040c1107080c030d0f0519031d0a0b070e2101330312050d1406120309010e0f0f0a06030c08010f0506070b0a020904090c65 56
    0x1850710010002280030f004180c024010341190003010a6942d0100744119040000148881c07100600440c2103d95040d0348488068004500400c044d01134640c0c8074030382c901548400c1ca9041924404100b41c1801076110100e08035a41715003000f12802610f03050304940c09242100b0f5500c15213031504001580210b80e0001095903494241c01510056110424100612117646440502407000c6103079419268403240f0032151070141c0340110b40724000c0401b8220414034151001d0724a04407401c0e05441084211a8504070112f20420940c03607001c4d04605030302140800d0300080d4185413046442d800301d50058500c1403c4810940000d68400c82d036030001e408a5039903181c06a0441d03012203120f0240c070141074803041c03440c070f058085055445a440081c0142210001103800c01800340c04488002000400c240304038901400c0c0940e41c0c0010313101d03e641c0741640c2075508040000020310f00c058203429104001c0082c902c411540c50140c2d9416010081154001040403c0c1d0300036000d6440a40005412903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 874955143 1250 874953893 874953917
    0xf031a0c071119090504060b300304050918010b04061409090c0603040b09011b12020901020f0d090e150d0f080d0204150807030e06070c051c03020a120902010914060702040c 76
    0x120823100030f501c95502522070749554020090342c5030011364552860015401c5846130b08207026085014a4004651104100090210512410b0840044640154001c001c0c101d00042080101d400c103100f10b100a001c4401c03200a54074100c0986a8400c4103401612007900c0b04000090703a0303030310855003210003000c19000e001e07400700d09203d140c01c004484030b040c10255100031030107054070f00c8004010a040360001f812400b564070901c140340b03c44170381b4003c5440c0c480704468007802c920058028503a0000070500003400c15801a0b0450703c81c6040a41841240480c503101d09405680c203000c00d542c1020204450350400002d440207100500c00c10b040c0e50280b282c9054024125840500044109410103075101c44508000c19640d8116080c2d08021a2544903850000c0c2003003007006d0b2100b803003001c400c0c4041085404d9002805840700581d1113880701d07036001d01284101c8100c0400640000e81203c0103201e05a600007840089000c001c180038108240ca0b40000c0c01c0d120341920020024500031044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 874956393 1250 874955143 874955153
    0x21020d020a1e020d0206192a02150411010e06070c0f060f0809101509020c0d140a09030b0604020c0f150709050d08030601050c070f031a0c071119090504 67
    0x49902e19618400b41600580103000290f541c400613004a44044d661001c840040086074400c19400f6000d40c500d0042c0d5540c2074007849429490803a02c000b5000341452900103034003078103500744100d034481404040880d05900440707041406050440e0807000810000002c0f55080300b050004045500a0600b0039007003127001030000c40540b1007070041c001e0400a0180c2c2c030201003845c180c048104040082c0f4104514802031501c3c4035903100e214002d20002d010f0580d448040307218181c0b0340c015121217030402c48a0304c03a000a88103940401c0005010300701c042c4002100c4002054004100420260030400d6495825040c2041c40c541e00600b0b80c03101443c0e070980075400b441c00d0b600200600340008003a107001c02050710b010040d04020212000000001c1303a41e070080c02503881c442120301c1155419915591000040e102c6070000b90365070011003020b0f07040008005100342c4079040302a1450300b468002d0b51882006000c10081507407003450b0421301004003080358034540040480310b40c0071500341010f0520b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 874957643 1250 874956393 874956437
    0x120901091a0408030415060522050c040302010203070321110a0e12030a0804020402070605091506061813060b0a05090909030c06010512072303060906010621020d020a 73
    0x641c05009003030081102090460f000d41341e00942040207040e503020300c0340754540100703865000650b00c501290f042c210b000b41160f0520b42e040d10503620411841e1200810980540200d10009006074010030110740024861081700c089050000520322180d458240800161455045c14040e480700116481030340c40e0f0b0201001817208030544248070761000190505da16442851869414001c1500100e411500d559046412594011008200300c0c1010403c00c1c4c2c13a5100340c1d50012049100ca0007180a52403c042100c8ad40076034129004100141041400210703103210b15002d01742d0ba9104d4002800c2000c2c1c80041820030082c0c2c0d101903132201300f642042200c00f4050440041c0d5403050210540c021000503403141500e00481c1c01045541042904a14120b025000070600c5e5011444184803030141306c0c103555510300b0440a4500c0741d0368092030255030b048248200360015070a810000350450110010090b100400034000d8541900180f01c5405e0340e0003071000f000050030004c444034080e11101c80c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 874958893 1250 874957643 874957673
    0xd0e0c010923030a08180a060503090c04050601023c01180809190b03070e010c02030601030b06040e031602010924050f0d180606090c0207030f0812090109 68
    0x3800040c09041c14640089122402e141410310005828007041c0c0c3d03601000480300c22a40640040c0d82c803c40021512170351001260014050810441d012400b280070b201603030300c81c0e4211030081004140380001c11000d448080c00460560107056851502d01a80384180396407004038140040440114a10b000c20415694240882c56450003038400c21041485c0d5050311312a40203806141c60b0030124000079800070300c4040382d642d468126040011b841d400180514811880c0c2e4132030300d05080b141401556080c0310414020b5054005400600005000e626082d40010015100041e813174040c0017000c2c0346074025403444000d842c0c0c04101104540c0c0c0110608007520401c14600002205a9002c0c4c00c03401d5000e085005205003c924518200180d409655141034800c90a01400c114400651030500c0184002d40e20141004000706400e1094082c1c9a551807540c1d0040030810310f942c4850682c1c0e00c00c00011910b07407504003c038070164107880030050b004014400000a00d40c50625001c1d0980250349 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 874960143 1250 874958893 874958897
    0x1b06060a0305030316031b02060403090905090312070201021908180328020312010902120609010f1701020702040e0d08070e13091410021b0a05031b01060b0d0e0c01 72
    0x40c00a00000b0804020307260400d1581c2958181c1c008054016070250148005c02e40010004441400300c1d0703130303000038164015402911421000c07901c0e1800c12040d190b0407218445154010080c51400340c482400702076201050f88001030412440c0380d50750184030364140c00c0b41e001034144028080017640c40e0004145041100004614000310400d04440c012151b4184107999580400c060231600d00a1045981102003000f0607800356031200d0449000350841d040a9246041810008401303050084009060380c1403003004030030080c0743c11000603c0710300d9a56044242d5409204a40c0103031030354082c0da40450380c440b0140981d9140c40c00001d0003010014000c0c000c01c014210031600300d407074809810240c039420b076002040145007400c06c015149443c80c0020001e01c61040049810203440e800313008503112003102d40201e540e0496640795242034065000c0d00c0740e0020071118140051078400303554600f45040010910a40c5e078a1a5501a04400913a446c3d140c0c40c1c107074a000006051081d0100e10000b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 874961393 1250 874960143 874960159
    0x3020f01120608030d0f0c0f080408040e04081c06080601120606030f03021c0203091f180f06270605071a090c0f0907021c110109081e030c090904171b0606 68
    0x3601f00030252041030042d14280500840894180503104048802401c40070540072518101490002c140794080c0d01000b00f000c10b8918090044441800340c18100c81c44080100140d9007400c0b040c40400c00d030400100e407459912000000003c20b8860040091030084e00079094040782130380f82c4480c10501400c80c80864000704040e012940c0e5035614590720842c90941815100251103054988228464060003000501040000d00c81400c280e0030003942d000fa500c2641a0071403410900c1c00d0b01114000c030151141015051140c140700d00701030021180070340000c4208a0603000042240c2c03a0a607016480341d000600300d4040c509240d24040c89190f402d513400c1440b484c1041c4002c2d240d6910899042d201d14004a54040d8184500019183c40c074022000300080b481500d81988603a2100195401000c82d0240396018400e4000951340315200341159a4609540d280c200300d821180140708030340704940300d05860f510405280c042e1040b40b0b07041c656188628022000d65141c040000c003058868424 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 874962643 1250 874961393 874961411
    0x2d18010509010f150c1a16090801020406120c090302100e0103061508130203030c16050901090216060903020709140604060e01230f0d08070303111303020f01120608030d0f 75
    0x14040044400101307443c02c41c41200d0b0918004070407122491100001a028100340071080240340c0184201c800d00f84ca0346400d040e130398000c0900f0307805184187c00111b0140c1100100b13118094000003203460f0075251807002c01d52641e0010f4045040d48143e18001100c224543c00e080d6010310030a40541203020911031280d60400e0010030442008080b40d981c0032000c200407045440400030f9420130380090041e00c2c0004e85160240e24074000c42d2044c18868a890400002c426110344200c0d407043c02c00701c0d00c6014031a41c50f1204005844402c50450452240103000141000a8481d40c005044090a220710f181003180400080e150280c00030a4041184c00040241405e00300340040e050074845081c441d1140500300150b401c845c0b0300304080e007010728100c1c400300700b000305401420814800c0d1003c1100000d8044407089600548010202c0740c14824814000340ca0301c190341000c2d40304d05162299164040d00412000e80300700381d2284540f5880410100040002e0b40110104220815410020340b59 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 874963893 1250 874962643 874962659
    0x120a0201151a0901140301090f0b04140f07050f0f0405030f01111b0a050a050a15090f080705191b050306060a0302360a0c08062d18010509010f 63
    0x340c40400794540c0b030000106240036034002e459414440301d4402c010f45c0c40c0e41e5941464805000a510011038007403811840308024130342441042001d060480b003942d0030755200c0143e1148404050700b4041480414000049203201c00f100130080c00c9100d0074440d460314504420f1503d02042002c0101603079044c1034141c0b010850341e200356088203402c01101c074420603501c0915402d00c010703224058120b0054110007070038010000b8600c403c981c071030115844074100c02e0b04124200d40b50603400401c012520183c4030046210900a000c13110700036000d840c0121042581007407010801001106c0104404041074803c10321040d5080041a0a0f405003880385040000600e075506c031400000d20848150260b062a030810300ac4508502440d0030315841c1c3c8000b503a4003480c2048080790101c4035135041c07800940580b4490030740d00e4052880982054468101d440554500c460b450b02040b920003100300b600c01c2156164101d003a2002c2c1042c1000710594188410f01c0b891103416000449412005901080900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 874965143 1250 874963893 874963919
    0x905041a0418051203100806070503071d040903020a0b070203040819060b0607061a0409080a030b04110a03090c080712080f1303061b03050c0403020405060d0203120a020115 76
    0x3060480740010b040c1c485554000360118030700ca001c0c200c1d04c215024980e80500010003907000301c408900c013030311890340d590700260345d80c004856543c0000d5081c4045283c643c0a208160310300d280c41c4c0c0400c800040000c001c0f40447d103c03100282c006a0060460009010045031541c3c2c0118852010b1440d2505090b9019500e8204454007100d1003201447c100602002d907010343c000c0840109110b6946106c0c0c2400c170b02400c904607110b84940000110b003903503880c02c0e2003501601c41e1300c1403050341021790040701a0300801e0a164290f800580781c0350300140c010340075401480d40c00b600d51000946417480d41094414603109070004e0381c0c2580148418800d04102d080704640d030551240615030b5075400000c00c1c6809002c1c003100401000398080300401041629001210920a100700800811b001c001040782a144156410050140104400d10160800380c00c400d07804207000d4065501c1e610590b0209150074010b03051454100000300e0207a55559083c016600c682d217001c4156040b00e030401130102560 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 874966393 1250 874965143 874965191
    0x7020319050a0c111f0203030717010311120a02030d03090309050307060c080a021c03090209091612030e18010302090115050a050318010608100c05030f07032415090504 74
    0x20040380405940e039a445c66034101110f42d50ba52031465910310000c02a5581c1c0007a9099808100c5101d980c014041c3c90500e214100d98112600281500219003400030300403905014520740d006191601c00561002c00c00d6030154007090b5000505500c0c01d0034001c0c917200c80e54000700d11a0700301510404c07901c0e501040d0204442e0300405072554650a450040c0d1400d8200c0500c0b60b01404200c2d2120310a5070158840c00d00c81d0300a403855850380d9035102c1c400e500e850f0901806502080e5401081c41085010300400c288944a0300f00f030b00c41600c10000084d0f040703028150300c030b2051040700c0c0180300310306018804500619014400c10a551007180c000b922a000d01001601007000100020f0029140031800c140d0b181e201d40000c100c050f0702d42803ca515083d0540c0c3c03404020342401d0980702103901c0340c0300316403090385501c12610907a15140313400c9004e48070038211075244407030030a0040b810040b0010490010007030180350503c020340c8010081c01c0200c4030740c41148501d29010741c00039a02c03002d81c0520700ea = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 874967643 1250 874966393 874966403
    0x91203040f0218330f01051b07150e0307060e0103090515160504080a1506051002250b0f1303081603021e0307030e1210020909010b130b0a050d0507020319050a0c 71
    0xc002c170f060b80121994040c00104081c00205540080d00e04840070480e6801e554800c000d07928000c80c0803c05072110b8040941058040d80820010022148642d0000286080514000c0ba080e060f580340e0926040440100201c402040814020b01d0a034001d942c0302005450704205042a107002e20080e1101c01c180000f41c01e200c4482c2944180065980c130060180400824a00118811440003541c0d41008988078504a41c0781e070350110148548070720305085031680e0000f5072400d0700d48901c8070690f410151545a500280c20340100015005001400c148085010f03038540301045820b0080c500003044645115442b8010090115101e0200481c1d80b01c0d6007508050101c1c1e003d64001c6544000003124034000e90060a00901d1700101c942c008003100315044403000d00c00e90b00c4100201d160702c03810218042c2106810070400a0300c4904010340b080701e0080c01c20038104620519074806440e4100c40741001038200040c2d8920140001c2460611400c0e80d00d4071909080003284050a80703020100302401c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 874968893 1250 874967643 874967659
    0x20031b190303020309010207120f11061b0705010b0a060507060609090b13022206060e18040b0c0403020d0602030a0c030e03030a021b01020c07051206091203040f021833 74
    0x4a00102501208e501030b601c040032100181e480d400003009008031b00c00403000100314001c00c6809400000350300d8081c0100d4800700008001d2200c000903280d200280c1200d265485114070781d43d07603581e8a5100300a1010740c4a0903610051850b1100464081e034015001c40c62401d060f0101041032440119404041ca564000409807940000350469100426504403120040d125500003090350304568103c400303a0b218200054044420000c0400c48010b0031300c80403a5000014000c9810001040e4021103182c0d42c4d24031380350710b98011825001c440c25040da1016000000c1c0102001144248000c1080078031702041414003954150b92284406042030f22040c1d00400e07000f07261040b2000f0329880f2013145000f1540c1d42c145400194403902c545c80f413144505150300c242030040401007620b51080384643c01414605020020340011908060420359288408558190068403954255a42588140f14881c0c651624072071100005400f55503a0200190407103100da00c2102c03588041011100480c0d90342c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 874970143 1250 874968893 874968901
    0x50402092214210a022a090106030609060602030c030a0c0f0f03032c0d0e0102153607121e0c0f0b0f090f010512040f0203010b010c02030c09060120031b1903030203 72
    0x206c11000d18120364085502000018002c1d05a400f4104890300680c3c1401415920784050b40c880c061000462020341040140a45161080f004042051321484160400c0d0000740c545c03c450070804082100800da03a1800f03128215501000241e0698001041808464010040a0700d5400d80200036081c8202c045100000d40e00902c01c0705400c8400c04001d45e01e500c2c0400c0e02d00c51180c468034074100344038415040c51100d480400000a0540c000e43d00030625a85000701c4d200010301070100680d40c501019010b0203100c0c400310303400e403ca42e000341400b01c0603d04140216800442540c410294814200301598100008000707566082804503600300c1c1c0b030240140181c2d070501c1014101801020080f0412081107042c4070391800a80c000d4000704035056000005640545502401940c168000708071f5400303600c0d01c042040da0181e0185404240301d642c80800b00d00c000c0325080f04445942020030714503000180c50301b00c1505441044001c00468000d021256224001048054101a0000002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 874971393 1250 874970143 874970203
    0x1b030c02030405060a030b0f0108040803040807030905120f0106060207081b030c0d030c031812060f0e06070929031f0308131404050402092214210a02 66
    0x140c2c00400d000340016903074220001d8020003c1951400d070a02c20205a0440c0c06154410038525106940c42400c0a19649075030b122482235820000d411020800841004101e030b48031071140c0a000c0d4000d100404510900503072075406e40e80d007608010210343c0980e60400000d100005c10786c00d1200c8054480710f2902c030751001b0a04001001c1c0305140c101000351075000070154020000040300c1e01903611480b50981410102e598521540329100b51100c903030920201007a41e9900ca0320040d02048000590b50107a07002150411004039038050200c1c0c241e1204000051080240401c2e0303021401051061288900f9981c03090b00018000308602118145100c00c1c040b003501c001c101640d08410358a45891316020580c1d546d40326030041140c2c40b051070700e40590360b08050042078000d43d40108600025614051200c0b141c1d031603410b40c10340c104039407841007000c60303100c10344800c0c140b403004090030707107110480b15a1240e40f060080221045100f041282041a40424801704040740794052034003d820f00598 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 874972643 1250 874971393 874971397
    0x11130605060307020f0610050a140409020a0b0315060723030708040e31060b060d05340206190603120207140315040b0c160609151b030c0203 62
    0xd98100030000b040c09000c0b0380018a90038800c1400007101c09980c0d51241070405440b9a03c500d80d0030400300d83c4280006030340110180910b040290000640d5010742e00018680c40c0356030702070070040c080001800b1060b501e6010185032880c3c2560300c40d1800f202507031000c2541006a522001d8010038201404450100f40101c0c2c407420340140700140c6958032042c80740078074201a61112148981418680c503d10784e50140c0b602034071810492262070055903203c081c05010070b03402141c1d1143d4100000e00e01c9071101d00c503ca006000e030680002144020229400c3c04940070301c0d160b04010b0200600640c0d041d80042c0d00b55201ca095848041c148482e11502d2010301269040101980d943e031100d140500c0e0300241010881d003100a0300c0c3d05c810006014184c442c4e034480782820000d51000300040100e844400c1590f0480c000c00040c51600180c0c1841c2c0c104020584412034089465042c0c81c002c0c0315024800444080081c6000c010b08014000b18a9070710440c0e14482081c9904d0f20001c02d170003402801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 874973893 1250 874972643 874972649
    0x1e0306030705090c0409051501120e010204091113240c02180f190e0d03021b070b12061f18030507171014190e0703080309060a09111306 60
    0x403c0c1005410041c0400b14a0340050080b803242c02d01e80350018058002203910345101d4181a190411034034054240034002d00520303d11061159000c0100040c0360440d44210514003a80c00c0174a6100c16403010020180c0c1060740c0180482d41c20080a00d06139103800c00103090305209810000340708102413002c5080c002c070130b034215000d4075070318010440c0308000200c0d05481003036031441c00b462038610b4442e4a81114804000c0c0f41da280d200800c0d10007480e00aa0090920040c489070200c2072181040c0024500201500400100c0ea0081400e40114100c1b084460300008101d801813070410030500c0d80301c60f000d0000d60f114100428940d030000d42c1218050b00c00091a0004140c1d168186c580b48070100fa6080301d1080030316803003842130028018425104404100050449029907030b02c442c01032a00b80304202d4040d00b40301d40c3d901d403201a04d0004000131401103104000044e243d1410544a07420710800a090706e0756a0300700310740306000960342c0c0f90180704600122400101e80e60540460390081050390 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 874975143 1250 874973893 874973899
    0x2109011e09030b0c030f070234050a031b0605040e0601050313020441010303051c0509101b09050402031504060e160f0e2b0321021e0306030705 63
    0x4140450400d84e00c008500c944c22141401e8001d0311254002c03a0743d004010010780c1031801c5040c00640c1140004201820030b40d14444120b02d4680b507400181c01120340754011614884c40c0581c0741c45400c202ea584a0043c40079040840c18a40f408803a0070609100510440c104038000002170102069030040d1a64260081c00400c403440003071010059082d80d980c0c800c3c080611406201400526040005246000000300d01303136141d1840c0d074252074982061310f48140c01c00c40401100c0350b0f91100d00c602403041d03031b01034003d0405070600401042110002d91240e40c03c100740101c140e05403600414408103e4405507170050b581c0d0b0782d40e004000703e514071400141c1d00a0030070500080c003030001c480d51402181041a404120000c01e0010b0305c081440e8400304002c0b9128100e5400704d403070f10042e10040c3c805505212064901d0f9541030b90324000000c03604801240c00070544d50104200c2403c06000300b46522011454001c056100c001002181e003070303502800c24000300045c048d40303060011b200140405 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 874976393 1250 874975143 874975163
    0x3030c050c010c0c02010e060414090919060603021503160c15060608040b01050907080411010306050a06050a17101403030c1e12040b09012601082109011e0903 70
    0x40c1000601c410102c007005d078005103001804490034944881103d00f1104290480007002d8107440620014060090200061340aa407901c03180140101e9600d4528601c5908001401421032040002001100c2c48541e6490401d1041010150500300c1c0742c1200006814600c112400526040403441a001910780308581401000102a07401035525401580703c0c15506000d41e0b218030038440d105004540d0000011984030100c1c021030050b400326424040b06160201e01c0750348403004600320703004650055000a42c00104406440c7d03104c20f041c102802103040c402ca030341c00c0c581000112048640030300c00b41820445064601030350b04008a17442c1c0c0d140c02007034400a4449003c200d031103100500200c08240100d40c60000d10881000407101075850342592241400c10240045414901503c0c070540c182c21b00880c0a601a40f008917070314000d0450100410301c103442274442e0031046200d0201c10441c20f20600061020380e800c1218001c603203c5226040306070a0942400715028107a41d40040d007603500e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 874977643 1250 874976393 874976411
    0x305030126120c100908030610030204091a0103140403080c2a1c0201020f0d0b180a05090c0d0b011203170103110f010f082205160303030c05030702070303030c050c01 73
    0x201802400c03c0a0841e03003680d6518000070601e2064468124008100d46400c0000901500d002c0400a8242c0d60a2500504080e160080c0d801111013940708540301c203c0c2c036042d4804640c1d050088008010320398031115002d051130359000d0b0045ea0042d0400340c21410114600000720f150801c0d81146a02d0024044004205a18a03c0e01c03040d5145030b5005150590070309404041c014000c81d02900c030195030041c901b404002c074001c000d1400490080d4440b00c0d031000750380e4540c035085600d80078044c61280010710b41041c0c505246018100701005000e01d000032109400705410080041c112080366600e501d0180d014541110b0f400b14001d03401c0d0180c0300c1c41001006004907112401090380c000d0f1003880459040e40d00642d1440e0311610762100041040f00021a030320a03902800d400e202c0c5020b0141c507445401e40c0d41c0c0f8204181e04040900f40015100700f0402e141c1c0c540580d10b0088981d0074224610306220000079210700c032501014007490b40f2424000d0f0301d5403103881161942201c0200800c030010b0303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 874978893 1250 874977643 874977673
    0x4090603020126070e01091d0f060a06050403080a090e0709030c140d060b011101060902030f250c0f08040e0f010801020a050d050606040b0c0a03021002070305030126 73
    0x5440e000980c001460910b08890302c1050150300c0c1144442600790444a55444004440c1450341603e014104101034800094008071050f04440700c1415540141681c80c2c50b90745071803542c40040c540d038810201103004101264110007120b040d41d8001c20000d540c0c540f07010007a80c0780101a032000030010800350030007103201c1c0e100000c10180c0344106442c2a82c1c030356071502000c085e103807600301aa000c1d04031605100060102d602480d00c1322418108a104429401541401c480f038a0b072100344415000003c01c1054010600701591003850000f114081203450844c42d284208120924814040c080d00101d0600c2480e12506600e1940325442c04d5607240ca8629403032001909031142c0c2d64480c0080c0c00462103003010b0080d201400d50a42c1c0342c50426104070200030280501525141e0000300030080411031914034002040d12000190003001d240f4024900285441700e0b465580400c14810310460b030000b0741c0322003201d044650b148120820000301080c0d001031251400f00c01c0503244602c0c4446040701c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 874980143 1250 874978893 874978901
    0x12120c0403050307050f0c041a0f0103060812070302010f05011202010507150501090b090708070f120212040303060302131505040b0609030a0b150a18050705071a011a0c060c09030a080409 82
    0x30f8054017907d849007000d009110940e090303043e00c080c03400010b0490320240d0038038012000c0491014940800c866550345030a0342000300c000e0340c01d4888100055075009144d02401f5040800e403490314200265072600d0120708584540c02d10080c1004000580b01060001544420420070904001001156074601c650b90041c0086201c0f14010702c94100068503a50140c1100751240001d17881d803050401030400c045032141c000c1c030302c0316041c26401d00030398616050315079400348618429280020401d0860040084080b0481442e003105400d06140450768560190804115107007503a000c141d010381d950007d6024000c5440d09a0540300e036025030703c01e0242c3c1140242c042c10342c00003076040c4905884244844030410b03003c0e01c0d00d2610280241c90511045074410399001020b440c11500b40542d583d100144032110a81203200c00590000502c58040252880c00d0000c85075010145440300d4001520788680c802403402c4c4140e0000301d07020750b09407818422604160351210510340e0b160f4036a44040700030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 874981393 1250 874980143 874980163
    0x6010b09150a0306030c090903020d050a0324080f031801141204060506090601020109031e090512060f0601030c02150606041226031015020a120e010f0212120c040305030705 76
    0x300d22460f0b1b00044c0c1690340d124007480950076a014203a628851182541e141d880300350b0300c90815695520311151511116203560035140e0038801400820b18180c105840d01c200041c0ca40a00d0704200182c1c0c4502804141c00c240001007800c00c1c02c0e0030400c410506885000d0341d1030400300c0380d00380001c000c10000d541c1d100c244107540072105d0030100e0725508012400c81c0c0c2d042d2001004204c03181041c103c0816010034400200343c2515014030070581302c4011449030100c818895000b6801042404412451084616403200c0286400c2001c480c0e0004000e507038074449140d81d102c2c41e200382e02040d21500d905003100c015001c0c1c440041410201c1e41780180400601601d40c5003003240d110000c0d407003907031503c0860b80110702410035004c1690a000103c000408010039140c154800c0e80101c100103424651000210380080e03c43e0601807007400c0000d014555a41005402c54011510403000709d41040300ba540030a14860256009a407009141c0e82c00b40f1030b87c0c0000e401352001040302000c100000494144e6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 874982643 1250 874981393 874981403
    0x90e15030d080903071104020f040303020313090908030109050a06081b010e09072a050a080d0b0904020108070e0319080a02070e22110924030f06010b09150a030603 72
    0x7650200c808a80425042c0e8060107180c00802100c808524040580008404000c20052402c00341da0340b100e0443e4003d038411005a040850103964052000120400502d0500c4051203151015650180580f00500501014170340e10004a541c0d1440d507400003014007800b0040307a002010b101440d0030135a83c12001f070303400955008507505c103500b40036111a0040c1c80a80303d102c100910005040504151501e41d8500480381000070000714904019024001d80110002999503101103564021ba900c0501d155014510442c00d010050341d0080302194003280b186882c60202030380b200001e06041144044800000e1003980342402c0c060140024504c0200d5902114189540c40d140c001174650101c49107c440f181034a00c2e4104580c0e8104121411445171086650000c070890000340017030415565919030a00c42e100715004e0f6240e00d400c1d00d1380d15004030018141092444801c56680318140141211080040b454150b036032600043c910090114540042c0c541601a00040040129210070380d6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 874983893 1250 874982643 874982653
    0x230304170915220b0a0c05190c030b01060201020c0d05131e260c131d0f06070203071110020a05030c03120115050a0e060c0708030306150301120b07090e1503 69
    0x803c56541c4038800003120340e11406a400d0400d042010754504620b807505035098019286502c10704c04062208090341031242c0f0000b10f01c04c0c00c0d810b012640210581008003960700c10000b0311407450300019031040002403450541d980b103101400c00c4501c60786a500002c0c20806000c14481140c03100000e4409a401454004000003900c2c0c0110080e00900780d82000b407600180b1008080d403c1c03501d03980b000842c900c000466080a03500da034580350384030f0035900e42503070f00940c1110201550620180c0d4000b41c40c1e200450401200b62030344011a003816100038881c1400d100f541c0e070301c03a00901c894500c0d242c0107004d03203455400080e05281c5990142205058080c125800810750350b182c29180401d010195403050308005000c80305488000309014480c1d0312010078400380d028001c003041a030001d050010041d47c2c41c2e0070701b401405442507402a001e0003030b00302840140000c03003501a04000080e0044821585519040c00a84000c40da94000f1454201c0040401204c0390310b5020684c1c0a40c02030f01154 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 874985143 1250 874983893 874983937
    0xe0102180102151308041a1305040605010e060d0605040c080f010510050304150605193003120f020d1b020a050c01030903260403230304170915 63
    0x262034040c5828829200c0e448940480c1400c455214101c0344e461064403442d1820381c40c2c40e5089010b91042e40c22140044c40012842c1040302c02c1c4600d44000e001c1550148211802c010000c0d20700c0101403c8940a0b40000c01ca000000449401050080070060b00130050f6040b07804009004800854440d99840e0612000045d28184445040004580d5542d410b0840c5c03616138600102d4152041d074403030504e4403000007280a65a419007142688110386440c0792562628080107201c00c2000202c05661080500c86000c0001070340e2203018250340b518104180805044070354000b00303035a00c81940414808210190340c002c0c20341c400d260724080040c0b00d00c80700040390002c9070748905000f001000b03034114260842043d40280c010034003803403280c1440307000320085181d10303905900c015a400620000c080148001c0c180c00c21000d1843e000d003e0000120f40600000c07610291201410050a080d01e607100e0500c01192a0240e40e403000307005009030400c040b20116484036030082c00c5241c405d0f21400e9551 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 874986393 1250 874985143 874985147
    0xc030b0106080f0a02090d2102010b091504090218040c0501080c160b090a05030705030a111618060e090a0b0705120c1b060c0c01060603050103200f040e01021801 71
    0x90740c81040101c1c445940b6640e84c854000182d00409811038100c495a08004002440c4100040b09420380c030302940e082d0061010b000b402d44e80022880341c0150f6580e4140856148402d100f0030207203130b0555011840b4421840400c01d0301d002955000e10b046041000e000800581e6090b500444030240e1f00c0c0b84c00ca46600703841205030f1141001ca0380b02c8091841c0d130140010040c2032020b03444611f01c82600d840c0961034850508640c0628012103450300b0004080c1010340c4c10104400b200c0d55540014080301075890403282d4000f080340030f172280320f9000d102024640a42c40c1c0000d8003402c244410403803d070034103d003900c0d52100c17103020072206030000100048940d0702c02c2c01920780d2501d0260010b030302600c41c141c814945501820502040c0084038030140184802002003a0203001400501555180d0365242c0c0f03070031556150095020142031900420200d040400701c2461940b5500894a00c6030018000a5841c030000c0702139904207007011450010b5400640c042c0c10003101030650582000495001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 874987643 1250 874986393 874986407
    0x4020d05031b0c011202161b0504021c15062109020d050607080a1104090f0b2d2d03070e010816080c1c06140408040519050906040c0203040f030c030b0106 68
    0x400012a45c02421031008c5600c1c100d20003c041d003072440d91082e1030340b5000031400380e80c0300720403050b95903c0000c11000f4414027882415020134540c4038405102c1e04010005060803190b656807207628041c01581090100254444404140d00410407102d0071407500c0c14541303a030411180036000c1000b200000d14840ba00780901d0444442c072081c0289018100f11010b0002c143c9001481c0a80d5560410740e00320342c4481b0720030010001d881001607406c44802c031003201001e03480343c42140140140011000000182544800d010000500b103040301ca455102281c9041000d6014042c1d02d0b064000019480002059007a400180c524098442980f41ca506d0707588c401c02d0316581d64019200d24284024020f0b240d003040c3e00b40744075500109010780e6114584009100503142910758450020b02007069140403014031101030b521600a0042c9403070300c00014850a0001c008901542d107611124000390b00c00e100b11005020350074000303540f4644a00345000d117004680401c039101c007848800803031001c0c01440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 874988893 1250 874987643 874987657
    0x180c0207030c12170c0102270a0e19050109020903010c050403150c0c0b0405030327061609230f030f070303120b060d05100f0302060304020d05031b0c011202 69
    0xa102c0c0e0b039103803400060080500002c04191810700304030340720a028058490040200c0f4040b000096180d4100c601c0001840b030f85500600850081c540440c4403c2c3c0302c0809500407602a800c2070340150b6250700700388050100c50052411524501800070540c100164064826100705a00820104580d004203445510032804043c0041e084074000100c40c0649421602e102c140b0341c03400081000259462802e149410741e0b044400e5007001c810040009a491030140101104a542e2041d114013082c005440380c0c405000030060f00162000c100d820303401803500c00f00504005648400c01e01e8840704558400403026009031083c0c1c00180d10200c50316000501506091040000d403141514596054403c0080c1d15000e66840e6104c1e164904155540b402a042200c0c0e41d14010a0034508003003455600c00003600b0111145210507000c0c0054aca90400340c0c5c3c1e000c3d5041d18028000401410aa80380d401444411308605a14401844035000007250000d038880080e00c0d1050b0b44c400d14903024059002c0c0d84 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 874990143 1250 874988893 874988903
    0x9151d063d0302030d050a080708010b0711061308010518070609121505070e041d0a1e0c0f060f020624240c070f0e0c2101180c020703 59
    0x903590440c107240070110305541c0c4a004140400e40e0383d40428144070400c03034814042140401d5908050350030583d03040c2c1c084810302d4400f0881d07040c109100d640340a4042e000d085034039444c03441003264468208075164441c01780c04185040c3e642d145103e0103007a00700c0b82c041400c010003103200155100000c01005480464a5156842e410042012005211503c040d281085070340c0d0320410020781072141030301a1490340d617480000c0c1c6400303082c401a076504180300f05179114513244a104044010940310b0195a11054415442450350050440c3c05d2030014081c0c1001090324002aa031108803403103200300e990302d81340e01c144018825026a100c1500311110070500000c101d41010101c86501030200c0e0301401001d40c0ba04c810095910b40d08151000d201c0406a00c0c0010399101c900000c1003a213008203460b24901040c44e00b0040201c80c0c0d00d0016000000e200c0c0007041405490480160020b400102d011214500350795402c400001903100c541f4060000c1d1a16046034455440491003105881d045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 874991393 1250 874990143 874990201
    0x3010b030c0108070210020304030f020105071e0c03030e01050106031409030a02060403050f12010f1811121b0f0307090603150611012901260a09151d06 67
    0x101c01074802038002020070046006026440401d942103101440c001e900990700c0040d140365043c800f80c00c45001500c054140041a8a24502589034400d8100140b0140c0f43c00400d0714070604d8280c01070704030605440b640c4d500380000414103550584c0114810b03069107071381c071130b5607200c0194058030b034410191108010380001e40080d011034010170040490b108410341c3d079440c2254008810008150030b0300700e2201070403c0301c1c0c04c018080310407004121908074104100804c04811088540a210b021006000c6608074000690580700700440742c41203000c1700d256665036200c98114842654011140c450120b442c00d0030102d80307644030b48a02e42001040029000c00c4504100c2c0136219403000c40c5900180e0341d00c9441c1014840380041d0040c94081015041d00c031040614400544260240014000c1200c1c1f011700f882405000321901a8210104460000b8584801d083c50241d4030b0010080000503418840088901501d15201001c2e0030001003d680700c50b101d01050501005001401e150582c1c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 874992643 1250 874991393 874991413
    0x503010b0901051c052701020f030f06030a150b04060b0405010c0611130b030108011109060a14071a190605100e0f0a08150f0106050f1602130f0b03010b03 68
    0x50008195204240244213080c1502030052011350b0401c4804a81005000d00d8030440b500d524082c0ea00764403565402982040c445443d0300c8a1400000e14048039941101c01240d007a8074241302c1c81c40840c1d0421440b0040310400c01040018001204110380150b01d40000000c1900303140060380c0503560140e407403404010054480c40b0241141c1e194402c031106007044502880080c00795410010400800440c1e00c96140201941c2141d2090501740002c0008025891103a9614001c4030b44030400e0781011280003901001c9403074540100c0304020070292000c000502c0b402c541d000140d00c14007507890410450303803035280340c60191040c52052a82100d604030703002503003e020703080f0244900d0001d0205c4820f00003000000714002050b900200480d08041c013034068101c01080340952000d9801c0c1824031035490305000038010300c00c0c40d1640d050b80a020130240060ba102c444280384258004003050315600041901000514042541459043c80c1110604481c201801120b90741d607002406018407040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 874993893 1250 874992643 874992647
    0x60303120112110618010e03030403030804080703020f0706030e010e0a052a2e0306052119050705030106050102070315050601050c010e0d0e0118061409030a0807050d0503010b0901 79
    0x10520000b19400030030f40744014940d4846502910400500110a65640d404040050141c1c05922912806600100f000384040381d0406081604603503c911b410342c0e42c5031a420b0490803e20383da00b0240d40750040c4480020100e9040c0c100c044100440b00c02000b80013500c409281d51082e416600034000d82003485281850201510065001b0038081c800c0c0740310380344140010362100d5050000304035286c00d00351140c50b4801502a400085070b0582005c001880c100000a201c01c10038401c1c0b400c5610001809030205a030034454500020042c01d50030850311640e05e019030b101c88550207114043c0d841d20000148646c40082c060048035000401c590710001048450302c05401c004000398188881042180c2c035040382442075040c1031010101501640441c07010003402ca0300d8a441b01410442110f480b0b0350030508105000c421211281032036140d21108500040841c0180303c282545409012449000d00c050321300141455072091040e02c2252003880e105544601082c01002c100000038018850a94 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 874995143 1250 874993893 874993919
    0x51504111e2103030a02030124051801121418071215110a0306090c0305091905011b210507120b131b032a0e06040f030305030108060603031201 63
    0x258402600050580102c03003916680c4141e407401c1c144e550000c0100541c82c07030308001c2c0b82c0e16405010a9081c2d902648002030160055000d4109407101e11048001c1d5603005500a100607009040c05000861031821450207554040780c0700d40010b45051700c40b41d1040c04c007044600580d980e203032249402d20701c80d0700e0310301d0010300e56070309403032160380d500c01c04051401000c0c043c1410621540d1301041c0365090040d84420b40b52a950103000b49800c00d0180140b184021030501d0400d0503d80d01409000c503103041590251071107054911607151000500000568000c10310007080045400201d1030602d461801c500700c4100302d40d40750008400c04050300302d004aa401c0f01114003001041c9049007520541408116072524813640340583c40074442441c1e4941600803081001c18503001c0c5c091040d014444607031540c00722002242005084a0303040d019a80308010759000d4208400c86968051301c030714001e4000d600a0181e0b064902c20170000402d285400000c507003030303a0036a00354040c07940d00c0e01c0182c040903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 874996393 1250 874995143 874995169
    0x71208091519050c13090209090601080411100216081902010809070e0112020405090a1113060b07230609030f0327030306040f0221060d051504111e 65
    0x24a600d24580c0b50904982c0100760058000c1c1080e26900c185400d400784d90f0740a030350701000c034660040c00170441503510741c402181d00c12805c0c01c3c07002003a520ba10300203000c603845403a0250300681e10800d44000650008040c00e0100865049020141d102c025256440b50301c82e03604043e24982802c8140103520605c0e43d190400c80d040d044400180d04c031882c20038800070917000100c5110005801c90203602d4a0302417243c2102c3c110028055075180c0d0780722442e030101610003460003041650541020000c1a5205500400c40790007030035254481c602c0c2540118404c000340121081a00c80281e00d03020004c1030710303401401c1401c01549031a820301c7e0005695000289087d1880c41e40780b803040070342c4490682e00a03400107030402940c0e403407900004000c01c8500307100c0164542031040c4840003031480e4151b40001010008544130340c081d41c640e40040c070150042c101c014040c2c01a00007041c400a12180014010303441000c8640b1085500300a01c02000c00241071900402d0300003003204814148101200c3e48 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 874997643 1250 874996393 874996411
    0xa0f0203030c0d020c0411090a05011409090103060e060906151306030f0b0901060f03110f03071d07020c09191e02070503130801060e0103150204030b07050712080915 73
    0x9040030344030300301d040c405210080f0000d600304102d00000c43c545407080d4500e10543c028031034240040c00c00410036106403400b481d07050185034580b46e1805d031880c1003605e00c1260024000d05c440c1d0784034500000a00742100e80d6490360f12824011900c55040810b00900c02d82a480150316407441810400144841c502041c4031044e40d07400c03005c0085903a84041c00300c4a40180200c0b8010706156000e2403c5071100d038031496003400202d40500008511200172011040100c42d40f0081261480c002810000c0c00c4d80a00040e00840100340804402803826601c03c44483d02540e0209901c02c0500c04202800ca4981d140183c2183c8260368a001c41e500c001c0000c1c0e001011b0040700c80f01c0c141d03060201c1c1d1012000341d40303d07480490781118803060920528003518000009001c61403134840015001081800f004100d05c00a02c01c80080070078680c1901c0c0150b800c400442001e041589000d0701c41d0740030f548103903074060036085204c50b41030203003003101d004000050040080702d586a40c0407455103805041070b68 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 874998893 1250 874997643 874997647
    0x100507020607080301080303070e01030506010f0302071103030310030506130c0905130501180212150c0f0904020a050c1501180c05130905010501121e020711030d03050a0b040e0a0f020303 82
    0xb010455150145010b40784c043c0040d13aa0342000500a48140075081040303040509080c20441d00780d900611030400240300b0304000d601c815161a01c0c03501051420002c0c2e0b0107102c00b1003044919400c100481c1c0840c5c1c010b000740c9000da21001d051200040e04501c3c003900c0140c0d565030411400e15258400c0342d0040680302c800c01614074540d60b10342505d9003140e802500c030000c07030514825450406111400026881d005000d92041c0721088049450300130846107400c003011900c2002c40360003404640701404014800c55039180c45803006400c5400800e15800c85100cbe00030007215610b00c0c0c07038455044c1c507485007000b50105000d030352010142020042100c10005c0134825100d1000c40c050200002c2c001c4044007168070b42c1404001000603e444070120784080c1003500071483c0b001c0c1720800c140c2c80644042c0250303546d45642880d10748840c05028564061241200401413540d05501c030310700440b050315051281240900400c410790356901c840300185c0e00305e0340c0b20600040700e0202c10101a4070203010f81e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 875000000 1107 874998893 874998907
    0xc03160c17010603120e03250f15120b03030409060801061d04080301060c030e060c060a11070809090a140103030c021c0308072007080a050c010207051005070206 71
    0x1080c0503246c40c500b50113450900000380806c481242010118010031240070701c100540c4105200d9005904010800000c14132203240780d200c02d07903900c1c0740403200d85c00c0441c010803000c20320540c10f1000700000681c0040307501943d0002c059032800004c00170b01c2c2641d51400c59451004011781d400e0980104000514580c0989064940f1468054042545440c00740da11040345040030b5448030002c43c10300360550001078194490b00305c10b40c0a201002c0c01c110428018020f000c0f0040c525401802070081c54142100d40d50380c00303d2a00c01c003090750b803401150040005420381003a0b00003900102c00105604106020094102000354604551303007050718014140c3c1c84c090680c10030420909902060002180e007122903618154081d82c01441d5200d0300c0564032059418102d40c1809903c80300d4a6541c00416480201d500c042d0090a07416010801120181d100e4407040340e11001c107000721 = true := by decide +kernel

theorem cover : BRFrame.Cov 874820143 875000000 := by
  have h0 := BRFrame.cov_init 874820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 874820143 ≤ n) (h2 : n < 875000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
