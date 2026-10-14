-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1020
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:52:04.255497+00:00
-- url     : https://prove2.me/submissions/5a5687f4-d0cb-44fa-aae1-a198e6dd3623

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 183273381 ≤ n < 183453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 183274631 1250 183273381 183273397
    0x50708030a09080d0c1218030c020d0615080f0c010c030f030902150a030218030c060a0f180914010504020319090c03320705060414030703080408030d1812080c 70
    0x80d03c1c14101484045e00800900d58017038081c80b00300f00c2e0300e40980291f03040b9412401d000c2c0100c1d16807044040189080207084007454400d00d000b1035408280141d5100007001ea42085a4503040b15014844130300d010011804015824601810300110301d8601510510030078805904240c0c4916070f400a5489051030055401044558140e40303184d1182c008000790030400400030f00c2c1441c11204181c500d4001480581c8240c020042c62400d0900706083d40c500c44445403000c2071000c00c840607c3c54801c6001000000c0080320b5005c07540200540010041200503000305d8400c1380305005001d00991138452081d541080039400040100f80c0b4100a10200181e03400200341544c06e521906004111841040c2403c08002c101849419045161342d120071080c000c56410a1041c0f008100c049490034000c41481405415a41c4c0680c4a4588004940c403075009450705900020703640a07064101e1040309181001c2401c0d003044000560f80f8000700c1108a03600b4010440b020001c580044d4882c4101da68007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 183275881 1250 183274631 183274657
    0x201051b0a09050a0b0909010801231e0f0115020105010f0b0a09030501050c040e0108070b09010309060e0a080310060507051903050d02190906020c0904120e06030114030d050708030a0908 82
    0x80c0d0b40c5c404018032541d022120590240301e004000080c00b00c0140100300d120f1800084064074482c10206561402d000284101104a082c82c44070803c800002034103809100e01e103660303140540c10007400c948441c2201c041d0310b0071a85000b0041000400002e000341c00e480040c080c1a680d0813024808036280c10050704082d1855180030103010024208000420031101807610304500d41c0e0b030350404c0a40f548030340d100d1a02c65200803c1801c1d415032280d482178201030b00c05c50001440401c410041880d0000c2030300b044800600000a0011032148030310108001d000a243c6540b4140316581e41e2515a110800791021403980c0c0c070200740c02c0502800554044200e60300046488459030094120310003440c1c5143c50224041e12800b0407640d101080c1d1184141c00502a08107503102d030f42c5c910782340c02c0401c030403e41000703903c00079400103a54000055008002500d44044030030307000b40c2010b0078003482d002c2400070310800704031290000f042041540d40c400f105100c00500765826007080c0c02d0718480d00c0e5401c1c0030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 183277131 1250 183275881 183275899
    0x414010f03061514060906070506070806091602100c090503030f0d050112030c020d060b04020c0c030111040528030204020c0f070504201b0102030103050a120201051b0a0905 76
    0x2800000c0400d14007200d0044209212600401c060356016103028003441c9603003400742c070f50b8004d103081120003010f40e450094002c62070008552541c0e81882c07402e44555000518010601c03000340b03010078055402c51078240020f00b82054103940031359a4070782c254150700415210384140890ba40512054001400d029059a5a440182d0406441d65002d0f542101e080b602d80300c00031881221400300b1282d802c1d81900e0340c85401e0f42940800c40c87c000040e030201c0d003468542401c0317485d0744c403030b4005040bca02e250320007009020003110130182501d4000c80e454882c0350043c8030800442e039640b80d400c1c451031442e2061401c020140701e03840301802115000070b50020b00005d00004040c8000800502e0a6800415103004c0c42c1c4640030401540c021010384000000018404030488000c0001001c00c1601e415990002400c80089030f42682c00981c4141d0700c81e040020007506101003071092604e0100644020009072504001380340400e48000c1440c0c0700d61401043c445102c600036240000a801c00810b0604 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 183278381 1250 183277131 183277139
    0x90809090f01030c060302120a02070c0b0a0302071104090f020909010e03030f010303030c0e01020d03020c01140903030711010510030b0c1b03030a2003130305040e010608010311010519050306041401 87
    0x45551401c2c80308407080301132200d0000700c01e4828425034550946c80c5c90035910f20b441d03894003600607400204064030040150040047c0d07001c1d01c0b80c0108051503064a0168440c0101d082002c121920400d2a50180c0e00b015800340028001821503076840343d0440d20080140c0360314280c140108800ba000180d14440003080c44149411207140034100d9200e6542030240454519048442030194200706e80581e1190308002200d901030340250480359080c0000041d02c0300c0c1140300c101c1180d016a00009076400001c00e00007038960011035249030f01c028000900060802800d80004401030b440080c01800102c408260141c0c4088101c8181c10034000342d0402d60301e469098180c8035842500e03c200740700e241c24140790412005c080c80d2180242000d10250031596100580d892a4407010403c07802c000c01004049210a6143d02160282810f59142c0e10cd96046103049031203056581c203000e0600c04180030000310101071025103145119245000d91302c0c0c1d258840801c0183c81d000d45080c0f180790400c80042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 183279631 1250 183278381 183278401
    0x21c1104030503042441031003111c150209190e18060c090103091a01061b0506060d060e1e0d0908030d09080405040e01091401020a05070609080909 65
    0x1460031040380b500d0f0f0000c10f10160594052880c001d11684440c0b1b0f001840000c0482880c0301c100707441048000c01d0b07400400d4a02488142e0040f9117000c6004401034040c014041d2101300320301580c10654624004c0240c15194544100d405039004003288040c20140d04101100e03019074151400240c0007580c2c880740401c400c40c28500030300a041e42108804002003550740b40b45d0001b031a203848540900701c15100e12030096103c2e03000a500c24141078582001100244543d01c0080d120942d0b10000d084a5042020003030504140e003180001c8000c81480040205802040c0a07802110495684c0502050b524110317020f80100b80010803e4001c1301c992a0300348681d5440f40d8032105111054402c055018a002c0e18011840e001d0300465500038004005074001aa2002011600a1075110300380395442001405039081e9201a02c0641d460717103011000c20000c04c0501e0741500c00301000358106107040348000c1c118010101c029190b03035211030460050141150481c0c3d482480030f030400c8001c2c50094040c2c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 183280881 1250 183279631 183279659
    0x1803030c050f0c010c02010c0204061205030318240601020111030c040609050306150d030c060f020c0d090501020613081b070602150702060c0a2c0102010f021c110403050304 76
    0x580316030066415200840c04082038289030f0b070340140c5805808101c2d0750011185071005000803a0460303030310400440d0720030342e0195a600b4207128a000f1030356480d0011011080c110143c10203200369000c40c4280701580922610001c21030081c42d02102c0580d00c0c440101e002d083c0620f42d00d9280040042884403070165480100252881c80e21101401551a0305040c0d032104211446020300d01c103886003000d40d01d0000b07013100800e0300078a800c00c0c1c4c42c0e20546645040310300d54120300000c0c03a800900d4040100341844200e010180c42d040814003e03181c6000030751100c80003058010381c0a4140711501c100282c6030184c50b003942361840080d10000558115550700d83c014000c60016201d08584c07100c4400400d02102d100310f5065010741000d8030750741c200113180d80042d07084806110160700ca8680040081128041c0e43c1041000700e49007a454070006801c40e001050816070b0603004100c14003041440744143c042520305040d00080644503011000741e540110341005240d03000c000340c00501d032102c09040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 183282131 1250 183280881 183280883
    0xe010204090c020c1813050303190506030a02090f0a0e1002070203070b070f082a0d08133906030609060b031e07180e0f0702010203090a0809011803030c 67
    0x4100901d600ba2030741a039681c20030000d41940a6005e0421002400c24070600395049594411144400c600503960142190000c480700c60034850300c0c1082d151040110300078030f50080419806400c1045494020a146d140010b2001a1050401d0045410510780e0386c045081201076005450000c0c02000305a00690300001c02039101e44139503000852651a03810480b034402ea030140660000d1070903951803c1040d040044080a04040d01000c4520b02c42c0e003025810007208101d01a02c44c10005c100054143c0101801d420100e00c800031003800000e0001c241c041e0820341c42d40c44880200d01400e80d1403840b00541034008040c511100300003800700c0c2c041d0030280550301d188509110042d100c00702004580011110510101411418005050a50390304d09800581070720704001100c42d001c1f40e80000c14001d40c4403049081d00d041c100140c1c011007000d003d8004805200a5145040c010101907036142d0110010704514800959024942e005941004850600c603843c041a280e0b40d050241c5843d002d158 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 183283381 1250 183282131 183282149
    0xc1e05030310050406060909110d060b030403020f060c27120d1d01050702060714010203010b09010e0409032a061b02010b1909090204090602030a0504030f0c02031e100e010204 77
    0x2e000ca41442d00d40590b038190f49560f40d40d40d164520380340094015007080c00c401c0a000e00100109211243c26010b21001f80c20f802c00f888d541ca05051400a24040041c16410610381140b01408003120b9528105e81d404c81314004e41003817501000c41c0001e0040c420101e000e0b404040040d46405200020030821480440b80c0c43e0381c20b03004030301203000c0340c512a141c18107400a041000700341c00614085016110240c05144c88030145621440660308a90081c4c210042d0305002040e1010590f03480518124984d50560f018801c144155a000d17142500c0c429650500c0c40303c18407040d0607400908850806980c01510a05c241e08041c92842c004a040d1031a070001035013004a40945401c1032610110720040c00c042c081d040c00e18140c0720600502c0d450f0000c0342d1080d00d903249600414034900140d8055840244c00003140e0500303207000f805494030044d0140901c225500c06a01580d400302e442924000d444040d403d041303464502c1c482c2050100b10345652401d00c0d211511030403190560250081c0c0308055 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 183284631 1250 183283381 183283411
    0x30d02310305060121120305060f04060803070605090a06020d0606121509111b0303070905100e1003021b1c050408070506070321140f0402030d0c1e050303 68
    0x580c10500d012824007001c1c00c10742c0000d004109850603112000303051420000c590700b1028499941c00c844d51085d00148000030340301c0c170a201d01c03480c00c2407109000210858080003040d1820160075103901550101401d10399071340d4002a4260024010321040903403051085589590301c04c030040040406021f100000b80b101009240103680c030f803040c0401d0f1044003901944280c80c1400c0f46015001c2000c0c02d00c84400d007840390082d0542c40003441c0b9161952000515141e16242c00000c0007072405034409803242d100c00102507180340d000005040800c200751260203080405a00076000f038810201e41000c4440842003000c0308149c04140a446159a000c0068050401032421109400341d8001d2503c1500105402c010754a0600b00500d54607200781080580c103400c9416100e00d0702e1191489801950f110401040c40480301c011543e031040c8011108501420180c010965500128445000340101d4014081c01e1011403551a05032001d07040d017004030b0f45040e00e40541c1b80c0e0405e4819012002d860 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 183285881 1250 183284631 183284707
    0x90b0a0906140c0d0e190809090c040e01090902040605120a140d020c060309070b0a0f0e0406060c0b04050c0406080f060907050d12110d09030203100c05040b0a02030d02 74
    0x142040a00030f0343c0181d0350a00304000400410000d2080d400c1001d150301c44c2c080d0080442d444002c0c0641000d0195855648400c08101030120341500185102d10340041000180806101c0300381050645410700c4000490161030f1010070000c2620781c0019038003181240300030710700a05c00989141c8403031191159010000307140800556488400c464900507030803081076880c1e1810210091a0f20500d01000c865082d90f44111440d220303802041414005003421149003103c980000c0701c20003014041e91300b023001c945400c6008000070400000100786180707401c0841c0500c03c04014a0400c0c4130010401c100e16a40c941c15103a40d0016240300c5003160103948000b4a03a1000420602c04462014001061040840ea240c1210407091004d000c00c0c0f05403142821080780c002c00494000c01015200d00b1070640c01d6004051900503004003100f07480e401c0880b040200c070303840016601143c02d00804503407604100401642103000c0e4403120b40c800c0340301182ca01d40b511091120307a0103820085c2130a916081c09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 183287131 1250 183285881 183285911
    0x1230d12030f0908090105070f060e0f120a02030324092703070506131407060c210c02010f0c05060c120912030718050306070f0e0607020102150604090b0a0906 70
    0x50300b01d0240c40c071306080c0400c0c02c0c154040d070014040c00d481b03809821601d070901d66074101140c1501c414890b05901040010050030400c0041c0d1a07441c0c0c0d82c0410905000400c100250b40788401003420480b10100c2788104140010201e85e07600070751004203440c0551910a0040400c600d844c1c1a0f000390044400c1443d0583e90f012048411241c3c0140180035241c0c0c40b840c0d2030512056a900072201c02c44050350320540c1d1601845080301a0819640300110b2880b642400c41000f0003d41c4d4035072130300e40b2503034030a51071607001020205e03d10b0342070801520f1812a510180c0302c41c00060340203032260003180200b00900c14250010084140e421a811400340c030b50001440e036681010704407110806003080410440d03401030100030001c484021080c4041c540750404a410142e0683d621004940c0d4503140b8182c190b00840d00000241c0142ea1060030b203030064000039a0351400c0311038a00d4180403030010500c1c945036078106e1040079400004154640c201441c0c05801030002c0182543c43c0d510b02080050701c0b441d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 183288381 1250 183287131 183287141
    0xa0f060501091e0305030c010209010206071b0210111902150703080415181b08010c0e130609020f12090706080a0c0207050325050a0b0301230d12030f 66
    0x1010395800b105542015030840c1d0341e911a501c008030002c0c1074a00000041d40401c000c01c440c0c0412000542c540e190900007a01e0320001400c800240b0404a141000e9043e02c845a00c1c90300360115400c1d8101000018241e41400c0e0f03034a00d040d458003482c0440340007410b0746548242c5641c8295440986100c41801200c85405900801000a5a4100483c02041420140c0448001003040000782d000d00f44411012102210504a880318007840d0101548420000301d18024900c800091244545100700200050103010440b84a91904103d806000c20254040c8000c1d05c0c08100441d1b42d07890b000660036031070700180c1c031150001c0526000103c140b10085402c1013115200e45400d0050348403c0100d4010340702001080046200d00c41d000030702541c040203c001c0d0303a444200281c0c0e44041304501183c00c0000c0d45c0140f8090052010100500041c4000316030440d020040c200c030700c880000b16400003000d4103074121390f80300355500e00725424004d061048048901c581d803001c1140e81040046072060325 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 183289631 1250 183288381 183288389
    0x2221d1e06040b34030b0910050f1318050304030203060a3803060103030e030c03061501030c0207150f11010903120b031204030c0801110c0a031d0303120a0f06 70
    0x35103950100368502c0c0b20f651036440c2c1d0700c41050083d42a1500e00700140c031280355002404d00184d258a001901401c040070311a070891140145000346900300030200b000340b0040746e01c10703008101c2005440c103038007904d07841184050891807002030300061a00348250340b41c000c1c0c0002c0c2d02c20b002e10700c046400030100344544070300003200140c0400d07400c103950071420380d9201440078a00759404c1401d41520710b40c0d00340101d80c0030354446d842d03901e0309000c44810b1500e03100c0c0410020780286e02c03e90a1080380490494500c0d00d0351000d18001ca82d11060107000c038140509640080800b0908540d2184a00c0e001003c0080461041c1d030340f40240380f036400c08282aa2400000030b408500126040400c40205812221030000c0103000c641c0d04200b000145c81e407a40c06948240d84101c1802c40a110702c4400f0b00480d10b034002c0440c100b03070410603003d48458551107100001414803041c5040031803a0030b189440d04400010040540303840c0d00b04040d00b003c8616084441c028018900b1606141004040c814807041d2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 183290881 1250 183289631 183289643
    0xf0503150f04030806013c050a050301140d02090c030601030f0b0904020405070e100e030d0801031a090703060507020d03050105150d0e0a0204091a0a060302221d1e0604 74
    0x40d4550f40c03010344640300040d04242c100600c1e4080741184200001111000c00c0f0807000c0a4108031209003001c051060030350400040140c03c1241c0c550b030341d40c410180c030b0545030a041d5020f0f0320802c0078009508240e0800317009400139203d0042028580c642006980b040c13000b030b01c00b800f12001d0f0f003d03c80200e41e60700c80041d52002c0703c58089005810303d640119409103050400000c414410301c002104c00d480d2050010000382e84008203003107410148a00c003c0301405040c160942c1d4119946c000503a0603d1401d82c80681030900002c2000c0c10404c040d000440d0464001c1140342001e10009480c1c42c400d0101c000802d040c1070002400382400015494084001c2c4046c504103510781006401501e11501128074521403890050056aa2480348007680d038410075203800d2a80c1442c80100400c203005166125440c5000c2c01000562150254800354150000c186c108845d10301c000140103201a18a0100d485804c20390307150129000244440020200390070b1508108451140f03581d6400111001410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 183292131 1250 183290881 183290911
    0xf0e01060801030f031715040e06070c1e020a0b090f010f020606061b06070309120c080a08060315090c0307080a020d031110020f03010f06020a02090402011202090405010f050315 78
    0x4c2100306a80b1010b1504c689420510b041c444d0075540b901d06c1d000d4039070324850080240d400005103014403d20940c406104003621143c581240d0141240004200103005404050100081c280440103ca001c09134001c011054140d1200884146c5810a03c0b409006101d000364044d819030041d42e0b204240e01d01c682c018201569440c1c103101150300860a8042605417020b0303125407003001800b11a1150019030b070b001500181a041071440c404520400105010000c042e010120b400364089640c03401250030210301c60b803a03034000300b45089000170154181c48040c40c00d024000c14003003416076181c11708908803101641c54001840d102e4950704002035003c0444840b10001a006603e42400719600c841981c20000a1407900c1c4140d0307124903c2d00c000c2c1d01c00007005000104508020700041d0442c0d1000300490032031607004c2010b442000d003010f0305000d125441c00744104e1241d011100301d41c4005c1e00900c801d5949220310b441103246130140900c6400348144020760441e591002600c20b004a10900300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 183293381 1250 183292131 183292133
    0x20f0c0616060e03030708010e04080a08071b060905010506030714090c0708030405010f05070f051c020913050103060605011809020708070b043906031e05070503010f0e0106080103 79
    0x19030086100e44000000d520070034011903401e100328803020302e011010710b5407807520500040c4a000142c0000300ca0171041010305c004204824140d030f00c00b440e2410150103689841e6002c1c0d8004440030302500c0d0248189840c442001000c0e0000e442c01031042d80244440c1e110102010348a0416000c0d002030800b240048070014a05844000c1d08000d01d0480c2d28078046203900c580d1400c0d40111000d0b9416910f82c02540301c10101481095440000d61031700c055140e0312214018558856031410b03814a440f1141c1c40080c41d14181c0c1103407154480200490780800340a0403071405807e092005903401d61401070009040d5000b40203009104000105500e101820b060f00000207400047c4140c2c5e28203010f0051100146407600094040d41c0103102d1000d00c5400c0d0386a010308031401c00c2c03c901e41101103125106014020319038080c10ba0703c19007008645151080c82d69050044920307074851b51282424280070b05560801c00441c142e80d0000b40d00103481d0307111401803c02c05820b11840c0c3c002414480104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 183294631 1250 183293381 183293389
    0x3207120e030a390602070204090305031905040f0305030615030109140a06050102032506050a0b090a0b01050d1d06010603050105010f020102040506120726220209040f0c0f090615020f0c 81
    0x4020f5114600040c20005240c004c24201d5109407005c80200d2400401d22052062050b070001d40c1c07801d806420301151802d6520f51700f901d010100700070240500400410546d949005c2070440c01c071841d00751035450351b03594445900946080400179a02c810010045001e030515030090009492040c2c00441c580201c0c0842da0364a403442c2208908000c02405002000a40c04e0150341c0c010400c0300808295103a043c6d040007404031021301302e840c019181606651240c0d81081c1a030321000d90410f4001802c0340d022a45540c41002c980541406004944c00482e0b020b405500083c180c50003a070b501580100951020303405c034401ca01610380d01c5030040c080369420500b038600c05907104900d4a030a020b000b0503c6240c06d4510985150384940036010310030000040d20080b50f0380f01c4510300d4a40d0214011071a00840c0c03c462000e000a0481b1401702c226030203111200e0784c401c0081c5611180410b001e0f66598100340100102c0c06071700d40b01c0c668204100c00151002400410041c0210080c14608107024200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 183295881 1250 183294631 183294737
    0x114090d080c010603080a030501080d0806040f0212040f0b0c12010e1005120f010b0604030c0506250308011404020a0503150406090c020604063207120e030a 69
    0xc40701c07440200160420b405080c0592002144507194a03916071195150103019034205030082501a4040f071100e2070314540c40505103402c07600546000901600400c02c90010b48600314070481030007405801c1c4010003142e1203014100f5801005d400c541c40d100c81c464100103208201c01488400081401803054040000c900c070b8100012081800c1903507030303e0000c0b035101c039041c440c0207040c0d40041c418003845450a0003400081c8200b1681546054159074514102545600a05004442c04200740004201140450903904400c0041e11424145c03490700034a03d0209015010582d241d10504943d1f50426009841410140341c48103800c55035448207402007041d11803401d61b4810b0b1140070020b0304036075900c501c03002d01420b0303805406c19241604211080e2006046140c2c41079541e50966405903211100b00410601102070b0b401098803503507011100001c03814807100d0610302c1c0050359002038100100401c0c544ca0182c076403100d820800c1c203042c010810130004e021254940110000f0400d1850410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 183297131 1250 183295881 183295883
    0x50904050606163c1704050303070305180405090f0d030212040b090a06020d0608060603030c190305040e1006020f16140102150a060810050c040506070501020c0114150114090d 77
    0x10b515648101c4044840541440c4802840195410b51400003400869661445c080001c6401c9500c0c0ca03141c040442d55a00c18880007408000c00807403041c003184010303403a800121000801c1401582418541c4949906541051241900c2000620001a0b00a0086d502c0307640800a000069643e1798a4690201c44c00921803c26800dd4555200c0010305e5032001e440c8071600c1c20000185241000001071900c0000350850303200368801e0101d103909041c0043d107489030540502261040c5090b5140580382d032b0081ea0005905902800b04002c1b00443c154061011070751030b6405c407a4140c8490155a8481c070070b161a2070301c50380079000d09200c142c00c911040b010410040c41102c0324101c004105404c0c2d010140e0360344440d99242c0c0d05c100081a07040040038030200fa264030402040c10030000d41c1d2201d2041d80b280780d010310740206007201441001c2d41a50350a1044000034000c00c05212010030122074202c81d443e035003418401c03645085500c42c40101c6030800c80c0440d8140340081c10000c00c21030400945e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 183298381 1250 183297131 183297173
    0x3090102070f03081006020a050318060d020412021804020a030b090a08040305010c080903030708060d031b0303150909051504020f18090d030b0603130602041505090405060616 77
    0x72210000810380e40703031580024065a1104164140b1a409840600059204408544c041740301c06000c5a004802c03a4524000d80c840081002441808616036000740b41c4000042c905c081000a050041c51030074000c1c1c14401c590311000194580c000c00ca00038030565019410864884042c0005402c0c0a800c582101d101c10031118056916032b602401f55029400456807651034140c005510754000541580100821029604500d0b09070f5005040800080c1100d100380140351801050600608071401100020b1084982001e000e04018000e0300406000d074001100c149800103581c1d40c1d0f4801c0d009125406070161642903c0040752008031400908141d9001c0d500314202d642965030006420b800606849804245140111502e4100820006da1005050800382d040e00d8a030344031700407039a20240201800113031480b6800c2210007805070360040110000d82c0da41d04103d65030080702401103420111424030543d80c0b200b05001c618020787d42082046100c8040c01000920207a540041101c8040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 183299631 1250 183298381 183298387
    0x90c040c050f1620010f0815060403060b1207050307030822030507090b090402150310090606050409110f03040209090312160305100b04090207051005180d0c0308060603090102 77
    0x5a402c519030164240041c4958046a01800c1026406003211450034085000034207060b020f0000e006500f50999003410441d203040001c200440c008882c000003c800780074651210340724030f414002403101c2802e8910441c030340e0010b11384c1c2c030000190000554401401800d441407460703441e04000d401a0249015004222402e11315910940600c40300441c01200100011482c11070680100c510118407a4011501c0c14108405a01d03100103e4252201c502c0129a40c3da89144103c040546160400101c203400c042002521aa118015006440c130084040140351164000441c0c5445000355400c401c440900001d0301504d0a90945503001c205041500d14203404003950200040c030484500b0a54401e0b0301a08040990510856911a450345080c0c014681413056005040c012031198002c06a00062a8010003400f0720000c00460715240051100341400800b0040c0540040d05c07241261042d0f00d1a83c0009103d00c0d020030b02aa0151100306603a1201c41c04e001c010f84c402400c4590941d020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 183300881 1250 183299631 183299647
    0x1003020f1902071d0411091504050a0c0f0207030b07030e0a151a040e0a1104060305010911100503010e01060c0303020f0307180b09090a0c02120408060a05070503090c040c05 76
    0x40540151031896000d4043d19051400d14001c0368000d01c1c0e0b424400491200300000142c2d40300d0301700100c0100b11401019551030b049540a80701d03486100540103030800080c007000c500369400805c05601680c40340e03c070003050090101d91701c03c80d82c8030103040f1038026004112030b00c0c00303030b404a41402072103426986005440e803035201c0a03c2058111852140d0746040700440030b0310280310f00c041c2d40c038200c405004110650080c55a6414508070150040e040c0018040302a0b80d42d62116000f950311000030300040040e0f0609103011502e081509005503030024002c01624031800840303058030b4458030f0018280c1d00f0840103c8103044064022014141d00b04014014030044401071403280080303903620940300c2d8201c0d049280b454030950001c9502d14052040307054996480c40c6a030790264580384000750848540c80124581507090071a9a600000081c000c2200000031031142d00c40c800300c1d10b0511060301e40502c212040d2200700c0f03001489800074444611545080d411800c4808214504941042c1d04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 183302131 1250 183300881 183300907
    0x1d0607021e040b010521061c1a0a05041a28020702150306030d0309060209121c020a08090d06060e0702010c0201051321050706090303020304060b09061003020f 70
    0x800d00003442008401c1c000e81000d0b107060300540c12410020305e4000d007802003030210302d400309401c01941c070151320202d0000b03203081d21400b200e0301c0700d8030907108102c0b24450b242c18900c054401e980b0078054201c032181c001130601411805090702495000e00792506581010b60740742480e120180a194101c40c0013003c00001c41511801100703401000702c40181e5a0360720b03104004441a050331114050903083c0700700311895901080c1c41124038028113001c40c100020340703006002813185200080c0d000d285002c00d800c503503000040c1080680c041400d900d505902e2043c00b40d0b6242c00100004021400400064000f400c0215900041c20b1080c40046440c903192003e445100381e048603190010303076403030180d504c16540c24058641c0042030303010b988032032058544400074030b00f8883d800c1d41420340013002c0c3c1031605c81c0300300c00300d440181d00310100704004402842c004011350300c01c1c3d4080e1001420001c280d440d91508140c0035002c0c1c1401031024810360b02012056002c0d40003c50075400c1c40c03270240409900310078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 183303381 1250 183302131 183302149
    0x50c03090a06030605030c0315010b070c05060406030506010801080a0804050f120a0302030331020f01050f0d1a1e1e0312220303050f0319150e060f011d060702 70
    0x2c03070341c901180c81ca0810050629081c00111220302c00e0f03000410750000e02c1500d40d0a01c0c1034444107007440340c0c0d800c41401c2c401540c11882e4484d40d00405c0c001000268168540d0106014001c240d071110b9550b66200b58a503038910179044058103c0030104820000d51804c0c042c800010039016001c2039407440c03203018590800c071100310b003940035030000000c01c01d0111051100101c061aa1480e000000845000710520b070300c0300c4040240120225464004070303038014030503680f185442001e010ba88481901603040640014001e0340c0001103c044103420300d24004021105101c0c800c14604c503606c41150400c20040010181e0030f07252641c03100142c10f1620240090460400c62a40c900c1c0c0c0c0306c4c0480e1103140c40d007410444804401071401410320000e82c0c07041c1100c10021030769034259241e841d02c0d500c0d00100b10201c1d03074008801e8a0064035950380304001c203030380d001c07140c08200c14400c0b03649100c2400044501c2c0d058040c0005c408066040300f00314030892503016010040d04050401c10789901245040e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 183304631 1250 183303381 183303389
    0x112110909010903020c0105070c17070e07020307060606031a1e060c010b0a0f060203030103080a0203040f06120f051e090a08120a230103080901111b090c09090106050c03090a 77
    0x20f5143d040b10424160101705e143e030004401e1800601d040700c00d80f5140c1d90362005002e0104400c0c1b210540a4801008000c00405801d9420f01c01029081007540039644c2d90026508483d42c6003051000140c0c0c5019100341e81d100c4c440d00001c10190700c005030400040107990507880d85070a00e9400c50f4100f80e142c00000d48142d0b8403000c00060b0810000303080186131201da074082c110120314035600b809895404000e0b2030440760301040c2540c030b820b070441050b81180102d130800300300301e4240303000004c40c543c1c0100e01d552581c5640c40c0030014600a0186802a91012200c51259031401000040f6070b4504000307256000d881e403410740b580f110300380d40c0741000c43c0d100e0050035000324141d00070b0124082207031090030450454818400105085051030038a40e540c148406080c100001c249099141d0003110021204200d501c240c5070950002104411201802c4080314001e602c1100061030f80c103080801c0303502004006100800307683c0380035801c5079642d12000400c010780c0018007842c03640e51a880aa50064 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 183305881 1250 183304631 183304633
    0x40f06050c22030c0515041a1b2a01030603080409050415050f0703050604090b0403031a0114041a0d0908041805071d0118080c0301230112110909 64
    0x18040c4910011000030521410142e600c5910303104000140500001e0800c5540135240c068081e18101390481c03050145510484a250390003101d80840381502c0020904456800c2038080c80903603040790766541c0c280340d21900b0380d040071049560068400c413601c040c00c015014540456842c1d200d03034800259030025402801340c16210300a2104204440e0f01300c0780c1d50902e10100f00260300e0000012001400054059801d165968011429035215608144d410035040780061815081516000b4000d014092010322070f014040e9080c0c00640c8101003130b1150b6812010114202800c1c9819001d050380544d02000e1244003c000030070040380540101d01025006146d0030741c68501e4200003100650905a1014196103407104201d18660040440007400300c605c40d441c01400d113502d0050b240101074400d07580c030000440200180042d000603000c910460f05800178047d4680d810b090101c0c184c00340d0700480302181c0510048c000c4c140842008010b03140030391624500b0b00d0840000c130310708200c103031841406 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 183307131 1250 183305881 183305887
    0x20f09010e060a0804030e040908121909050a1203021621090b0d0c02010b12010509070506070312020d0906020d0902031506060a0c020424060e0306040309050405040f06050c 76
    0x11940e0072a1003210401c009450382460490702c03890040c20035000500081c2400641648901c082c4c980b0751001e400d50ba449400c42c2d65036042a401010140c008548181441e4407543e0281001c900e280103000c411540140107200e103000c6590749203101e000341c0390044100f507400c0c480642c0c3c48650311050801c0c01d0086000300c0c042402c3d9402182803000140c4440300388a1800001c10070000114100c0d8110000003400082c01a0b421134204e0141001d0002141c0c0f02e4021901200715007819401507002d07900c6d00c0c080355815a9180103105207070080c5c00024000c11030424000038800342030707002400310075000000090056103e0b96401c08070303004840d6a100b225520860401103080400226088200b4078445c5103281c078100000981c5d504c5052192020170074281080405c41d111900204da082c640d04480c09801300b14100700407001e428600c58140011008015110300303040103d2f447d40100e0701030b51010121400d241c00d000103802c003c3e000b101c019140c4034020000ca003079841414060580000c00707980d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 183308381 1250 183307131 183307147
    0x30c0603061c0807060e06070905060703120c05041e080d0813080a05040806090601081903030207020d05160e04020d0f021f0f030c090506122203020c04050c030411130f020f 76
    0x4120707003581b07409404991101040c440415000300e02c0c1c03c02c58800b259402d0350741202d45411106411310100c00d41a0909050f9464a09a0040b01400990301c03003ca4520f0300b0316410030308110101003846100b00980041c40c00c5c0e640c0920403040190720156207103a030320313510420f80d50b850a40c1d804511408000f03100403074140280c0c1d80c00e2107144e8022407800d00401980d41032082294460302c46013000074400003080f91030b004050080e01510040d9400030300142040941e4104207444079400e1600f6201d0340e0003480c01140c419045861140900d4001c0c00322440511503680303030300d200381c021a816a070101144000d0b0091400c9203042002100440c1d5a00c1c030010003002018069943340c0d14104180820070800344500e40707455091391854042c594550415840e0700021440c0940028041c81c9480d684443d01400d054000400c2e40d00c1400c16581003141ba50307142c80120f4103000c03d68006012040300984000c09141802911040405440001813084d4607154030000b281d202c0000d0280e40e60740400c25079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 183309631 1250 183308381 183308393
    0x902090108010504170c0705130902040507020a08030a09080904090c080c01020a030203070b0a0227030607030603050a0b181615171f0f0605130b09030c0603061c0807 73
    0x5030041510304020301850030507644998680322100c520100351003000c1540f800403c010404940100b002502220a40350080e046c0c03c090310082000780d0050381800082481144001402c13002680c00c000d03200d0030b43d25105880e0b0301800c4101d00664400009102d4425665100d1082541d401d1041102010140c5010803144c208a04083c0950554110404150110b5004411125070300c2c0d02c400120350360364070032503584000d01030b000c00d40404200f01c41301c414900e04101412100e005045086620b5540c92040c12016544a40002006034002540080000d02c0080e040c980081505070151501c004501e072541c03400ca121050081084d19044007008803407415010302c0c400010603d0300b075500e10f075840c92080e0130b524041c180c0035940c5810084240e00703440006106010341101060b52030701a130b0b6000010300682100301c13072007080381c2201000208420700704121001680c1c01780141c0348002c402003c001258000400458003d040b03640c1c0030a4214041401c450403a205907075141e12100c443c1007035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 183310881 1250 183309631 183309649
    0x130506120102180603090f070b130f0609090207020120010903122f040b070b07180810020702040209030d091707050d0b041a0708012d0902070c080a0302010902 70
    0x40303100d692041144200d04403400034003002c07010301a181580d032503c503503c01c2840e0103211958258a40030f102808500450224010322844844d807042078441600c580515010410320700c1160f000c125101810401040d1903000351406c640141410352a4548191081c00041086245040d890355074060381010150020134024056a04040800c0514000604581c544040902994212664440e40c200b400010004c480150260b956604d443e061185880d1000746002d403944004980700480d00a0059a006070103c11240104002c000051017060385074000e40c407641c01a41c001d6001c20400c001c64074108412150701c0c0103030781c2e40d8071ba2620700b12039a454821185c2c07880a143d0441d1104000700d0356184400e428480d003041c040100c94550313290500c04440c28210200c0071111000030002e10b030b40c1186204d8100e07039644000e140d5800740c003200240342004428421490b000709002c00c4c00100c0c580e074094040c0520421061681c5074503401410320346900c10600b240140e4544a40706d086003090094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 183312131 1250 183310881 183310909
    0x102090315040209011403070b190305010b031308030c1608040503120415050d0b0415030c06030207032c060d0504060b180601143106020613030c060b130506 69
    0x40703081c55060950029034210300c1803250300460080b1610001c071660301071100500601900c0116990b41241694440d9881c1c0001003550100346080d00004200c40c0d86d40850380300d860242481036503142150349404c865000642200c40006082c4680e042011098002c0760000c1c2c041c103049030700d50b4607040406140280405100034041d4040c402040010b03041308240702c3d003031018101551104100c04d0020000c08010602d19801400c05144003902b0002d1798400b0240c81c050782c40518995111802a801e0f8030071010300400041186072000001c85c8042e00c81d0b800d0466004400c21800495000901d19800c1114124021603480d0103010070002c0c0c034816041202c500380d07501c610020307020307075038403500300b4028101814003244083c42c0d2210b58420045502d03000d07a00030444128007c1c0d480d610f0387d84000500300d07924504443d070301107001400001c1161050520b940700d0300800400e59412200c0c1c26007003008640c2503031900d101810b50b503500c4001c41c640e668000c100050710715040f4100804183c0c80700e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 183313381 1250 183312131 183312163
    0x2304050306270f10181509051011030f0702010e0d08040f0506070815010306030201050703080a0b0402041203020c061306050c01090c06050720010206070309080408030307020c030706140412030318030201020903 92
    0x1170300600003025030000703400c02030302c00d940000d1056550810754104024607110100f1585407403052000d0442c004083c50080b005a0b813494029520140b00364221403c1120f880040d0740710600c4444010302c40d0b8800b95200344145a030603803807000d541d1a18076143c825100380d0b010582c0700b01000b40e0b0790654840243c105209107000c4c01030600d9500040d015124045001d002c21070060300240c544015500304a0b1001c038080c000715600c5a544240d407a000b012030074110018001c1e04201d00291a00c9030545a030301140e03400c1c0c1d0605034038000c0c00f642c0e81e1340401d1014201c2d540710224007000c100305103202401080d2549034155903000500d45502e0350360b038002184101c5203042d000314190303036400211584d0041503070500003450007aa003061910fa00540e4041d252520001040046a9a000c101419082d40c142c04031041152141804e48504104400c2907c4680741404200034204024118020060003030030001401103001068094198500b1030607030140c0c2d0009040802800e023000549070890b1001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 183314631 1250 183313381 183313421
    0x70207050901091d0d02060901060504050c09012703060902010f021f020c0f100b04051b0304060506010507051504150209010207091a0904032304050306270f10 70
    0x200041c0384224103026501c03803503581c0c60f2200c840a00400680312440d04000c01c4400c0078a81000096580008541d03200282d42401d00c00905070506001341da004120b403108543c2400d46003001100c0da038041580340c008a50300103038000c02002030304100c14042d50007080e010030b0303144107400007429030108a40e40d00119801540f080d034411b00c860340c0d40c200003407805102603541c00c00304519501c0d18140300311400359802030b5102e880da6500c5581c04070281440c00d40c2c0a20007070f602c2c6400062984a032a6190942003c100005400108198045940001c0504001c0d082450a4464901d0003201e9142c2d2070149108909001c20301081d48120800968998002d51502d08942c0000352100004c1c860220401e4a90080602c443c6060b40080400d40c00035010001519050400420075248809084860301d02051200e500107c48812070b000c2e03034000380c02000307039880708104070400d800000884441086e007032244000e04681405034007803403c030181c0181a05170365030044004031160102d171012110348007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 183315881 1250 183314631 183314639
    0x901020a02040902010917070504050a0207030c08130306060e070215010f030b1008031318050402060a110f0f0d0809010902010f210906020703170403120c1112030f070207 75
    0x24030000e6107541514007140c807000c540300586010406421890380070f4007900c00c14201420000d180303001c03200304a03000e0000781c1750103008034120b00c0b5001015000607001d003407072400b1442c0c09000300000c110342000c501c5000e949486600442c1c03225003040342c92504000a01c04016410495020004603043d108049545403164140d140e400310302c0004c1184502900040c15000721290340c074018800c0b20140e0307550301c0c00a01c61a128442c14000c003141d043d20040742c0600c0d13000354801c49214981c090107852400800c001c05440140d4080160a106d00c140305072000014404d101c00c110302e02c0c00000800100010070000703803035484001c110034080e80c0361001c8180507030f03445003000d040d40880b810b01050303061075911150003a12059100c001c0040c10044500704201081e4004d0450310700966030f00c9007a0316001d58401c410a002d40b80600014140000f0348112031850740045403040c402d00341196082e143d10040340c1001c240c1c2e400f07600320500101c104101d00030417040065000050788041d10559082c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 183317131 1250 183315881 183315883
    0xb0f03011409270f0708010b1302030714160507142107090506010909050702100e0f0a03050f0918060a08030406050a0f090e040c08071401090b09030a0f0c050a0605090102 75
    0x780e1400240e40c10515074889100f10500c09070307110381100c0301540e000c1a22030720440d029024031103200c0e0007080705020011804400d842607078040c00a50303803440980c0d0811000b048282e040721801051035924651107800080e01001204010482010790b010134020a204200b9241c408a10720141d01c0303220f0340b4507040c088020524106450f801d0708001030503103809004a8807090990040d400c01c600d0241030001c15500007880d42c0400011800900038003d550660a031101510303451015103074010b20f800800203008901038204081c0846109040003a036500150500005890170032081a202003400030318100302e01e6040103000b000340218503207841d0120003080b0740b141715a240100011003a603040c290744038008800092580d056102107508050400d50a4103c0700e1140020b00d103e080c000090302a003510000801c21030584800d03202520300000e0107a02e030310008a503503041c001c10382c0041c0090b0816040c90605030045110030440f605090502c11400b0054006e0014800c0900034421283c3e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 183318381 1250 183317131 183317161
    0xb07020d060c030b06131a0412030c41030f040608040501020d0203010306140702010c020d03050a0209060c07030507090b0a151e0c1e030c0305030705040b0f03011409 73
    0xa8000c0001810894141040f001040009031031680708800086841d040c4100040304030071f03100c0843d40140302400c44045188144514868010000400080d01c8046400b903803d040c0c8150281c2c2c6000144410344200d02511140d01d00d8440a071580700010111207200e47c070000982c103038000019843c06c07010b071205803600d020f64828101000744c1c9000160402c10290150b4020141c842c03010341d16942c5a00e005d4001c0e01c1604500ba41d440002c400080225205008600d44152241c02500c0381d03400408044020340350060418281940821907070301c0340e4840d03c0c020300700005a90081d2101a0030b6150448c00e0680c035520120041742031111302941659034200d8001290544075842c140e00441c01c0c001e039420390f5a0002c074104144410b145a03605c1da04100800c00c00340c40340c0c402243c100e03242c0b92844c030840242c0030060000b0710301c40fa515000030300510040da04a002400c24a0416070b031103c0190841d40070503010100d6503000300040022b1101862423403000b0504503002c0d070040c80c0036042002108 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 183319631 1250 183318381 183318383
    0x19080f0405070b0f070f06020306090a0b061b070512030307080901020c0705060a0201230618130b180a030f1b030e091906080607080c071a041a0a150b07020d 69
    0x480001604c24500000360102c40c0583e50010300400d9007402c0c1d080040094100311010b900508104000940400191050400300c1200800d2903041c0906500e100c070103154200c075054418803c81402050700d039a445480309010658400465030b910700080010b001d0740c0c002d05a504980c0c018404600254400300300354082c1e410540f03100307480e8a0345041c104d016000401d91104040f07101b01030310314864100017516101c1c640503100d02c01c012070400740ba40580c10085403040d4103843e0380350360300d400546e00350f40442e00701140400900c80c00807120020703400c0c0312040f801240400c0400003001401508400b04044141c20410030515445082d02d0141010046030213451117249800300141aa403a2800c502800302c034503000400040e131315504600d80c1c802d02904c58030081521540003c003c2c6450400f114025941b00a4600c01740c0064502b84140301e4000d0011950310700c02c0f0140020710403000038610702c03402002e80c012840382c0001110882d20460b41d003107800c0348642046030501503191004020815 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 183320881 1250 183319631 183319649
    0xc0504140f0a15030e120702031504080f1606060e010b0306011103040b04090b121204092705030307080f01060c1103120a020d09061706040e010f0219080f040507 71
    0x4946041c00a01070040d070350443c400340250f844040240c00d52607030204107200080d10403580000c0600807041040d0098200081d03155100307a401d03850038640004030580081c070481380c640c146610981030f402150003008000c8330780c03c80c00341c40b0011322050340600001054801c0e416805035043c5075031800c142c40000d00e40d81c180150300e410046810001c004130b600030815012a20744a54a8807140300c00b9001004c0e0080c0703e281d0010741a0b11409012801d8806a86020440d91a0070718005880f800380000d1118540441d00c090501e1902c0d650301682015018480c001856991a06c0e650243c072880010b012000194641c1005100d0103400c2070400a60580201501c0501c3c0700d5900000d1030612149800c0c0c40c08807001c12040003540c1c00140d051000c883c01c0d16030300982030311030070120345080100380342d40040c610070000704d80300d4242548104403041202d000482e0641c03190145800380d03840503007080d5180102c4500a070b899507004d080d040e013008104146040500381364540303641d540001d008680384c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 183322131 1250 183320881 183320899
    0xa0e0105090a0302040e0c011d06030103140f01060f15080103121b15090b090c0f060a02030d05090f070512060a050606120f0a242108040f03060c050414 67
    0x240c2c0d9440740000159402081807002d062841040c80e110f400c3c01c0302c55400300b000c0700c03c10a411801c1104200c064032016059504580c43c603160f4610305c285008000d6902d004004031581401400e009080242c420008440d90305440c26419462506903210030800b040f1104005000040f542c201c100314a41881c50a0021111031110344041c83d8440e2400800000140360b00d212802c60b16000001118003842c41c11600d5030b22461415184c40d5502102030f0300c80800344940000e40f03404c5000d00009140b5104aa0610290259540403108203070784084659005040403885080e0800c0320f64080c0c10299409400344d59400300c5659030b15806000541c1440d103500001d8480d40f928801e85030810280071102d101c904100c680b80003064030079600d114903141003100910803c1001c1c0e000b0f48060300104048240b03503203064082e2048040d040000080100c5441080380030400d0700c030151010301110700c5040b01062a52030f084045584400200b0140801404208095460443c2c0321158510503036035541 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 183323381 1250 183322131 183322147
    0x109062303060a0807090e060609010b04050409111314060402070804050603130206072603010605030411121209030105130b0a090213090b091213060c05070b030c03100504020a0e0105 80
    0x3c0185030303a40110800384140d0800207245a8282c11031040fa10030b00d400d40d03085480b240c0a02c00c0d19142401903001d2210304000c00c2000781403641c44680c01c0c501807280000c00005072000201d0040c540e08110b41001e440f100354001d0b5801550342c0c150042011103086240c51620759601c00a8003071449810f02c16540400042d1001900c4441007a40f6a40148103a568400c649032448440340ca00d0080030070840d0400d400208031110604072416680c090719401c0c15a030391560707075100d1881400b248603000a0607010b2803220400403c840300081c45e47c01912a200c540d130700306040c01c440b002881780002a80304443c1d140403408400301c854104007a80e1001c610910140042191803400ba442e000c2140d01e800c00000c14024941c40e0240904801130945200418202c004440c0e4040c1d8600390000c1c04080e203081190380d011b0940d014800784a0030941d100103641e148502c0c01a0011a84110b0403c800020000f401404c5200c480c0074000c1105d0843c00c140348920010f240701018903115052000001d2030107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 183324631 1250 183323381 183323389
    0x12020c0c03060c04030501060b0304021c02030c060a031d0613021e061912110307030905070f03030806090115050306040203070c02150406030b090919020a030b0a020306010906230306 80
    0x881400c0107030071181030f07042c44905820203900611058645500c0c1c81d50100f0703400748000c200e07402140c0042900304650200b40a54107912003164ac12a41480744101c03550700c1e0b40790100034200c0c6040c40d841c001000c150500b41800321103a105078035040d5410500c1000282c11891548c0c2da03a0580540d03403007000e424400c100ca45440850103e00380c1c04100421317564035000303035002c2da40300103034440e6902c2442d509542c1480302a10440320803642c10040600c000f6540c0c5101e50302401d059801402200d02950b5580845500041035070000d400240804040103083c0c00d0506c001401002440c54013990001d1035140103185000191800d84a1500080841c15007489041d00d0740310160000d00b205078500c018041300030740f0b0703100303100341070110707041480b4507040c0e107850307001c080c410f2010902500c242c1804140e000410604082d0490340006814004008549209001c42c4108010100103980b810f0080014203001d280758071100810500076450280d01500c0903034103411584000300c65071030b41c403071100203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 183325881 1250 183324631 183324643
    0x206030a091e05030702010905030309010e060a020127020a1706010303030c0e27010f0e0a05070219030f0215010b120403090b070303060311030f03070314090d0f03031a0112020c 78
    0x2c505600848010001842008401002d106200341c030f604075410344e9801815280e020b6503420a021a90180301d49100c1c0c1020001045003144d24800004c1000d4140e5000c26009600c2461618112650403083c08508080e44104060304181000341415801c45203910743c0e490050000404260300c880380c10500900501d0201d100b0302c0c0045c1240c1d07c42100317910b6921000d24031120b0451600340c0000002d4100c41c3e1040042c10b0760041c1901904550307548505002500b0050700c03d008602c220aa9140031110070f44030b00400b14030079551030090620510740241361102080d912190550407000400c014981041119410090000c00107285e90701c0c0d00341a02c0105d8560312014800c080000c0ba4410180d060b40203030142e0b881107801940c50003801c4289a030740d0080c128404070580c0100302102c0130038026001801c82e4a00c0b2240145006e1000c03010070020500350300222084160038a18608054160048152000306880d02144114902000a001041203100d41c0b0185074005013400c0c41d13603424000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 183327131 1250 183325881 183325913
    0x3030e0c04023f0c03090105060631030b0c03040b01140d02190306240b0c0c1912110103050f06100522060521040309030b0a09020d050c1008040206030a09 68
    0x401c90744c03500d40c202902a50003203442606651a14001603806d15100c0103403a803040644404120360542d00703025404506074482c91000040d80d40302e00000060510980a02c11482011800e4503810545040f0000f2075041e0841a03100009100268030780d103d6990440c030aa40480310820403510b1613014940c04030071500090181402c0426075480c07401c00482100c0040ca04000714001e030b50b515001d03514940200456108140c1040c82044840e2030300840819030f5580c045800c01045550b003980344081011590115860b0091504241696805100e182c1c0d000840d280805611302d04100045c00050702e240405080c4840414001e8192071100420b0b40d20b0424108003200340340e1544070242a6801c12920403450850714040300940080411440f4003d030ba1644440c81c2d01400c0d5528180118802401084103560350b218210150751041d0408003624024006420341d080000c080c05000c5911900c0b24051001c00b81c00d000040e1644000c8a07800b8050a1002400d281d55107060a0f07042c10040c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 183328381 1250 183327131 183327247
    0x170a02220812030c07120210150303030b0609300106080c030c011d0d150c091802281806080601021006081902011b03030e0c0402 57
    0x4141512003a0044805681c0e0380c104961003810700c510482814441100c490304440018000c0394000340c0d0100c040036004240c0d0041ea00c560101085c43d000b00d900100e070400d08070118000420906030144a4107559010641d544c0e0301c1d10031500007140c03068510714038a441d10007407000c082240c03541c440c15040b9408440b41c0280140369036411041d603111404518a4402e0003140726407040c6600400e04035009980494801e0901804034080003410001c0040560344206004041c041d40c0c02d80b4414041d9101e0251602c448450a10000b1030006a03218803281d8454410071040199001882d0055000071501014500c00c18061b01c0c2141c00f962600e050b070154100080c00420010703001841e00d40300340303420303802c482d802820105404241c642c80c3c0309010454201350180310b903e5416142c036a5501d13006060104030205d680c0d170b604243c030306181410340c0081d541c0d45000030900c500780084100300208072800d5041c01c80d00e00c15051100510341821440b001508400d0384111040901100710081d045 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 183329631 1250 183328381 183328417
    0x120c030d020a060b060a020c131d06060414060901060c080405040203010b03270a060207020d02060c0a0b0a140121050d02031804060f06110705090a09060e010501030503030106030f0b060d0608060f010501170a02 92
    0x2610ac075966031082d50828481c50902d0100c10b02000c400b00894464580141480b0481e483d00348150f908500d80344e815101100c00b0000070620f41c071280015070003050f080301115603a20f0020301c6043c00c80d200510480905810440d10f9001c41c80005040748481c2e0841801a50380c1c145100141111700d1900303000390030000200d00000303050350202e00e0301c140d04e02840b03c1b85015070301c55188a040b5a1481c0d0815002c9000200501c0492014581c809140c980c1508943e03a03420079031905031901410714100c0d001a03200040b0503189151102c000500b103801a5000c1c0290f500303140032010039103064020340c0c04104402c1c291510780e681c100185001841d0103402c03008a0300317203060080040c18038590300b540c00318104032041442c030703005204460403241c101340036500396400c2a01c1100600080e12201a0882c0c03200040c03201e070790700c490090905a840c0c90340012203900c1c28880500345900107000b1040d02441000400003030760800d6070410003122210850b5003039943c0c006200000d0040404001c0010106 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 183330881 1250 183329631 183329681
    0x9050307090b090a050603060403080a02070c150f0203040e1609090903020a0c14010804030302031801050c040e010e070e04150e04150f09020f120c030d020a060b060a020c13 76
    0x542c410040c1c010140d0710400c11360b45140b8958103449040c0c80460b0554030503c0010046485600f015402c6481828007516004103521103a480001c2c540025622105040e0710507581d40c0c200304c60b54140300b8140090340c01c0926008494005901c0103201c4d02c1d0000c80090900101c520600e60040070f05040f4404000d621201c0c24029664440607004881042071044003085155100e90105541d4034140c0d40c1031030640d1aa0780440203504050300d6000354850720441024914400c1c0141881806100c2021382c031a440c150419000810690103000548080b03000e1145490b8050381d2401000c0096030701103140e160744803100aa03601c0c241d02a40183c41c09400b48000c201c1140510142c03180b020009214028104120300d00315441c040b0020750001c1800300d62405418841c4610002001140646d4421401000030900380882e02507503100607000030300450704020491085a5140c40155a1942805000381c80a035658031070480b0248075980500701c0b82c40140564101c4cbd15810315072400400c4482c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 183332131 1250 183330881 183330899
    0x112020a0302101e030e062a0a0206060906010c02011403040213140a0b03062403011401030b09060f013501020f040602070506070209040807060b0301180b0f040305180109050307 78
    0x7000c1055814005200d0b14884c4074468011403040d0166407025003629154604030009a00c141e440450039206140030040400074860050000040c0540203440c0c240341280070000c4265005101a05201c800502500540d034003800e015041d82a402105640c0d488500002d1601c05250301c00b04807041c10000120705400b41e00c400280200740c84207051000010340000c040d10307400c08460360600c011644001c030301c150394000710311141c04401400008010728035042400780310809800648449200a00344489078400708806944000c6404600d5000c0d41001f00d04c00b045510324911103480480703c03c0b008513a940300c281034440046d80800865450714004840d0042d078105100b10805070007042c0c070020380740c03c08904481d0181e5000341500915540c59840c403400307812036041a80c0c03240e070305c45030210717103071001d11921611307046c8a4803860885c042c0d443c040c4140e03007005214541c03160a040520001a0700038003510484040c451550340c06000d00e01c01200d500203d0b611055240c03085c80030000760051 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 183333381 1250 183332131 183332147
    0x20901060309031206061e030f02030702070302210303010e15030109030e10020105130204110d1404060e1911011110021801020601121e0f06050601031a090112020a030210 75
    0x7100344c44000e00610245400c0b4101c819910400d00424106086140030300b800c014085050905030400244030090000310604a800c201c4410300542d0010405205625103081d1510302003c070b0113103400d001a20b10400c0c176142d000600c68007041c1000340001c1030480c0800c15040c50b14440c0034000700180c1c810b83c20018150b9a000c80500e0060124407100781034070b403060290500c41c030310070100204200ba80d40d09000003450041040c2e0155407040c40121724207441400781d003003541d108540c2070700706d401c0070f043c00c40444200c0100b09171140e100680150f22401301541606095070401e520600003051031005031012280c16901751050700a05880c844500300a078007800c029030204c9507000b0390820100069039100ea00b030080e40c044880c1c4400c0c01d0000749501c1c00c10101a0049241c20440d518507580d1910420003081c0225405500c070420404a540d05204c1c4420542491070b070312100d4036582c070218110550601940d680544041801800d5481e8591f01000859021701150036030918480000c01d100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 183334631 1250 183333381 183333383
    0x9030109050106061101090b0c0c160602030307030b010801030b07030b03190b090706020c030312100e161101050106170603030f1c110304020a1809020a090f0501090207050d0813020901060309 84
    0x322450b0016905d448144109541c2690000880760a5114030070982d0154100701c075840400e1052040c0e4918910403d071508004280c41d4000b075441c0d050010010301903030003215215040060300c000403c00710305440482508080708e030400040b5181080013003030800541500d011620f1303655190703404c1045406500c1c03d200304808015550419152a01241c44103d0b9401c80365150f4410b00c141e0f8500d0111010003608464440b8898281a98030400e184001c00e044030805544042c203518441803d40200c046640d00b54000003c00c1190b0500b84040d00c0113042d600004c28941c41c41300080c81c0b41d1010011604540b245c15141500e0b40b000aa5091040384291244184035040900c0116090700000540780a03d47c001c050002a07818400302001000c0d00741032280416840320310480142c3c45140c01480504000f440c00f24021131400841d904ad00c6040e400b00c134286104004c00c0700429400301e80610044d07001e140061180c5c80704036000091a114000280d03000c11a00000156140c25900c03610b025 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 183335881 1250 183334631 183334637
    0x50f2b03090f03020a2117040620060a09020102030f030a0504050d0503090d05030702160b040602010e1605010c081b160b03060f0f01170906062409040c03020903010905010606 77
    0x100352191509114010b0380d00c8000d4008608503000c0c0400d80c1c40c518800c0e5101c182000c210700c2c06c070346912412005e003c1c0d101342c080c21080014042c400c0b0b035401a00d42e0794980058005204d0003c00140300b61b510b40006001c10320445c0e0f0342c5204401c43e8401c0c000c50b00070066000540b5200e003400b20740304005150664007150b052103240f0403c0c44540c003d4007036131321400c01e117400307480c484585000654582c0e000414000460158442c030407441c13440850741c10090306e0b08449172074455003030250183c00c460000e50400c845900c12040b5410600b000043c22050721803c0c600a00d07441101e184c504124014040d81051a00c5d2a9032042d00792100090011941c00c000031003102004e03500d900004003440250f41d0b5070f4001d03800305051076003030500c1245480c41074410b14194070440400003040c14054000d840d51240d40d08048144003061900303010515820f5482035150640a41d00310031401c81b4811030503858003854546448a404501903030681e92042c7d009002841a4949882d04500802c107501030030f004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 183337131 1250 183335881 183335897
    0x9090a0b10091407050a05030a0e0a03030f06050307030f02100908030a0c05010b151204030504210c151709100905010b010909060506040302061b010c0914040213050f2b03 75
    0xc1ea0f10300030724001c1080c0d40301e061420070701c40412101903000601d501401900e510809010010821446d031a590095400140c2c0441c94a40740c003e48180381e020620a03408150240b001c2250038403003a56803a0b04540e440303900714100000b42c1d01c0c98200d0340714480c240400b1450000d056000b403000035403103200700000c01c05011100c0c20040660040d00b07265216074401d1001e0990107045240c41a000b82c001d04215042a46c5c424520020865448100e090724103071001a10810501001001c00791100400c001402ca624400c010840240300c80c0d243e003000717008400714010140512102c0d110018441080c4801c00040c20128060044183c03200e00050001a000520680750320425064440040c0800c0c50285150200f10440c0c105c00e18680c50005424041c540c019801d1080c0c044100769901ca401c3d546141c410002c4011240e61070290182d401002252103010018a800d002e884040b01c014904040d2200071401015007640d40c0712820041210482c0c40c0c081094404000c01e21941e01c2e0744c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 183338381 1250 183337131 183337151
    0x20405040506180d0804020d0c030203030d090c0905010b2a060106030905150405330a050103140313030210050c070f080f010b0a03020d081306050306040b1206040209090a0b1009 78
    0x4e42d8a11004510000500c900040350061800035001d03201940140c11024489480e900024203680c00022a0094541c0d540c1a1004001d01054818018003400b0001c00076580b5004104a0b03500c40c401d46400700e00001c0f5480060309680c4818240c0c4481ca103c202c404941e103580016000f031421417403e840d54810321046282120b240051148566801806411510b101003510000c25006100d81d420f010012050002c510408210f4248181040280428607514504000c0030f40030305000e01c041e060700100080460201c40119000c101ea50503503000b051000740b900215068000c030304040e02c03140600764002803072a2024040e0801c2e94090002c1d103091005180e900c1e4225a005441c094010b401107000304091b10b000702440e4551800754103240c0c5048512065000d100200350000030100d02c000c0f00303100c124100782c440c101c03041c50b0035110205081501c8019503510100100001cbc45980315038001264010f090003800c0045500501e10806402c100c50011a100c8407805080c85440c6050b991381 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 183339631 1250 183338381 183338383
    0x1020a110a0201091a0c01020711012304030b040f020301020a020c19121412070303050a06090e100504150624050f0406030903090b0f091e0117040f02040504050618 72
    0x1942203078142c513800c0c0305a01e00b540018120703070070b83c0c0c402584500074081c0c03c1e100d81d42030005268081c421407441c1ca144660a001400010000d0b8030b4143c0612482245030f04840c50304101c03800e4a0304000310b030100c1d0741d55240054090511401c029003550000c074003508550340000d4040907564049a02001d071000d41c00895440390094030404107400c441c0580180442c2c6c1c032040c00000501c549064400c0d0652007405c510140d13205420860000760342d401000203420b424482c800150406000c00c0c08030911075240150741d1070704080d00601041d0b84101160070440c1d84000e000302200341c11001d019283c2c0d10442199000310b141c214020100c8141c2c02802030314130680460301c560700c000104508040c00d01d80201c0040a002c0350807028443c4140000ca800c2c54840c0c0509422110b00f40c106503039604400c1440720710f10204401554035202e0300624555682c0042205444000c2c50381074503441c0e502c038280f001e954042ca01c0043e403c24a428184000d0040100c5c010348609600141c220341083c03503407802 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 183340881 1250 183339631 183339643
    0x20712170c0f07030503060a0e010f17030a0f122a090e0403022a06070b0a0f060503030405040f090b25050304050604121205090c0a0e06061b03190201020a11 69
    0x40c942e404002c10145000900450145801840145c07050380c3c501d88411000200c0310080c0c2080c107600c01a40000c00c8a55601d19010b602400c0300030245042c003c8942025180070080d0100300203211404034042c1162001d5071007031a800324556030107000040003010030840445170b5801e450010f00701d010b000c9031209044910500840c0e256004001c1e8410030180d206072101480002c00d41c0d0640c049640e0615a1a24040c0604a0007500780a402d42440f200c00c82c00c9400c0c8404548840c1c0c14601b0070031072680c020080e00c00b00c03001510081680b03014081040014031240f803005204007520005e220141c040e03c44c0380c0724414900c16002c06481d003140420360b080e0000b2100109203611880001d4006a909903851042290b2410018554171000c002e13441a203034200d42030605a8804641d803862482c083c243c48004190340c0f40500d02a0418001140711446840090702d040c101e03140540030018000c1007140c0300741c04100c0b00c1102040d104032000b4007030344c81954a00000b07001c480341d07808401c6010800c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 183342131 1250 183340881 183340897
    0x703034709180a050a03030c110a12030c0e040905010c090e01080307030507081b0604021306080705090402060403120f08160e10120c05120a0c140d020712170c 70
    0x1c020305a03180c42002d250300b016901c2c020810b009001d100c40004130100590b55071207110b503d0100d040259500010480103150104684e10b9001d00d44c000301103212000c850350003203110316000c101d40348030604c00d4038084c1d4a22041c82c0c0261030300c04d509052100650180d0b082511580e1500030281d52603a0014101d4402e02a10f600e5400c02c10a10000074003c4006000b103d1003210f102d81030224080401e023103840070081d44001500300030100021490415880145c0c1100201c2c100403060a0101700347d960640c030f015050040203400c011a041d541c50805850065900c0460055140d40000e00204084050015840840c8425010401d5861307101440c28044031180e50b03404a2007000410400c1d0180b058100d001880105149020035186074040c00b08610301c03548606581e510005105108032078014442280140750540d09161036030310101894500b10440d2085481d85660400a030013407040c150001d1a45070034070800c28401d5007261504032640490328543c0007581c2c1710314410f407552081c0c0034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 183343381 1250 183342131 183342139
    0x3020301060f0c020109260609010e0d2a0302030a0e010c1110090305030d0c080901060e04030c050102041805070e150a050f040e01030b180a1707030347 67
    0x1654564402c030b021000341401458903814180e1f60340d004d00703110503a10000801c49180b0105401485004101c2c86400c00003080c001c112518101140544418244219608200c4007043c3d01c1c5803040386420305a80d05585143d0840d00719641c0c036000c1c1d600da000d501c610b000314104581c81840756000b00066901c160b04030307404011400f0401d04010745803541e90035200501418040100100b9400c10261002039440c100000b00a06c3e1a000038198510007804000940c0c1403040038442d540310580c820ba0007680c11300b000c400d181600d20f8854068000d0750401422581d860400c401c070035503540c1050380100003e071175400007240550144801c842d5222000002c1c43c004004a60b502c41c4600c0c0103005580c45040b04c54203041c1c5640401c40c1207042a80f05440c102160310502060300c3d58070031900c1e9103110030f2008020042c0c0941d034802600d00d443c60401070599000c034035a0141400703500003980e0105a04251205861642405181c09001900034030340a0501c610502518100003905000c4202c010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 183344631 1250 183343381 183343397
    0x50a0603020306010309050f03030a1401120206160b071806021606081005130b0f100206060904060207050604120f0f1224060801050915090a050615130f060302030106 73
    0x85010340107540003615a030304140d03071200000c01241c01800072442d4606800042c550f28103185240106481958a480307100c009000010841180b840e0303004200c2c40d40c140d44568076048555000c0c441b20350030210282101c4c6d2003000304070481c0e0b805450800520b9000021038215900d40c102241c0e2802800c0790300700e48110b2000d007442400d004585107584000030621070303030a183e150008500c541300009046201213485103c200340c0b620301100c1c000d98007002541c1c80680e104050b18029540c1d04040c0c004d900610300b04010405010403901242c541c0c40d0000110f82083c1040d14001100c040c00134030740740004804034800d140462091181d81d000f102590359810103180d685c031000000b04120b030800100c1001c45030b82e0b8103035407810301d24040084c107082d221030717490b50314200600c21080da000f0b1200e06000e00202c4d02210b1079441440c02c50f00010308080000b86a900c2c0e4000c01d0101980309418000c3d44004a849080540d100880c441a10b42c3c0321a5104915610b003016000c2c0c0c007003805610701003280d007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 183345881 1250 183344631 183344639
    0x50112050a02042703080a05070c0c030602030403260f091606050f1e070510051b0705150c070204150f0512010f020409060504200904020c0a0b07030603050d09050a 72
    0x580c02c810f00b13071003401540410a0040c90821a000242850100d0100350307070108201003402c00b885030aa0244c0e40b0b0402e100c11a0140c0d82c0c4410f0a01a17000041000b03a002c000b04041c10b00c00c1d010050300311300700480d51031440310003007981c8141c260032a00c0c60745050740c960001e2003840010410003200105801d110321528240300050301d090b0020038880e4010340d03043c400400c2400ca0101103809103085005525a5000d540c2070007800d00b444007058404a500b00000d00002c0922144c41d501c8002401076036031f0b1100b00500c0c0c661b0410100300c10380e00703001075414244201a01090000c2c004c081c0708079002c10003200003420480312048180700f89000605102401c0029090002d200e43c080c81c60000005440100c0d0344e001002c0381c01607000b00c0401555480188002d0900c0c4c880c451840130b10307404003441307405030310503c541910440c00707114000c1d6008500a868031100700b2840307003015030140440c04149400340c0010000c10b824403040d2528820300381c2c0c0011550107683d44006882001c5c02c1c408005040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 183347131 1250 183345881 183345889
    0x11802040f0b0609060d0f23010801020a0f0311090909030d0e0c030a060e030d0504050c0108090c0306070f050702090c07061b17060a120f0309091112100302090a090303050112050a02 80
    0x890f08280c180c00d07448008508000102d449481400781c0548c8034103810103075040c02840e2000c0144c0005003a60310400c150108550440c001c20381016003440c004c03a4800c007a03610035002e4044c400712560050a00c4c002c0c003000e880b01102510000c5082070b8200494084203480550300c203201c605181c2c064000e1900c0034041000381c0c102003030759601c01089903d0304640c00104400c4460841e01a113003a0040540c04502d980d202c2c0f070040e08040810f0082540b4894480080e8643c44007800c010300384200c903040f041c1d00d0b0340500151001c0c0e58004200303c41c58941001c1c081314940c0708020440740c880c9001e00c0c08110301410071070901c1a61580c0d4503020040c0340d0303004101a0f0280035040070f9004d210301e6800100703801001c0d10355030a94440e800600480c01c40e85409812500030b03403c09107015040040307000e411030034141a680c0380c81d00c501002c411a180e07051082030094880c0c00180d0040b1001c42045804003441c1c01007070b20288240c0e42006207a03a108a6610200303141400101181c104200311005490 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 183348381 1250 183347131 183347137
    0x302060904050601170702010903171e0a0615020105090c0109080304120204060f0308130608011208070c0f080319180302040b12011b09050603041208090f011802040f0b060906 77
    0x5410304185d180100e01c1000c050101d076040f02c503000141c3d1100241001c269101000d03910a50041c0218030480c01c00d14044140c540c4034000c5807002200080005d0f540301c0594011ba0001d200d80801b04000302100d07580240071b4202250b13038010522074001d02d882d40e54403e8110350111075a0b0000b4608090920880d02c0c8607203d000f000341e9000e52125001b01300030008540d050021440741030181d80d2004c0e40070b45034810300781030b030b01007820310060f680100580411055030f440d4055000c491103aa410300c600d009064050b490b00142850b111084012a9111002000300b140c405010544c48551034410421116501440110fa03400000301c101000141400d8000d80c0c40303010001c00120a4201c8070b850182100e8a124041d510754074035101010301701c1d0700f10317103a039018100942e0309030300c1d5203441d0711403940a00e1074488c2c51040249550000350b010105105804050380e0703900c020f1000be050302c2502e410646071038505903c900d280190f8520040140d10402c0400c800c081c0c03519050910200400140d90 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 183349631 1250 183348381 183348391
    0x121506030d020c1c020303040609031509050c0105070312140f16140901120c05030105040b0d08070f1b0b040f08030c1c17130b0c0a05030619030b0a05070f09030206090405 75
    0xc4da001e0a01001070b5030a10280014124550320400704501e141890340064000541c03668540740342c410210049400403030300340c0c452072082c240950b0b15001480d04550b16400c4001642e41d95240c0070510450340c640c80d940740d005100d003106000c980c0d140d104000c00d00070100840e074008500b02c10360322031200c01240040c0142010504010b200709007000a00016a00c0390f86450000450000040c171075850240704e200304036079058902c035401c85540d42c0d0743c03606072160440203844105800305040c2000344443e194800d01c0c0000d0600414555102c03003041141e00300e03000d01807040360705000210303001c071002050b9040b8074090340090210008804403943c411850086000411010441d074040c045041c4203da40203607118240002d400c20325040072104000080c00030712118804202051b1480d900c90f00352500098100c80c0003004803100c61100001c01415800100016a00c45c03c011301d02e00554013a9118424507190415801d500c400103c51500c480d010083d803006c8140401440c1d0b04140d031040d9800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 183350881 1250 183349631 183349669
    0x5161d130204091406040c11030904020f1605010207031e050901030c02070503190b0105010206013209090606030d050408030a03020d0b030703141513060b010c02121506030d020c 78
    0x40364559404106444c0214440c0100812420038085581000d11400304905038602e040900285400c4810341c492107419003891040c1c0d002300710151050340100c2150a03c4074582880004051545000782c080e400c400c00c141c022540340c07001f100c0300c01f1041601c0e00700c104150761524600008540150000e00600500340708500c5650701c0031071142c07410040c040e8058041104041103035240c0c0742201501d50140c111a04540100004114030b401d401e0a00c0080400d020344144413900310108111590a008545236010001806000040c60041400b0b0302400007942a100b0101d81420261090303c29407280c0042c0340e000f0454200402d2195010b4100b4441d0010081a50060100001c2c5000c7d80c580064801d035680448804041c40c0800007a5680e8001e241546c0d0320385041c5103496518200440044c021a442c0e010540090f0300c1500308000365540203180014030b40e140310343c080d41c62003901480c12410140c4004581c02c0e2600080c7c080c2024034650082406000b45410300010400020b030300451 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 183352131 1250 183350881 183350887
    0x507060f050c131a030106050c0f03070c030203160302010e06090f06071b090c0906050c1014060a080a02030318030a0605070302090a05060c070b22030605161d1302 72
    0x108030454041c050049041c100700ca0340321008616207a40f6800d19900c07440d416803100b10003603850f01d43c890a0301d0459400e03041040d06c0c0d0030503070086410302c403900800040c41c0c00300003100c4c0200090500020b094070b0080c1c1c11210465004230000181641c80c1c040a80805d00310f401c000c1d01032910380b0040c0700808000c0c0c03a0751554403420010409a80003010304403410385090481c07030741d00410f0404060040081000500416149100181c044483c9010306001c12a00040d94400d0207400c00c080c0207400e208280402405000c02512400302c8402e070741c194854607403020300107554080050554410f03a0001c010b90324181100c10600d030070100500c039040d014001c00000c40c000c1441c1d0702c83c0d107210350040c0e2405661040c3c1082005020080b54114910640082c4960800b000e0005500f605554003601c400343e55082400e44940715403029041020340c3d2100c00008400c22800c1d41051b800ad00e19a8004a100610f004c802c1d12a09010180010031880c0c9948100300c03407a0200c5c2c10f484001e2000d1006103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 183353381 1250 183352131 183352151
    0x3012c0307210e0312070308040827030c15040b031027060b0a0c170c010207060b1c0803190f0903270f0504050c040f1503141501050706 60
    0x10142594007246001451142c40308000d540d040440b81d12010070032000740250018804005130203004044025003003254910020302007100e100701300c52681750209082e0b007501481e079030b01d490f4003002c60320360078024003031503880b020700e801d02e21603c4880b419141c12150800d800c268040c212034000900c1480110500d5400044402d03104695142011085200d943c90b5415001140103803a0203074025403841c082000303582c01283d0b000c80342d02d40c01c1d584110039a0714400491042c403500e000381c5891405552000492a0400507503501c030007050141030761180212600115144800a04a000940402403c200003020300000a4500801e000a45000a42004400d44000403030309215030440c04695072501c0e85945070500d110031841d841494005d8400c0504000c2e020810400364820303180200d464001180d03400d41c2520548024000f000c10720400c01e5940c0d000c0302042080d03518142c0200b45084001d808051184d4925441307a03001010301055109a07030011207950740304000a440d401c2e55116048 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 183354631 1250 183353381 183353393
    0x20f040306021c0c050a0503181e0d0201140412080405030403200111010902030d0e03100507090609080a0515061305070509100c0c0303183203012c0307 67
    0x40450f00610207401454502e110b40b011511400100418042c081c441408000d030701c80300310f0b688050307503000d004030308100b00c4e4071980741c02c81310155415202d90310748004260060020b024180900316a00074000b040d0404e0031508111010b61b00600340b0104007020426a0b0300032a519034000303106504480c9019580e4807500402000c1d81e80740c0c400c40d028074212803139945c1c1c0014444002e803c42c800810052507641e00190351865165208024030090203100541307642c081c8001e4048403c840024400b9180c000ca00401007405070040034085040070401081d142c0001800d00c0f4000e50160007801030a00350410000d000900030725280c0d010360400507125181c2013030b0082c4d900859007512002e845001840401c65070280f0000c4c000200b2410682c0040810104603101003209d0309400c12104c04140d0340da0310100ba82c0240c205210410800300000f0603a0841c03049110a08803416001c08041800310415090360001c1c86911107000d4414401403152401611000d038410f420002c403803504440307903140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 183355881 1250 183354631 183354637
    0x20a1101060609050f010f0c1403040506191e020601090209130207120801050d0203060c091c030801080613051b220f06240c020f0a03050a0302070602070612020f04030602 75
    0x2800001e050100c080105050140006204003000d0803c00080c0c02d4552009140042e4008c01034003c078007504810351004010f00445000e8180034200076070f01e00d880c0740c0c418030040c1d00402c11000a03481005442451088084040724810164003812003030b4684070380364019410100c403150340491310034910782c101c408030b20003014a903220f0f0503032101e1164000000340c04810140e1283e4026031a903001080103a030042000d82d8030980403083c050f19504120040340d17518074490340824004e500c0322100b41c14180c12980003412600404104c5040d965130708900ca2055861140042155001c0e654a00c1c2803404600c3d643c00f00900544411007006611028007140340c818804070012030351303606034040317454003a00510010782207041c01040c0b80c0d0811500c485081104140e20020031520000810455458010161180500400f0058400d4607400c01903224071903844101c015200e0711f200020020b00214000d011110241c45000315404262000c0002c0c0d4018940d43c80e1b01e020411001c000a422480a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 183357131 1250 183355881 183355889
    0xb030a0c200109030e040606140d020403020a080a050f160e060f03010507090828030f0e06040303030f0b100e0f0d0b070305040507090b0a0b1c0c021b010c0b060103020a110106 77
    0x3041030703841820041c045c802050f01490107182000401d02800750450b091500480f400c1082668418500d81644024016500300075404113403524001400304000031040384a40c010015242d103504a40682d568400d0180415800068040001c0003001e005070300c4c090b4481e00142ca01c0f010382c180e00380007a08403401110b0071008902e40e083c1c103002d5020100100465403c0c1c03002d5034003111200c5600c1000c4071590007002020001400f801d060902e01c43c5654414506024108a40b203603103e00c1c0160103006000701d07606130030746011000701251903c000c607141128aa9152000c2d8285410144888448070503c0d00303801c070100905d8580001c030f000078540c2c8201c01ca40c0d000180c03800d00c0e14005003080070942c4501c090906290581081e951500218400c031458880c5290b5560601e180c1041c07550002140044110f181100a01c4403640114ad0100445d52006010401781c9800c0c006503204604071001402085520002505075400383d070092210040c10300b404240100d40c00320190030b42d500740d04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 183358381 1250 183357131 183357133
    0x1409010e01060602070302150f071b05010e0607150f090c1212050c030d0c030b0409111201020408030d020d090210091a040b090103150b120f0108070b030a0c20 70
    0xc54503260080c00c1c418a0040c28903840900b40c1c90345190000340858000100d003051400b800603801148510300407c4403506c0340d10a4030306403144095104002c196400380b1603240480c01c1600da07050326150290444080036400161702c1c2902058804800041002d03051401c1c505650f14403c00c0842c44036031010004200d86400c10360003c0b01c40c0b5110f0b40948680080780c0a1000a0240f0310b4409070100070b565548248207400900c503801070008601030140700020300c0d000f52a12180105124000ca034100c0401810b640082140146150007401c034860f80c030070284590010f100054445003250000d001c4100a14808076104100c1d0b0005809150f41645d002d0108008501c10030001c103164444004d8201c0803100e480c109450404104181e200f2081024101991440e900e41b180040b00a42000341c880040c0254664000004010034101b0070f0f140302125010040001070700c1d260000d060b8040d12a0003c3c0b007815620340d154002c3c05022440c0038802403002c405d041c500d0000101500e00d1454040e50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 183359631 1250 183358381 183358391
    0xf150306030d020613030e060d050717151302070804050a080304030308160804020f042903070e0403020d0c0804090f0203240319080c01020310060906090e0c0d140901 73
    0x1003050300d450a10b8165034155041641005102100480b003a41115054281010104e419400040303451040c0e80f600903c0354078050910100d0369010001a464a1540c0e000442c6929051803a01d03074641d03100030040c0d100801c005000c02901aa40103854040c0c841c1010908044d210000201181c0c981d41108940303500c00b02d41002803591112455800c40b1a900d001c03001006500390052094100a00107400394a403202c220459031926403069611031042540a40031016804000c1318002e003450b6400c1c1300b8420900b0104d80521441d0445000300d906400074400510701c4141500d2008020600f42c0e0300c01c1040c4000600b1008901503480c08010208005a81b0700e0309500039558081314440d041c40d040d10000301d042850320000398040e2403051064007500c0e004003c1c50860348501c0b03810203145055001106014282002c2c02c803030300035104517403641c46155840305411a05020f00d84501c02c01c1401400104030306c0601c140003082d62000e030103400314a415070411580e401e030105588104c1103a540e5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 183360881 1250 183359631 183359641
    0x6071209060c02011e0203060a031202031c0b24030a110c030409050a1a030a06021312080706060602030c0c0402130b160c0b0c1b030114090303100b25020f1503 70
    0x8001400c0340111740411070650800308041003140d0010300004000d040400582c00105000b04290b5038000310b064040700c1d401084400d29006000e1080c0414002d000400720340c2000e0001030228070805079010b034120b086030744001d46007000c1e010681c06401003200400c40300c07409020500040000d007036112404229410301d030300d200c0c0c102d8070b04504100e41c07900300070210080c603070f404101c05400a400140c00368450051030901c0b460f0380d90640c040e124610400060104105071400540500703401440104003140d511101070fa160300c01c01c00c03001101e8204ca0032004261616074040c04a003007200c850500c6050b101e401c503400951204181c00201d5206468410801004000c40b030090002c050030141480d0810400d2951401085d410b0b05009450202610301918250b05c500d408001090595030a803d01c181e41c0c0c0c0d1207074801d40d008605a00c1c140c002113402c003110700442d8849074100c010052047c0040c5030881c0f00541a1208a030b000b09100c040d160f0030f139500e034600203040b180e0011046d502d09203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 183362131 1250 183360881 183360911
    0x5070c140f060112050a021e0423060402040305060412170118060510050d1a06120f0106020106030b0a05150604140406050d0803040212070306050709032306071209060c0201 76
    0x5070304c4516900462030003000003800120703c6000c4240d05488441a22a0304010f17010043c07003203c4129042032030038821541c003880a01c400041c0c141c1440c5184107540b42d600500c8140c0c41a03000240940d400400460006005d00704405e08001c09480c20b5461140e41c140074640c446c8080c2d00c00b60034212069401a030340c0010380f068200405080325465490072420780064803e0040344c00000410b941e0320781c0c01414905a41c0c02c411602c1004200707507503900c8440c4d15804944404c0d5465407071180c0c1800042504c40c014425801965004240e845072951907070f08080240800034050401051604101c1d500f50b11a0400390025040d41d070450707442e0356400424070040b1801540102d04c10182c0070f40ca02c01080d898402c607074000ba01070b01c1c0c0340d0500c0c2c0c9100d00c1e0343c5040c1e0305601c0100200c0c500700820254540c800310300c1c0c05403482006000d8401146049218a440c0e02400851081d0841e40c04544401d010325050b250f180640030300032404071491740301c4204032401e900142000d070751214116001922 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 183363381 1250 183362131 183362143
    0x14040b130b0c070c080d030207260f0f0904050403020606030d180b090604030b0403090918170306030a08040306061e030302031c0603200f01030c050d05070c140f 71
    0xd014501008810001e80301d403003038400080e01d10403102100180d560148441a0120000360501d1821076128841e960b00042c02540007400503280b5011840d80d0300c060b82c0c000080344110345541058281084120041030003154040d4107507041821040200c4d0146860760f00400b441103020b40c003c0c5c009454041e0916003840d1010440d281040700343c1440031031803100391031910242c0d05c032b0f101050380307a51442004c54130034440c9400113030901260400300f00030580d0102c140c0080d240c02807810b01041c0044c00d007801010703805920042181d1050100c0c90799002060015540c0100002c040f00c1145010b80c40302c20096000e90000d40b010394988800f07001c010b0340800400c80d050790510646070358030300c0c64070003d44038001c030b014600300305640d568005800c00c43c0b43c1202c4091070304610110301503401c005000c80141c607403c410900881032060707000319a41c02485012030383c00903a10384030b250074214185140103040050000c400c0c000840849030104940780f000c05882307019070000f0304080c0400d04003e45042 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 183364631 1250 183363381 183363391
    0x20f1b01050a0b03030703091401031e060609050a050d030e0307090e1b0123030a0b060c1b0108060a03020607020307030501021914071502090406080d020c01180e1803090414040b 78
    0x5c3d20401c26000001d5014242c0011100c126141a4880f43d070540100c000e030100e04c0100c0d0141c4c25440700602c6050a0340d0000045030804c1e03c2d0340390034a94507000d12400401038424203501c42120303002d1001190241d1141014507000034242c1e100340380c4403020348084030a4180014001e92151203200c100740740c5d8400c002c9501c42c09091450340000c1008001c902c1d207080c500f102e00703181e801102241308002c4a4100301c85540c80200480c1c1c40f00f5070304904641c2c603680302100c081e001841034042e01c4554000d543c07150150501902e000206402d60302030052070b43c000441260188620000040841c4c0300b0700c060401700c2d00030036841031180c02011004107c140300300e07010030310600200b01c10b0b40007a9201c0644444451440c2c8007588918103400003800600441c1d0040c0c800e4081c0e240c094140a9011070300c0300e60b030b10098840d01c9004184189a08408095004010b200c9034064049440c0d034442c019401100000c01c0112071a02402e0304c0401c0035542d07982c1140c0072410041081c08108900c441c882c1c0d07400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 183365881 1250 183364631 183364633
    0x1401050d0e0d030209190819140105010b031f060f050a172703090306060d020d1202030d0e01050c090913080c0c010905030105043302120a0b010203040b0d020f1b01050a0b03 76
    0x414200544c05456910940810a5823030b00e0480c0c0804000358440200e800001d05d00003044a5039461250503010f84c0119118803400c0b0021110070910698401000142c4a040d034907641c000280749170a1320a03520600c84102405810b09285040f080220305140c842c00008582541881b0f1404001007090100d038210000c2c1d030400c0c0014207194600203045648840c04549201c0410500d002140c241d107404013014103145c0004021404040d00040200050840e000c130804c00c028081001e54221a4207075541e03d40354508000c988400d142541c0c60a40100209001076011141a034415207030342e0181c14407800035000070003c044a5a000481c040040000b50000d2215240179601c801811541e02c07820601c22a21080b4600040da500c45c0c041c0b0421800d440855650a900d044920000000c54501c0180d60038141901102c2d4404000d03681150403811401d410100c1c0e12454102075000120000d4a01e2424450300e10100c035920b0603180120001c600014207420074010010541c1c6c000c60026000b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 183367131 1250 183365881 183365929
    0xf0c011b0206070309080c031909120b0c031008190204050a02070f0f030e030a0b04110d031205061311070605010902041505031f150908071401050d0e0d030209 70
    0xe1500800c0440e404010380c980000c030144030740380c142d001e4007800508803201d104c0071901c03c50202d00c0711011070006d000c1e926040c003015511011220201201c0b8001001082c0040114a128504402564101c0241e0301d1001801e0b4607120014035114401d004c040203460085100801c0d41054440d141c0c0024040703509600c0c10080c0e840e00701110207000002440d0340e40904050003410b208011003105200000c0954054042c9030601421010b015242502c142d50444d01011840c9814a43c40007040d80c55200c1142c0350b070074500071600601d40205015002260420750160071500b9200700c6d041d00b64629641c0c0d803110590300380a0220b80058024480030340c8100400c0c018000920b44800000d05075281960352a6601070b100010103c1250307680e002107944807000301d04069200c04e100d00c50040c5a5071038042603035800c002c40e691803007031084d105240d801032540240e551184000300342003600800041007940109000750b00d00300810481e900081e5000c0383e5800c0c18603046080d42d1003000c1021000710 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 183368381 1250 183367131 183367181
    0x15090304031403090916020a05070609090f0c081906080d0c0b10080c040f140103050706230d1109030d030609060501030212070e0a09020304080a030e031914040b0f0c01 74
    0x182c96007000c3c050303603944540700d83c6407080c1603c201b08c40880143d01c907050740c1465035a175201901501a501848921030b0500540002245140c400d69000301301036070f1081c07165202c0d120040304400d600d5544241e03180c0c46440c042080f120400c116903a280b40d42d030b2600030401c13003410100032a0002800060b10070004907410411514001407800c0300d01d608481c0009c0b41011800b018000f0114090304810b04a0844000810b106012800c50304586894075001400c071800d4001500c60880070850100010b800c1c04050900c498a600c00b21001a02d40b285924000521000919048640b60240c0000743c0780c0d0018803100134070f4042d1000030b1100382001c0d03040504202452040050040a8001308000c0311203040d9035035079540d111001803881c5c0c08215624101400c1050b42580943c507200b01003410701f1100d5003120800030840d18990001c55036002d2449e1030540403a1000110009440c01d80001c0c800460784050020050140c5005102c00655801540070351078207462010111880350004916500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 183369631 1250 183368381 183368389
    0x10e010c0308010911130b0d050624030c0706020d05070906020f120a0c0f0f110603040f0b0402130608160621180b150103110309030a03050402031509030403140309 72
    0x2e41595103044000c615000c000107500e0180c041c00f1400105090710b60400254600041e00500180032510028001c0355961400d0140001448198081e100000101211045403140c05075400000c0195024542190340e20340d403080c0d0b0000c20b0a00c5503d0342d078401340054903402c130340914010147c0d800609260180143c2c4a0b071682c0c494030b0b08400e001c4000601d120824800e284140d1040e81c445051182c510281c00e003009000a01c440844407507030b0761a0840070707911b00308003500e02c65036208800000440c02550340032040300000d04200e80025403141d034031800101d14021540035250f071200030510f20420108039645811607074464018410100a450706010714044989122900c585000c640207036054003602001c0303010200a00381825040c08c0c024040c0940f04e443c040c1c840c5c240da0a0000904002d02c2182070b03c001e50b411403440c0d008010421542d0b000b50012a030050004064851607030542103c103900c040300b00d54456103038000080074010402d420060720f0a040100e0300441c00c11507800081 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 183370881 1250 183369631 183369647
    0x603010c12051b0c0a0302011119110c130905010605042f0d1b0f1d1c060608010b130608070b07020631170c01081806070509010e010c03 60
    0x6150150b1503400103102c5501c0d04000c21004403070000c000740d03036202280c522038a0b40c5102108070015400c02d0a105e800c60642000e0b900e040101c1e111412403407600b81020744070003021100008450080318103041d01a960044c0c0e10b40206d031400b00c0410144818035209003101c541c0d8224501c168036081c0e8000466000191b4001d0f03520080380300440c0c01085040c4031150f80120b1900d80700e041d08080c081d50212122a400191a500f25168024050386c030103800c1d115001c0c007a5030b0900340e054905200020749400c23400b0711402c00710611100d18044079504c0300350643d203407500b094000740c3d191241e94202d4200502e0750140c0710b802c100200301043c00c000c50075454084500c140c240514021409601707541d01c0c0012610241d004035074132040da00d140303000340f441100b80354030382420802d81c04800204800b100e494a00340c050040003624103200307608015240d194020740751042c0c940c0c160760207122507002041914000d007000d40762213072600d4188000500c2035403000001c604200301c40440b040007a40210074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 183372131 1250 183370881 183370907
    0xf040209060d050307050705041103090d03180c0e010e060a1d060105090607030905010f09081009240b041109030307060c18030309050307090506010c060b010905091e0603010c 77
    0x4032080e191036030000510680724010003d45140400030340030040090009504003120401c0d202840070106000384002640012942423400d50044520901024840c2e03001c0d681040514020070a401030580b00c5c81c003903803495001503030090380d00c90050001d034000c0c0c2d0030309510800c11520010000d00b00300c2090320710444200640c0c0441010303004940580e000d00300792180d624010701115101d4209040052002285128a50200c0c10700303a40000f01c2481415600e040d00c2e00000140174910299114100920701840d013520344411035007044401c1d04d8982040c52021184420110349031400b8400c000c01c44200000140601c034040160992548000c000c0c2c49004e03402190001d0700512001044c0c80a01c0b40707079442c60725078118400100c10541c01c0704003031059a9081d01201c00740c81d00c0d64181421a0802d50711103002c40c1c500c0007400e0004400e9008030440640615040b6189035813000458503484c130554194051984480103a24070b0401c8201030390344010228000d02c4400c15040d4060640448142 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 183373381 1250 183372131 183372139
    0x60a0b06070311120c0102030f070806010e1903020603040803010e06042304020d3203031003080307030f2c01050c09060906070213090c0806091207060b040501031214030f0402 77
    0x500b1142810180102882c90903a010380d00e61321762146181e14000c0d80201c5594070501a40400b096510b44038240f064498141030b1a042c440c2c00ca00020821101004082503200410354400400103884a201940c01540301c2c40c0b403540c40394144907182007840c2c2e000b01900e004d14603241c4905c5506060950003d00b00000000d600d685444500220b0341440d4940406000d05090400078005141000009640e41040030072044104021003025601e91200380c4441c0d42202c441d9105002090740d000086030403030b019040014081c9105181030703040c4d86030750200c10b10f60b04841d06454a0070349403004280e003002040000f0002c915040007101c416024940344507003c1c0d5030114000d01a40c80324801c48104580080260106080c00c0f1001d1020300001c000403a0014020074001428200c00640c03140075124036005400303420950350031780380b40d5000321300d06652039901c80c040a54a138550b807140741d0117940284a00c9810070395680002e8140707051540804005102001080f0800102c0700060ba00590b04176 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 183374631 1250 183373381 183373397
    0x10611030702030a14010c031b050309031201120b0906160509030c03010501080601031704030308040f08041e0608160206060f010203070b0c0418020a05071518060608060a0b060703 79
    0x2a054654003440700e00a4040c8a035031190800d1020130044510b9405950000340140b80c402107045041e1000c48007090780c2000480c07140c4100f41c0c0140c0156a20100c204122030400c15a4501c001d1031520a0303110003084411440d260b000e00440368086c6178400440d900620aa05021404210b02d03149507184108100010440300381580d000d115105203040001c0c024001561500810b64445800b807004546003802240c52601c00d0300700c403054408603a01520b13032101907981d90b1101d00c94080070304030441d08180300300710100d202e11340c0510195179a81c00880038003405050800242c004032000e0302800341d0780d40c024180350916600181c42c40d0f11900544400444401403001070703145000c2c540c0010320305440f1900300703d901807241000e001141c00d440106440a00c80441c81c500b00e01c40e4031442c4000070810031107000032500b0130008042d4407040d020005060700400704001c60280f001d80045524580350704042150074820000a40c1118a0100403c80d910b403110004a15200e84080182481104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 183375881 1250 183374631 183374657
    0xb06030a050903040f030804090e01060308030c0304020a03240c0201020c120714010c0f030606080609070810030203030c030a0e03060606090d0507090c0903030f030b15130305030d05100812030106 86
    0x140300369001001741134030709010a526458020745581050088010807441c1c05210580510140154022203030090261850358443d1022004240c0c001403099070000680000000000d07c0c01c01001c103c650b0b6034108a081002d00b668107800e480c1c1c03699014046a006000300f500940b80440c070889d01580044400e03035038049074a0702e981102c0c01e0114803110740d40b91448904a180e0480d260320030800f642e45d81080801d4039843e0036601e00030f060752103d400101c0f0f0700028403228001c110250b0801401008110280e541e540003030f2035a03100d800c0a51940c0c10129080305c1349a00018800d808403012070181c2203e00e810b002107400d50040340c03003052042c00c070045110144081409041d001d002f1320241803202c07215100000d04032131414842280040e01c0c12120f00c0d1100d100e4424490900c1e0010a5400412000e4801001d1034002c00304401001a40318000800220200300030301625840410114040c50000081d502420301030748400559000300d0200c0f01c0c2314840c441181d05460301800d00c4010b41c042c1d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 183377131 1250 183375881 183375883
    0x2101e09021c0605090f0703050303270d0509180c0702060a05070b0106020a170a0f050a0e1314010f0308030705160b07030e21040e04170304110f040b06030a0509 71
    0x8089440c080d40740341007000702402050b0700424800c5c882e07407045401403c0e00d02560b0b80e450f403d0348405403042d007052020445000120b16002c405500055143c00c6210154060908100c1d1043d03c5401044000607100282d040036401006d00850f2510100310528255850b00b115114001009200e80000035106442c507018409803810950011060b81c855a1078940180d56503480ba0410380c0c840040d11011040030001004075840d010b80c0340d41c1d005000b20200f01c1690103030010f208481c203000610202c22115110680c01e44c02c200b070f0480000ca14000d246600600030300048c0c00060b80c00007042014804607203213000301c0c0e0300041140307021030351001030111283ca10000450300914040120084c045c400b075058100d05000e001a40940b90041010b266800310840d044410814104041c0420040e07661044080756109000c0c84610700380810000910f08030358000c42e002c0b0b500c08241c0d07100580318100081015034155098904011181400001132045d00000b002c0c004880d450b45c0009041040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 183378381 1250 183377131 183377149
    0x40501080f041e0b250e01110f0d0801050f030601031e08040b0315010216060f080411030303070903030306050307030b0406050a061802040503010b272d0702101e0902 73
    0x8190560380603a40e114504005000b10070348092003000c11940c4082c05d42a2145840c004184460b122540307850341e000c0c010345251008000b05002400f4002141021100c2401003500d0f9240580e2480e0684d070403c010420541c4036000c0b1a40254820401440082c900012000c640e0700c600c14003155801051900c0d1a0b00d20540d000780001407408418443c030b8001100e5400c044117400d80030b580184087c4109140358061600c0ac1000041660111108590289401d2030b08140901d5601c000030132004042841c640c02550b0703080005120903810824140c1c544650809040e0440c00b1b000480d00d95182d50b01c0342030700604090710190b910004a6071030101c5a2016004004100035101d01c4001c100e80030009411500c01c02d8005e508058015a1303d00d0420401c095160b41c52030400c82500340120703000b003522801041c020480401e83d216030245940310f0981c02c502005603007a2440303480c03d0040282400a4500c62130002e03403c0c05d029a95000343d521031780c06030403110040001c0b85540381c000200c0e00d203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 183379631 1250 183378381 183378413
    0x50618040920040e0d0c080c0105040c0e0a050105102106090204050f030a0f0822090906060b090a090c090b1908130506060f0a0302060d1506020102040501080f04 71
    0x40c6405070550800c00200c0c2600c00754164409107222010b071030350511003680c020050b400d4998010500e00e110850080d01200540c50081010394100100c1c69038681c00c440042d101550305c20424401004440416100c039540000030600a20441d4504400b003094041019400f805018140344d915075541c140c2250125402c25040c41400120354480020001b54018018070340184080e2180d0740b071034280000c801c050258480c45180d8541416100c031040c0d604640c845000010858003120407400600c40440702901c011400051120254034001c0b046604550142100344810302620002c0d5549408aa00f11000c2d2400400d2244922004461010654101088050300421000080002d00303914651021a03a1507400b51521007200c50070301034076640c100034419448140003074003508156050754005036000c3c1c0070010060701c0398009516504040b03003c1803550b07a0340c081504617440c0c200c0d44d14000c0c80c460000310b184c141050002040d07624010101040c0740d4094000c1401c0244d454041d072512 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 183380881 1250 183379631 183379639
    0x1030201080601300e010c142a0105060306240909010204090c1d010e0901120309050d08090a2c1003060c0f090f0f1202010212030126070f050618 64
    0x81903400c44c0700c5402c68440ca840c40091460103844031181c0805104900c4030000d10384a030403403e54501b107080c07281c0d0b002c0038528a940304c4044080c4100314219a01c06100d0510000105070b9182407003c1c10f150140041c14001c0e030000e24485024108004405c1d421b10b1f075019a107100c01988e45000c01070180c480c1c2d9000c3d4522038078066040e02032a80c4612190600046444074104800003000116a4107001501f0036a000f81d800c1d00400020042d15100d019052103800d2012003650780314001003840c80140410340e05980c00003004400340c41d203c1c4c030203030207060101103480a515141c1e03011046914500c00800c0c1e00d02040c400f0070980c029080125004540c010024481c131200a000103162030703902e00d1410086210f003200441c20390b03441d5440e4820380e0340031128401d1807403902030313604c3c0d4440050905034150b00a68140950301c03100e5000441c003a020b11540b48000071051f4521020301031020790040515008200706000110714002020111802110758a0700c0d004032510307512201e0211250700313a00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 183382131 1250 183380881 183380927
    0x60c02010b0a1e080c010f11150106030911010809030315030a0209010b040e010902030402060904050c12040506070e010806030601140316090c0e03190303020a050d090b04050d09080601030201080601 87
    0x3080e4150b003410380303001940b143c0d00c80d00140e58601490740c0350044001c0c00d0100c4c5c104c4504400f402d00c0741050781c00340c0011104607152454540c980d1640c3d0300c000c0e040240000e4842c03010b1740a02414000703a011624080c03908600702e241141c601500c80c00040e14944c0d4005d0a0840d050140e03034100400c5901d690010981c0f000340d41c0d204005903840d40580710708040521343c0800007030310403030510a90348119006842d451411041008010051100501c3d4413591813090261040920f80820711a00c154410700c01000242402e507409401d410a602c10541040101c800b00400c644000c81c51604444044000ca210b003c8003000007401c100008072881d101c1084c182c8000790303445c8690818001070b2600e4030f904840c007121a00307150325841500707500081d8112840b11003001906c654001d1919050518281c0d040c522200488429503508200c140c44210400040c4400d0100a00c00303000c00b5002030502c21001450070100544410051002030b050106400006840f41d01800c500341c43c002002e881c40c11 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 183383381 1250 183382131 183382139
    0xf060d0203060f07020123130c080a0309051c1515080607020a0c0e071e03020c150a0c030209031902040f06080d0908070f051203040302041107031b0f060c02010b0a 72
    0x55000f104a580000540c201540e4000842c202001000644c00000e0450701540c0d55a0f21246600c0c01007204032401d0b145a00c000803411400d200700080140b00382c0c1c4900c05d03e40740108100d420000d181010100c10003a003440d1002130001121074080648681e00480c2d28440c02e414090f401c03c2990050f84a401601c08014440d540400d00100b90351140d4100039286448500c0943d03114030413603090010403404a941d100d00381480d20620003035403a615000d0728014800c4850782c03c012622901401000f580c0040c01507440160182002c0c06000f46011804c003c140700010391380320000c404a0140b140701c40c07108010354803030b50044021280c804a090002c00d43d03459055070b540c02c4041e1400000303007200002085c00b40000c22200704a4101c42c0d001c1d130704141031a040203050751960f6440d105601c0100000401038075a0300a62081e48901c1d4252521011035081c0505048460100049440c148009070b40c009001e82d404e0f05011504500000b488803410b00040e80103000c0c101c00d2a07800204410005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 183384631 1250 183383381 183383401
    0x2040308040e010e07091202040510031b030b0c0a020a02150702090c0309010b010f020721060f0c1b0203030a0807030905010501030c08010c17060f03100f020a0311070203060f060d020306 82
    0x70b0490b14100c10080c0c569031740260072a000405400f0701049610820f20110141c50545c00054010ba0071800c0d00200e55900da90301001884901101c2151410100342041405001a003282e0301850404100d03242c947c0301a4001e441d40900c0306d000748034114404080f41d14203c0c013000e81740c40760b6014104404c1420301d540d00c080c3d160012035804504c0d40c284011012154030803d0540d001e09001d400030b000300307802c16030304c0e0040070b803002c0c1d081e01552401c030f444401040003801081445500408001200b5002c03040040103480c661145c0d0783c0150084900d503005841c00000c8a02c0d024481c0b80c0803c5036200c0d0754040700035010400c000b03091036081000110510106010303041c101c031103d100030001c81d110020250380c0c00d52030503030010402c040040002c9050822170141c1111401c000e007510060303048120310710308a4001194402d8165404981c10742c50a8040c4504911404102915400d1102e284d000990b00c1500400503400c25050b600031454580b200500c2c8480668020140d8025280c003d48c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 183385881 1250 183384631 183384659
    0x110c01090516050f0a0312030b0303031f15080c03071412010806011d040618080301060c1a0114041509090b1b070b0106050a0509040903050d0509070b0a030b03010204030804 76
    0x1c02c032006441c10009031915020075516005072001c2c01c0002e405245849020791a2010070140c42496165440030f0070f107680c240011841100a101101101e041e1390244462802041d00400f252010350003183c08599044000e255110001041295480d078a11404582c46405003180c4904050003188080021542c440f10381c3c183c030420000c44125030b03a10912036030036902e0b1081007200003042c040480c0101c4c6503600602045241004c2c1c2e401c2460142d600c095040c0d200341d106000050380880002d0030050700d030b41c001d103022452b420f400295505140b0301e540548550b1040d80c0c4501d5540c1060440107440c0c0103514000c0030b081000300000c00035414441441c80c0112800702d00b0b80c64150301000b43d4103041050b14006034000c484d00c3c000d1781c24460141c071660300224255081c08003c1c888111182c4d10307805000000c0d8420b84e18643c5500b04004c0c0003058a03000780c5054499001400c090007001c82c10340554924001520700418001103da010034020300c92a04050118580040e000c03807001605140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 183387131 1250 183385881 183385903
    0x90812250812150d08130506030124080601090905040c09050a020c011d03090118230f03010b011d120609061b040501080402061804060627050603060103110c010905 72
    0xc1e0102da41c812030305a900c90802a0315a90000d004918038000c201c248019180c01c0700700f0302c3d011000545560008070203820903230000140c1c01d200400e20045620014a0070304a0015041482050030030344000b07044900ca901522004646c1d5000040034000350700e1141c0c0090082040c2089a4240104c3d440046e6020358003940240d820608500c41401d01d144440f07074030300c84050265050018410044440707451000c10031700010302121000c1000001e42e07460320390000501c159440628048802d02c40700c503c580700441d00c2079141a11035a40c80e41c12000b8030b84080b0b0051100d1a000626100207254101207054480c5a4405c400800102c22000100d150103000d2240b0082500714400341a440743d07205034000c0340e0021b4042c070003080040c2401005001c4400d100c0000b910000905404038084804603400b040014441d9002d95402007140610385a0919041705000510b42c10400070034200d100c041c141504065481c4050b150a502d81c030284d410340408007000381310b840f070141402036850440c525 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 183388381 1250 183387131 183387157
    0x405070614041d07020703060606050304300302030601210b0108060a03030e0103091e0c05090604020403020904080d09050a050c010206180613050c030313090c0908122508 75
    0x2003008458110070701034408548081d5150709500001c4107081c5805040070300351506500c80c8100200c00210305000341406000e540d0b5941d030f2245401c3c240541c902c60900070340c0340e682902c400741b001e5645c2c43d540c142d5a60300d5242005070740d070b40300c09004070f41160105103200f00800e220200d12460800d190480101d8078000d9a545a0741d07107502e01002083c441520004003c11810030781400d842d4020b40000c0540ea0041c00c3c83c1c045c80114048411403200c521030200d400110603001071080d40303800701e120f5400ca10281d074114209030841d400315410440c050800303040600c0c0810002080322039900681991603000081d24180101e500c1c0c01c50740e95038125200b5001d8040e00c00055559034000d850143d217060524000c041076182c8c0022010114002e44040d1000d00440d403485400792010001464900705844102c01150702d40400f400031280702c0d058080420043c15010070481a001848041c0100c001c00d034a90389110102d00711000b5240c6090f5848488203c00582d8188070840014001004841d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 183389631 1250 183388381 183388397
    0x11012f031902060c0307030c050708030403030b01020709060f06080606040302030115170114071b08030910060e0f0105060f0d09030e090610092c09071a03041104090f0b04050706 78
    0x11026a15140110b40c00301d16044c080c8000b0b05014460382110720800d02e44d042581c94504c1c180c540032415441213030107501094556010040f596810089540100f9200004125945c10a004810060118800c10b810000c0c5c1b0404900c29544210490340290390050007001400c010202c00140e0368503d00c40c806001210303850b40e07480010706006142d00d078141410101034580da80d81c015a00c0c0c12100d28141c0c61079200440400004190310029400341c40e160005050b040000810003040d03030466084612480c45078410320103074003040480c0d08d042da2402c80740a5119095640da007242805100c6030165860f00308041c000901d5000850107075288803d80d001c410540c0c907881800440d43d08a4000400101118400c1040f400d41c0440c4034600203105404542c4005403a0306074030a91010394603000180c101038000c110401c42102c4146a1403110440c850552170142c0b241d1141079240c90743d16008503203030817140e410440100d000d4144194801403400c2c3c035081500300541c0e50900c900404010542c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 183390881 1250 183389631 183389677
    0x4030f021507080f0f0c0f0105011806080712020d1e063801030609060e060a06091406070c0b2101050a080c06070f150c0e0108010311012f03 62
    0x501c00c031880e103078120440c1c92800c1804902100154004900c030000c8031000d210b203101a50f4203004440d20302100300008113165040801c82c0f01c161218403c8500c0c40c0349010b03c10050201c1c0401c20500319000c1481461501c17295001040f450811002c0040142c03402050b00604602110041408640506000c01c412180b41c5041d24040c0350018401c0c10078080c3e100c1303900c0c40780c241c283d0001c051a01807401040340c550303c2d0502b10030744110f5003110156501c40010451141000d014140c01004540b501c4000c0510f410b0315040c50022070100039024600020300d039070034424030f00e08520080403540c044940d6101300e000803a4000c1101d2820140055410700001020b00e04130000f0702c1517840c0100a001c00c0c0384400c4c00c21100750700c40401120043ca600e003502e0049001e0800c010140a0405004603941d041d600d4010f04d0a4038200003641401024801800480c1252044040e401803c1c02e003a007403a00321818912201c3c604800d9001c1240050b000e000d10341502202900707140d00001d800310044d00c64 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 183392131 1250 183390881 183390919
    0xb030313050f1c0c0f050a060c020405060f1002010f140403080c0c03040b0a02030307030606021f0902030a0f15180b06090405011e09020f060f070b1909060204080f070503120a020f0304030f02 84
    0x10310034680010070103010340307014bc0351650080e5000340c0300400740c03010f982e48a80840c842550300c06074500580d40d11014099412401e01858a40d130506c0d1900503074915081c0d9007c2c200c5440034000400c561004101c0000510042046401810310b80310750035140c1c0e00981000390fa990044400c080003030b040280c0010070f9400011286200001801740506c0c0d0001c0c04030301801024007041c286c4c0d240c0309401c401c00226040c0400c00c0b40c0280039118001d6000003641c0b070f0200340d6040400030b05940204085080119803071030420341d000740381103c110440341c85a040c580d01608204500c000c040840840d4481140b00c4d642c06290801c0c401d0f15a00e00d004002001c21070240101941241440020040c40c1c0c0050b02c8001c545a01c494440c04c001d0300014000510700480700a11011136002c0c0c1c0c0020240300108041000b401160585002450036a0800c0007081d101d00d044691a02080f41c0130503040c00d42402400207410440c803080449885036520301b80354912414030002a40240030400720344d001100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 183393381 1250 183392131 183392149
    0x915051005160503160221120c030904020a05070320030702040f020702090c041a040b030403051c0603030909050a0b13020313020913031103030c16020103090f0c0305010b030313050f1c0c0f05 84
    0x2588005000412301da0301c20703141030754400c2c09121100d000400280c000b55980388090101d0540550320b00c0e80381c140500c0c01904544c50f4004000d54251942428100c1f2980002103986566041d1400300c0c8000308240c0071030107401600c00c02580400b1f0b010400a2001003d40a0011111104001001409a401513011a214a0240a603070a60400005001ca80035000038403030014074020b00582240360104074412240540c00885c0040d1841100f00300f2103a507801495044000300904004880c088800618848180401c2012140e004400211000080381c0070160f40c54020b401e803031403032a200120018000d181d140403404546004088044940e00000f52846610400210f51400d00c070f00c29011409034004070700328100341c0c944040034000b8a50640002e01c280c820060005510304601d412801c0d030380c241350103600990050141400d00d00300c0e502d0310b0f4200c5074281d8005201e10f0707801005c20070050019600d400034218000b0b0020400c03403007041c02ca003150800302840101e1500e0303000f0041e43d08 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 183394631 1250 183393381 183393439
    0x40b071214181e0303250806041a03120309070f050109062a050f0601050f0a090203060a0909150b0d030512090a051609150510051605031602 62
    0x10310708005541c0001444844001200c0305088408000e11411940d040320485141504907801c0401071041500d1060406072903404e080d00020380c4080704070700c024810580240f401d8030950311065042c2c8112258003580b40303105800340940340380c91068120800d03a980140d0700303d021480f0f00741000940f6080e8141d0301094034016919160440c0ca40101240c1e0000e001c000030040c1c15001c0150808940d00c1b417014001c8511403030180c244125018895801c00d03805130700240c0107907140168045c06695104240060703d45103000181c0307070f445510200b40c150103160408001a403501082d00c09000c111900c0407190040b00806000d000414006c0c00100101d607840180401c0040c010390790284c0444103480d6020b60600304407040d165840c0c48040c80c1070743c038400751042e21842c0d80b402c1c000085a4050501c103241c4c140d61003144185800c01203843c080c50140030004006000c90084c500090701104017607403d40110440f51140c0250461548000310702508a211302800a164000d040342381849041d0b00d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 183395881 1250 183394631 183394661
    0x3080c090d0f030302041d0105120d080a0908130303050c160303120216050706030606030c02010e03040303140706050901020306010e1804020424080c040c02120f130905040b0712 78
    0xc0d1400d540321101442c0d111030480506409000106000c0a5810100901c403081120320b0400c0d454072050085910f244100380c007454102e4100d40c40550f400030176080d040000e04600042007800b038186400c035806031403200c04c11201031074000002d041c0d000303005d042d064011106440c1c2d03c421510010140c80007038170008000c1088022503044094240e40a000868000008400190056a2460f0408145411043c0800d0b40c034541804029070520800c002c44510b40002c00c2641490081b180d9a4004c3c4c6c0b00080422041108580c0f91f155003806440815a000105004a041144150703010b50001c8407600e0004401d8801814107103081444a140c04c0c084041031074194480d5020321000d00000e140e103011107094008012421540c801c91040180f00680140c5110604032082209590046206030b0841d440810750f40100002c0c5011205d10490f00080680c3d40e2140c0c1040e80564034499004d40c01041c85c10b004c1005005158485da44100d104c0e694011400c001403005800b160842070300b107540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 183397131 1250 183395881 183395899
    0x10b030601020721020f040b04050406151508040f081c060305010c050a170a0e03070c03051e06160c080a1101050f01152d0207080d020d0807030c030902040c050703080c09 75
    0x140c2071040c10038620300e03009040402c1c1d010002c0d001c2800c0d85c1c0284c6044071141c4d4dc0745d035000e4003450b00d00031f5040a010401c2d5510580220034000070100d40000d0400341c803466849480d082000011002c42d1110b41c201e880c10781c500303001141650700070416407005503520350a04028950180c07080084607400c00090300d80c001ca070402064002c0d030160004161016040d0b0700e06a00b210048200040c2107d284150b4020140e18203503d45107007040d5080103216400f400b40308070310031207180200f001503111580c1710f407841008040c10802c03a94910340d0700001c0c01814001030049221035020800410011019000b40b1480d1620007282e10750031401d00c50b140d41840026520907405100b0006c1c8502418280f52a82b540c0043c00400c4200ca484070b20b00101580c00281c04002c414000c6c0014a8003040d58005000205800c000c083c0c0310140081000c81010f59075822060f0207402907000303e28440e0054401c010a48100320b01400303542c404201039010505190000b100710040d04101c454680c005030a040e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 183398381 1250 183397131 183397133
    0x50a0b0a14010201091e1109011526040b150d020307170109020a09060e0a050f040f03120c0e0111011a0d081204050303010611010b0f15040806010b030601020721 71
    0x1907204100c20250303045540f2850928040750051107400005000781d211a1203100d11703850310b010390710782e03d42540e80a0288040100010a090907420070105143c0c00e1040340c2c070390b54005905030420f84581c44100507140c20300740070906c40803024141c403640d41403031810490141b003020003211821182c4025415400050148254400a01c1040b81c458482c0000f0502000c190300180504075903401050f04c059490508000c815040c0e456540c2140c13242a0402a5003000d48075110007110045c0003030004600110716004240c40b509241030020601c0c02d0422640f500450010b2118081101507400208640d09644401c4818800c6d204451038000703640d44804130201c00e00c80700030503008082d500d11006220752021200340160061145100700d0185540f0740c1031500103042c100615042e809540e1600950745503544039240e0324003007844111342d0380c00c0c5c610142411840c140304603041103445d8040c040000403003092000c065406010260240e640c15500e54510b50f030384100004c0c0c415a00c030300d030202c110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 183399631 1250 183398381 183398399
    0x506040b030c1905031b030d09030c0311010504150801231f0507050a03120f0203010e0a0905010209030a0f0b0f1006050702011713031d10030e010609060810050a0b0a 73
    0xd041d5189010180d05a03644d0740000c1d08112849030507074945001c07441d0400d01d43c5800d0080c03e810361241d051128981c2e045031120406204ca5000041c40c0c040030074186046680039105482c018011005c0f1014403009408000b44219020710805801601c50b40d40c3c03006030307641d0780b100c8105c00c440900030004509211107003031143d20301c11021109200080080e000410340030701a0051050003a280c3c010308120424241003220290036000d00c01501c140014030514190036030454200300b16101c040b400008506102c0d00a10410ba17155900d032003103444074010001c1100145410314098000d80520340e035100325101d40800210b40c003150006103a90b00b030050a0080f0040d114050040c5031402120184010f920315030031050320315902e80d00020206400300f46c1e10501d0444018890480941903100c0000811090b00c3c01e4411081415168480b2400c0b01c40d095001c00014607070b034441030107203559415030107072103c51505140c001242424001407102c01a40100d08041c64050700e400b4400d1f141c01b0201d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 183400881 1250 183399631 183399649
    0x30e07063603080a020304030b01060806060d022113020f0603070206040201270603020d0e0f060a0b06070204020f041e14010c0f0b0c0c160506070609051e0d030506040b030c 76
    0x71251001e12000c040082030507540075103102d83c91500210765076419424540c00b1600f05a01c0101080019000c2290ba03440d02000c1d10000c442c0c030310000d030b20b030030800c0013001010705081030301c00d484c074000420041440c1040b1200c0680500070380304903d00d04581424800148012150b40340984d000501040055210700c00c0301c0001281c00f0300c0c001081480400301e1400c1c188990280c40080c0c0c000c81d4140d01c0b40c8651098a00444400b002403070303480324102031581c480d81c006081801c040d03924114810151614000c036010f041d4001d10455803840070817404141da8100e40908180319510134010f0040c2405d0805560036a880c05071000880d04900004403044240c461081300c3c061070004400002039180703030301e80703004c1c02c480e2180d01e0710342c0903000305940342801202d11414010b45080041005456440c2281e4906800000224010360310382011881c141c0c0c40c0503034000d5035803207903070a8403600000300310b03d000c10803940c2e014026911600108001d032160360705800d0f030680015103206800d141c07854003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 183402131 1250 183400881 183400967
    0x110a020a0e090312040f02121906020318010603201507060c17040c030215210703090c0305030901080a05012103022107060f050c0304110a05040c030e0706 68
    0xc403842d209481c40c0c610844c3e60180c80440344168080441c4045250039800c10705180142c00080c0401100b8000d008107003541c4141c042d0034a40e000022030340e8460001c0e40a009111041e00038000d032540ca14240781ca100138030b01450184c52907404030700c40d60319051040c041451444640581801803a8603000c0040618401900920881207041c03454040044889449280550801c2d07000380c0c554010700c90708503098280700e5203a00007000202d003e0310008041040302204022500035030f5071010030680007046040005440007000034000010400c0020080c441d4120a0ba5928159215024801c1c181c0304c0a0040081c101401c0058061014410403428100341c002d204071170707031200c61031184070074285401040340942900103000000c0c481c00c1d00a030002c601d0324110030400c0d0320700a0a00c101da800301806c010041d22400340031500641e43c01541501420008204221011506030050700402181031210403500038010000340480c0940c0d6002051030340703c0c0700c40342c01c10b200141281701c23000003900c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 183403381 1250 183402131 183402133
    0x9011503060c03151502010c02061e0402030c0910090605030705100c021f03060501080f0702060f0a0905010606030b040e0a11300a14010c0509151b010c110a020a0e09 73
    0x400d01c00a60751384402200400b80180250021000b02c1070090030b5501c01501d160641d4808014046085421000c2c0d405070343c800010b82c60103894602c002410030106540c410380c400e41110501130317445010b0b5503130011222038010421103543c1d640c06164543d0071922038960300c00e50b10905030904e64000d00308007400b1803006150443e102102c08500b8049201c00c913003000002c0e5110000c1c0030950b04003011a402960022800140d442c0c2400000d42d101d50040c00c94240c6545036000c504450700603080890000e43c080000c1c04240d499980c001d00034001c1e001003622075820002c6003034111102048008003607421070200452680c040701030104001c0c4070f065811130032144260385503061445450043c03d8011002c0548210b0324907080001d1514800015014140d00d020b41604465401204840d4581025244001c6034a102c946030300041c0503d2400f07180003040180d0807d19036030706610001c1881410380398500491801070030700759030b0b140b1a0002504440030010900454100d810416804110b0750 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 183404631 1250 183403381 183403391
    0x3070317070507090618090c0501050a050c24060607030e06090109050301021c0e0d0906031d24100503100b04110f03040b060d051009020102010e16080609011503060c03 74
    0x90b403018a0004a5440002c41e02c1c0c3c1c408051004612801d00c0c080501d040000c28000d401c40b036100c80e004c103d120f224890500c5000103240045a000e01c1c03d079800f4404282c16161212000300d4803e521121190155408440131000280285005426589480d07016a14114103122440078030905600c424001c034140200e03000001002c0e07800740014081030180c48050b1185e0792900141c2001d0342c8003a907a20700940c01000309020519030007560780c811a5010300d4042420041503400348031504010300182a14015992012080d40b40c86508030745100740c0d0049034010b691500914a00d0882030301541d64140c000d021150201443d075008600c24083c010000039602c02001d15400d401d40c404e442600740e01c200802000184400391a24a50140040e034110300704c0e205070f545040d02c43c41d500316a040e0050f03071840102c055900c00d600c409440004241220003020300003051114098003403280507d14800d42e000111544010f0160100a00c103848000070500e08581c0d64002601010201c1e4081550b41c3c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 183405881 1250 183404631 183404633
    0xa090c08010603050708011104050d15020702120c01080901020a0e01080a06080319091e29040915090c02060415020f0301031a09070b0f18040203040b061e0307031707 73
    0x2e10400006510a10007042c0543c0b030102c3c40c40c20344500301c130340c902c0d010700a100402c000c1e107484151094966010094005a04105903501d00038040c2e81c2e006500090b02c41004001c10900084085801c4026250102d40b03a8800c00f4150a0380b05400103000045c0c00d801c030408255000b00c4c86260820050000071031155110f02c0c80b1461500012101c1d10100c00b0302c440c00c801c0940104041024140c2c4003514940c9403200385607000f003a0030314841d1080c3e148680b0b103010f914100c00b1030f183c15079505184107641e446036103544402c046c00c2d03d815003002c83c20032920000b40d102214456180d1896032034015061a0b5070310785403200048100c02441e500103408203c0d000800c404d1000440c041c51080440084036580941800d490300801010361031241d201c6030b0b0502c450b1080c00e041d110345120400580f90307608502401c002c400d400814507640c000d1b00100c144130821007003564440c40350038103541c4c040c944407401540b0107540c0c0c0000d03c165015008010300707201043c402d8a1070803004191000c401e1400c840713 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 183407131 1250 183405881 183405883
    0x1009050a06020a09050109090c1b240c09050402070c0504020318010606170c090307031b0509010e04060b0303180108070309050604050a060b03010902010504050915060708090901050d05060a090c08 86
    0x411000f40000807290b01d414450380da017040b00321018020000080041a00c1c000d000703001d1502101b1400d0a07800c04080d10410032107601c3c00744d1103083c40403004407446a080d01c14040501429141342002c9100d000010416007810f1098800103500301c3c2c01042403074a4042400001e500150460400143c40f080d85a0101c0c1c090007280c004182d6540d072200182803c444422080c5400351001405440410110202c1d540014a034000c0d250800e008401041601880c04418209030303000e00c0d0404540c500000701400c010300c425124901070311090002031217103030406803207100b08191002d001107160742680303840d4440c0b0074850340020107003000100d0110035103030b01d4900f50741140c04640350740c0b000550310200b02c6c0f40d029510440324150001d010092403a4000b03400c1d801580580d078007880300c9800140e15601c0c1c58140e107a83c4600503010700d03a1200141440c00940e4411301445004903a4000000307140d0a2603000c04001d140c206000e0021078a5a00ca103801400b0820429150301e121110085500c0d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 183408381 1250 183407131 183407137
    0xc0305010920032d180c0111061603200903010b0303120a0905070e1503070501080115080c25060b0a050a150903060e01060e060d020d140a060207321009050a0602 71
    0x1a203c42c41e1040c007040120141c40c2898443c6c2a81c1002081c003404d0100c4a00002c0090b00300100c000c90203c40000484100c00a0645410075464117100811320303c00e00d4070301c0008002611054009001d94400315045c143c0c1c9210b00214018000d80000004801207801e44c4040040ca10500603508010350342d190340c58070940161011010814041d2620071945010804070004010a00b410112507141010100c0840344503601c034814031551030002080d91000c101115401d0740340004e450440480c03d2103280840f40c0814044030450300d0710070103a42038500952403908030f540c01411581c0480c180170b1400b11035040d040c0c1413024401c00c00c02c003000042250151404020386a000020007034a0041c1d5942004c00180c00c140c0a4401e0540d4a00907848000f211110341e500405464043c0322488480c40c0f512030104806454a40301052000c20000300101703201000c162045440c24400071840360008a8480d440001440d92012251420041080c0c2054040c6801031042e20200080e070f80b03403201039034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 183409631 1250 183408381 183408391
    0x109060207061d01060f0504110c1501030b070203040b0304080c0102120f06030c0a030f1b0b040308071a130b0912030108030306090f13060506130c0305010920032d 72
    0x580b240750440c146403010760440d80225040c00217002203458940c0c00c0d030040d1201e00826019684600343c02045402000c02c80f040050a0401ca0304815508038948281c03980c00e01085818656080103e54400d10020944060b01ca01080007071560311140c2d520740842e803004d1032440995400b40140510701c0f0010710591b10030041030607500b20300e1601c03404050034015400d108a04c1142c45440500100d5a05400c0340301650b407081c2608040308100321070051500300e41d482814040e00000c3c01008201d4408080c00e032062041c00e0500e04030105061004208004990260300c0300705082490001ca256400d05941080100041c0c0311481200500d42c860741d442600941d1140c0d0001043c0195820042d0f01643d111088005484140c100314103048480d2800400281c02c007925030021540079035a9038071844441c14009420040100846d03800b50192000340706a455140c03800f8007025070441540381d16680c27422b495140e503146943d440a401003000c00b208003a52812140018207049940035030328070303021b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 183410881 1250 183409631 183409643
    0x906192408010b0102010e07030816080304050f0615030d030504140f0a02090a0207021c0503120f1b040f03080f0409150e010b1204060209030109080a0903030806030604030905010f020109060207 85
    0x8030341004031603400e5038010140141103a00d4041c98400c06034022880c4015658130080665680320b00810513845280100c070040c0c1442d0000050000304040000c0305c0056141410075281c0954401d010303584241c40c09045540c142d0401d0503a140e00500c00e40c00180e00a2050a082041c1824000d05519051806032900c0c030b03a0740300c0d1112a003545480c0c2401a03000508034420741c940411617010814411100b00c800c009007110321308990030403105105030f419001c201e010440483c44c04481c811941401902e101100340c00181c01c207030003001e500c401c03502500d0100642c10000c500e9583c0f866181d03400740c5410311800c18140b1001c115a20b01c0e0048152031000118640b03201800c0c440c15010b81f0300f040e80904c0071100c0400c62040c520b0003501c1481e501603005040181c6903014800800d0142c005040c008091003400108c14101c140c118002400303490199880f83c1081d955801070554503001038a02802264442004000c0c641c4104004100d6003810b100104109546a07514010f0f44c00500d011540 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 183412131 1250 183410881 183410951
    0xc060614011707020304030f0311010c050d0b0406140609010c1a04051b010210020a0309140607120e06041b0b1309240614040305060117010b0603090619 67
    0x1941e4400c0c2c0e110048607460306645801e0074803d8002c1c0d0b9a119511004180980840350a000e142c0030b044581c0001002c50000e0040c200c49000041c0309a00690035002660304c5d0850072001070800b8032900042d51540c1c02980c2d001c1900801308103954101100f804d0411046400720400140041424086503018054600e005d0515240903414400ca0950201c4444a1200c00500b0b60f030f030001ba401c3c82004215070040c1c0e2038081c000110040d00c4005400741c082814591240ca10910010f405071081c602c1e03580d004082c00e00b000280b000e032450b001c00c520340c41c1c1c03140005c0380114400c070107202e0ba410041c40d4001d1034180d07180000b02c400d4002c9140d180c07003892002c0040000f0069801803000d40c0c003190101d0a022112078825551120b0103020708020001d440007408030105802d41118042d41d008012a0004d696600c4020342000045243c810f443d400c08060300d04034207200341642e01030303c0b03000040e00c107550302d0516aa082d81c581403460b44a090b2140352740a004414203842060018841030287c0b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 183413381 1250 183412131 183412169
    0x307030306120b010501051305120c101d0f030c150c01140108030a080a06170307060b0f03120d020706050703090b09070f0611030d020c240609070507030c0606 70
    0x403120254450310740e02d200c14100c000000c009211480c1550002d00340130b42c458400004680050702590041c940181c040501142503840003d90314030300c0a02207560321900c00701c100302103030f8600d90034040304050758486000301043c0c904000e40d40c2c0101030107012503d620240d500094070f4412000464100440300150460b4000d01c2030140708452202c0c0d40f210f5030107514040d0516641d200700602181045404004210501c0d400c6d001b03c00244070450740b800008030803507034540c0c80703a0000031304540030303458030683d03481d0b608120901003510000200134050709000440d0428041c2d11006800c240345e40c0c20004500001c610b4481d10b8000c1a05030350002e8000118502404480b0780a020000180d02034841040381c445064120b10a0314080e18041c610018a0b0320300c549107014003402c1c081024000316500ba04100300180f0700e0184a1074000f100c90304000365502541d50401507034001c0c1c0202d00701000820a0740184010801e1610030b24081c41c0c0703501151200d401700c4110787c10010104095514100e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 183414631 1250 183413381 183413387
    0x23103050f1902040c030b1201060801151505030a1416020c0316090c090e010608060a1a0301060c15110a030b040209100e03100c050406030c020a0b04031101020f0705030703 76
    0x501e40941c1078000348000380350302044082041e02da180091090f0f4907070358503400c03440c802d03000580c004a011781404103104580341818042e243e58020b4281a40c82c0c01c0481c1c0b8552200b60004040700c855254050030b1040ba400115955840241000700c055203030300c0c0415a02010341150b9100d110302800c004045409500d0086c00c20001100c418800d0380455120720121582e1500c0004943e0311020006041502810654a81c42e080c0d100d8200341a490b000010803980120000340304000482d40407401c69181c40e10000c00041c1521200811107080c40140883e0340a070003240000d90080c03081d4041030701e4440004068541c3c0c1c010110300c6440200d403020207a9014007600040082c00c503015802c1220250101e00796040850741802000104886d02e01580c60a01c03025005aa81da00c0501c08000700300340181031980a84100c50021f0300d8440c0c3c543c0003501c0402c15418240d170181400c44e203602c0e95101110201224034001c1802d5508105801c03880c00d01d40c0051a04611640245444400d281405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 183415881 1250 183414631 183414643
    0xc090901050603040308060f010c140609070b0a05042603071203060b0403050a060906021c060501091502030a140c0d1d150d090302070515070204051b090402310305 72
    0x2075001d15410f1050000080e000688a944540309a0b443c100c138018403001250b843d1500340300501110003540340001221004a9103070310420000c400c0307440003a51140e00d210300784201d1452400081040c002407089070040c0300c0e110460922411400800f05480032290b048d80c0c0141e0f0101d40411103040001500ca401d8004c1c80028031201440300d00306482c540b0b50a0322000110001001280d44002800401140e036055400240c40210301749541030492500c00001e040b640a01c602160410400160780b1941040c20650406181e000e035042c83c11703619080d6481c0529165101b00030b40700340012204078000f00008003110250307640b02c03032644103084c4000d031480b58040c4e5070368001c00211f0f0104800c80700020803581610004000080e0312900d03401c0407410300f1100e41009501c42010103100802d440108054072140e4001c4070100481d071614103800c3c041134241003080c4d02e201e509002c5008245810f40c0604040c0401001d00c81e0038080f511568010411804281e03542d86280010910922504000f9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 183417131 1250 183415881 183415889
    0x4020d030c110a06081522090f0819030b03011505010f0e060c01060e06040905120a051306080601021603050c0d08040b0a02010501031b2319081c14030406091a0c090901 74
    0x50f8105084901180c002c903450304104a0110310380b036582403010031054100d0820002d4020b0704407a294501001141e4100100c551f2f000000790901c003055001d03203818486c0d2421440311001c481e154500c1e100056550100c41200c0c05e041c440c48141344166621514010f042501d128000019082c0c20a5480810064040d00840c0501e02d800d42010000750001000200c1404001140343c46003c00001120700303214101e40d0140c1900808800a4880e0b002181c4e0360007801c090b001e544011910000040f03110f030355440054413980c400c080c0700001d07003001202010380c140900040c0d03191540782c81e2504403503070104a0000040c4c1d9900010030a01c13103041c040412030142c0140d10020705107003140381c208445000c02c1c400a9030750b6107100c2d410907642c0c03401505807031141c101e204492140c0d1103c00b141c070303100c110071002181e402401484035044d12a1741000705000341c2c00003240c25a103d80d10f031480100548041203030305240e03140e07440c4800040b800707040348216094012195a2988001803020120040e0300c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 183418381 1250 183417131 183417139
    0x115090c050702060a032406030c1b470108070611060c0904020705010c020106030b090304080307060f0b09040c03030f0f020307200628020604020d030c110a060815 72
    0x2c07520005aa8400441d1000c107042c2c036002c503496000d41640700714201c641080c22811965034000089050b0141c2007001c40203969203408140214039020743e02c90b070300c110200400603190303081041000010224070201d4044020005108500b018003280201507044027021000300202c401000010030801c10107000c0d00661500c45503820f00020129507481000c0c101494032140442d13840c074070f61035170390560305c0c1c00780c01c44024010f580030071398081e000700120b0005840300410000040d554450010454049800c0395006501d402ca054a03443d00801e000c0744600b040d95125041c8089944d501c400150065010b02c8101d46020716526001c1c18191400351554144101501c03000405074010003500c01440d000041d10400444820250340040c8070006059440345000c1094400c0004903081803840309001d0701205829010714805a030303500411500254494200301030500040e200381c0c0e45031030042c851120200c81c0001c03100002c10384041504154000f4010f48104551008441034410201c1c0080c0c2e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 183419631 1250 183418381 183418387
    0x408060a09020d1101020c0d0b060f0604050a05090a060504021b060708040f030f090b0409020702132d0e060c0705010c1103030601140409050403020f063103020a050115090c05 77
    0x7602044601c900240c3c09481c44880c450a5451a4028418403000490082070024005170510340440001c005480c100c1c01180c201511042501b8072000b29010703514000c000d011001d262034204030746154014a40c0044c9074441d0030000d200d4440d40050010f468110a8500d480c0019401061500d40010300f480308020110060001040c85001c0740e12480b0f800d0301d0450050ad11411041c3d400300300503031142c80c540c0f00000d00021200340c0782d40a000d641d882111109245801000050180c84200d00041d0000e5903140f071241200c0b014400c1c0c4592001030510100c3ca1003a5030708060309180007240c0c219024200050000c00300034017841410000041307828544407908200f1910340da00e0200402e070340d040c4048481580c3c001c103140d40984000f0912154144081d1a1034039000751503007001c4407119032a204900200c0d10010040000071710b2500d40c1001e200100301d0100c1003030345095904805900390b000f00388180d40801d200380246003242c8200c0d0380d001c282c0d0703282c031400c0310844c5c925178020b40401200b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 183420881 1250 183419631 183419633
    0x3030306060f090f0e07031401170c0a08330109091505100e060f0301110a08010807060507120c06090c05030f0c06070f0c0b0a0c05060105060f0a03240305030408060a09 74
    0x208040c1d1041c0d031511171003d500c954a84501b540188403401d28144407540c054000a4550060003280401000780d80943d09021000720612050001c06e00400c200303500b1411a104121031b01002480d20450304844c0740c4925054a800040d0900080c1c102d050615111510003051091500060350100c8091500b040305240054070045000228080c0c03040c0c0228607800300b085541d9803208071115010082c000c00c42c04000e0410155035a0011240c00c0205034804000038149902281c0c0c0011250141c80340c0303140000941d1072070a00908804803005128140c048000070401c04e2042c41407440c4074040d800041d5040204140c9021a0310000d0110b40d03120071000300c2561504011b40f034000d580851a0907402c0010b20302110800b546030001d280000010800b42d99140c0e110402030010b5009200342c43c46a600c440501c0150300c1000c182d4000c291040101c801d0ba1486607102010403040002d040030340900f2521a51280000e031f52040e65554400704d400d0103040c1082c0801600300300404810400171b07980d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 183422131 1250 183420881 183420899
    0x405090402040903052718240310111b0102040605041a07051203040c0909020607080a0e0a0b0c06060a210501111b1c021e01110403030306060f09 64
    0x40c0300034002ca0700c0d4010a010180120192444146004030b1104092802584003d8040c440070381c0e64442e580e40481d2001031010180304c039000b010350b11500c000b0301c501c07403000d006030100c249481a09440f489803107045141c40340c481c0307001e40240c51110070f64503000000c0b00260307001581c9500c400d6900c100002c00486030000119001c448125500c1c070500907414007045401c3c01001c6010701203010b0001490303500c0c01c440307006501c200d00c14000007210603158602001115420340c0000c0d0010f108105800100750707201d001e080a80c10a1400c11218103600000c01c5550503594403d1100940c007090f60b09450906100b06540642c042d100b4031801031420002e004c206c2041090880001c810000c503505000c005c1d04002c070040c841103111541c660f03813202c900c0c1c3d00c0c41e02200d223208240aa00c444981102d80541c64142950301540180290010158445c400f200620709040c0550360344d04c0001d080c4100c4001601c0118047e44001075031030f14021001d841c030391440c841e61040042e400018803400c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 183423381 1250 183422131 183422149
    0x314060f03010603050318090108060103031704050307020411030603100b0607060b0109080303010f170a03020d050904230403030507180902130b13030501060501021b0405090307020907080702010c050405 89
    0x40448420358008000804030b8010085900060800d010000b04032064903000144120300081c150350790869681d8844040e5110b120038000200043c051408100d85407140304032240d00a400b800549241003810b9002500312982c6050003455103401104000f103501d07040c0f2680d4800401c950003840745400d5040011018429110001e20050b80d038200400b0503481540b600000d40b80e5101120303034a584961044468030550300c2144001054880c0c40c2c084101c011030012011981a001015000d400d03250940349600700c1c869641c2c01c50754482c8400c1004000c4019804c1d040d80ba0000141642030904004040c0c4034010050002d00250030b0122081600d00400002103e864009c01038843d81c00c141c99507180f00c2ca40d405440f5412020a020444014070303001d80742240e11490081003426513032001680c5403000c801400c2c0c01030420341091110b0b0b04060700401c0e400240842901e103486c00c264005111645c00303688990000e49080204101d130341d024030a103c1c031140035080071401d0624100010b4800b403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 183424631 1250 183423381 183423391
    0x100902031b011e020a0b010e04120509010c0b0408190309061505010219080f270405060a05091003050a05060103030201110708040303210e030a08060904080405060c03090d0b0f06010314 81
    0x3d000d540b4180d00e968821300503d142c007035020034080d0141d40d40e03194981261105490680e1080280c0b07000102d024007560441d0360462068488940c10107040c0c03250040c142c001003042c5c95014080080450640c030000303031088144802d45000441c0071890a10404980200044107030410000c00107021580c1c00041c0352410007070208800e00a601985040040c1d0b000740841500070240105048040c0c0f403884400d030403041c403400b00800d0016004810001a1401580c1d8541c002e03004070424029400c00c2c084490703005a40c003420140c1035580390380d2a450804036590030340b0a0b0b0030840051080550a008000c0d1506122180904044681d2507194981c817440c80014244800c0c80f080100800000d180d00f520b01120700f000f00121b40384541000c1e260f42c005050f02c4005400240007401600d0800702250045030410301160a10303040c00c1c140150f80c0c0c003a1000414602c006d0000e910296100100000014401e002600c070604024032010700208002d0402c60601d070421a90109060200c40381d15805 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 183425881 1250 183424631 183424667
    0x20a03090e01270b0d0c050102011b120c050906030408041e0803030a090609050709051008060915060d0602180f010309050a17091306080601050324060f03100902031b01 74
    0xd07002100343c040240301d070542d503d4004840072150403c0c41510b0310090201d680c00e8009003c00001309038807205c4442c61408000c04141005503140345102e0716800502d0004041c1456440c01e0f180400082c0c141d0800c40303089a004e9030015040c401e00c940c628805c000302d030440c2610941d907402d00c81034640300e0100918421619548000f01e100f484101c0c1c000c503c1564004090711030058807020780101801080b15910745146402d24001b6001c800040c81034803643e5140c000d08442040c030361190703007658405441d0030b074030030200d061304004070716544000d00425a14002842d140c0c1509070500040c1200e2000b10b5051620301600d07035000c82e000fc500311049550101d08010b03040000380c04a031035801650042a0460902150061441469400001a6000c0c41c048900382c0e030b83d81042603907d111100c0c0c50420548503d100408210001e036a2340c0e0408402082d2113103640245020030324040b51031020800c22038a844002c0154102031104856080340c5200001b00007030080006824000d44034204102 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 183427131 1250 183425881 183425939
    0x605090d0b040b04031d01080a020a02070f1e0905040305031303031b0806030613020a090209060d1a010801060302041401110a0507120c120b0c0310080706020a03090e01 74
    0x580c0d90121003940a40d0310690012040c20582051044858201c1e0120046401e5406400c036620040100c500c8141d0140d5500c0d5a40c0d40b030f8942d81029401c440200d006602c20a500414030642d44040341780507000c0300340f00300d900b0310f040308580e141102c1640c85004010310f8401404082a1b20000b00ea900042c1220000b0a84006107400c400a10304100c04001c01c000d040d400d00040f80d44011007030b0090004404480700b40e00d075101d803c50280241c02d0001d6000f142e8160801c070061654028206003000104403906140311100b560081e0381620190301604039100016141c3da40e0418000d0b0701400c1d05240850a060815410000c00c40700c1c841d1044c14001d050082c015485820030203801e03110f51040646001e02d69480b82d138200d940031010f08580c507919460010a14884000000041c6900200d07910441e480720002c42c040ea610160a0445001146d074000c204000704200c0f07480107104a07401804c110019040040001415403c4205448003140c010040200250317082100c01c0050452082 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 183428381 1250 183427131 183427147
    0x21303050f01050a050115051602060406030e07150c0308041109040b0405011b0905120c04020d02040518040c060c082107030e01180b0711070803031504050f040305030702030c120403021206040308010605 89
    0xc411480c0c2c00081d84200003340200c0d91300e526801003240c0c01d80201c21540c4258984204800050a01d100040098624072420340840e118481c010740160103019060100c2140d0700115250000403501070f101080c010b028402003041c24414150a04100c28840e00440ea880800415008240c4039403131160108060076200f0840900802d07119440080c0210f55603915809648041e4125208051240c06442160b14083d035000c081e17144950307404601380c981207051a605480810380403e056840715400d01c5201100410040c64000c00603c541c54a4094a0a144010103881c44007c4541059040c1000c410005001c40300c103446840c0d200800000690301d004049030001c0d400e1900c1071292041100020b6125000710040d40a52060400c108000b8038200901040d500c0944e0500202480310002a0129116401440d080012881500e02d40030920030443c1c40c20340c0410382408501c1e40001d0800461034071aa4103019248540003030f1101d85090384010308000e8052288809000c0e00203070680d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 183429631 1250 183428381 183428407
    0xf030f07090c031404050c04110f030c0d0b030a0b0103170c12030a11040906030c12020603070e0402090402121503070f060e031509031e0903120c01021303050f01050a05011505 77
    0x11403010000c040000d4a05d0a0706145548031914203415001d185000360604070111000201e84010382480d140b1442c2da00c9512000c1d03003580c000c15a6002217995610a01d5043c2d800f8808905900d000e044002680e504505000c40082000c002c0b04415540030001d44d8846600407a070b4050041c014202c050301e0f645d821801202900c0e0b910701c9094002070001d00800d00100d244d0084050343d02640710f50503440d8640c50820942c80e05024065406481400000c14640c440e0742d02c0c881248010380f0240c1020402c50110f1b0507a002854021450f0000008000e104401807a05410b920011401045e140b45270205081d15101c40780143d00c1001080c1840380d40315141001400b00780140e05501540c00e20301500440c0d140c0c0c021204400c5000040182d122107002404261408100300901401094a10340100c2615030310155146001d55002d1000d01401c00807000848000d40c02a8054104110b8200b00c0d60300b105c00081864030300c2487d2900510010700d43c0c0c25900c3c1010800c1c1001035942d4542c0c5442 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 183430881 1250 183429631 183429641
    0x20301060b0307120218031c1202071a1e0a0c080c0a17130503120711010e030301051309050703050f060a02130e0403020109320703050a021c1509020f030f07090c03 72
    0x1600b502c2401c8c81091040c81c50400c0f094040c05a9840154003003081003c01d06074801d103000500301001380c040c41c0104400134407005070001c00580c00051622285009440c81d03103801c48100200c60fa4a45000c500303907401000d59580003c000601d1458030850101c06094401a0626000c50903562800100c04000040080c080107402600b26078540d040009141c00a803421a80700d000169100c40780550824140140c16040030b211024504580c00d01040c01240c4122049400c1080c2d00c0e4801c1c9804100e061152402071070045002e440604122000a440c015020f407035a580c0910400c41c4607842c08403a0314a005452110170f030900241c4560500700c1c05000e03012720141043c0c07030348000c1c003500c411842100d40d9a840c120038076038407202054605584440f500e1101900681001640c0350040c60403100c0a00c09941006201d80243c4e95a151900c188107908039171100d2a42d2500c4103020f51a00b50190144480228001c040c14050701800c2a00d070491445103040054881c004551803034000d400c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 183432131 1250 183430881 183430927
    0x516060213030f050c040e0f1005100315050105180f0601080601050705030a080105030f0109030516210e010e09040201021e0c0d08130801060b03010303110a120804020301060b03071202 81
    0x1900007002c900b800e07900c1e0700e586099541b00318a00008814000c40205083e900b022441c0007400d482c2c164080d4420280900600002190384d942c1008400101d100c071020010480c01c07000081c0c10340c10f18060061012080d81340008400f00c500c10455910001013206511100a103840010341d2590b400580381401160002802d80c00040b4030b00100c40c2d405030700030b412a0b90480848010315010b000003801c07103000420150008404000c0f4030f484a0b444c0031034181d40d40c4034040c50001103580c2e07403414034210031040c05500098902411800705d503a100e039155403100d0046a85100314241035001030f550300c0c4000d0b500c9249520890641403d17030014050b103c101c4002525900d203410341494039003060345c0622981f140715111b4807400701d0039210521468003031300d2107041a0703840c507401d54805580042e001c10014445100d0000701c0000540c80c42c01c844009959034460000030b092520425003500c10b0780c0c1003c01050030074010828083d52000717916002e0a501800140d50b00183c0e1103005c440d20316800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 183433381 1250 183432131 183432143
    0x1912021204081c0e0a140a0b0316020c0102070e0721110405031207051213080712060b04090825120f0f030605010e1002010f0c0f090501051606021303 66
    0x34009140e1202080b100c0003075268800310f0710030f16141802510420710710b49005401170445035043c00100c05600011940b10b40041040b0b202c6640c82002120300d80c421200019010482d0f80081121901040900b10031102400600042400c14840640a07100204240c04110741140070110050780320a039440c01990b18402802390000c0f140c80320030258400d1240c140603100f4910b4401a803561b02003036464507035102000d0881181490b0800b40180c01c1a545e03031001100718100000c070040108080002442001300b036140240c2c0505002c002c688008100c41c0c09981001420400a17000c035003250f0300c2040f45106084640d5234030030710342c841c1411108020820b1000028007411550022414640d600d1a41d07151112008106001c80c161107103031107143d0219240c81e90500c80c91070058401e02040581c0c3c400000c4100c1008940350944510501100100c1c400c00d0308c02221a901c0344010001d81300a0030b2840c0703401d0340469070302144008054003030105940070a0001d684103e00103e0310080d5003100c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 183434631 1250 183433381 183433387
    0x60c07170a0e0307080f161202010305182b02010905101104030209041104200702153001060306050d060207020d080403060209090a050601080a090203162619120212 72
    0x4aa01d540350406c000322a02da100704c60302c02c0c4518078050362160607290440e148842031900340c0c1c0150302400000c1e0050340c14442c403081100d0074860030050001101c00c1141d111018880a80c00300c215030148c0c240d10821a410540c0e800041180044d000f5401c59109000050448060404503d0350180d07400c000c1d07012003140d045c4000c0c0700250680b284002405c035402c0089903803010704c940707078004007461120030031b2010b02010000d0714ac00031074804a0003050000e2341c070307001701000c00d02e1900c40d420514405080505d50040741d1203a40c0c039001d03405490103007002c120050800c8c00184411400000007000d40e900010700d5021501e4440c0c002e0754680c0e01030001034036203071240343c1200079420850341940603140317440004070490814002c0ca0b00500061711240300d552074410000d40075124500c0142c1e05842000300700800c03443e1000031403000f061800f5010800c0d070003e13070004004208181403003055138440f0001040703c02c18102c0c54007202e03520940c100d021200d40481a4104201d00c011840c143c0004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 183435881 1250 183434631 183434639
    0x4020109050618040605040e060a020a0903080f0a080612120d060b1902010b030309090f040606050a06030c030516020d261302010e03070e06040f1b05070302060c07170a0e0307 77
    0x243d05182240c29045406002c100c0c0c842080c0401c0350441d2a01d40c1103944401c0220f40c403101d503036004000050351450300d5040c05440b070325244225801003d47e00403042000905040c4140e000da0070b90340100040310b0907a1000c41186c1f4260343c1c0e11142c203249541050024014080c00c02c02c0e44480004c0c04800c8090342c032000d40c04403000381a4003404803079002d542844101215440c0100445414410040940c0383c1c0351030340400c0c209a00c6005008507401540e4007004560360740c07440501c038010041135401181c1d200303070011300400741c03400502003e82c1812040018403200d600495600442ca003985800802c001c082d000c0c1e2091000d041c454256400d0185051001c103e04004011010a0003030302d5100701108140c0a056540700140304601e1400c011001041c118540b940001840c403164060104800c2d8218200c1c000401204541102040000139100c0c01c1540500501d41e02c440d6940d0324500700b90180e16a2410b800c00301c046070107040d500059502019014002101d9944405801c61380700c0b0b038075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 183437131 1250 183435881 183435907
    0x11030d0c020c01170403020316150e30030f0613060303081e070e21010203011712121306110c07030c0503070501020a0f0503040515030a110c030a08040201090506 71
    0x10b01c0140c50010b442070401ca6054503c52200a00480e0700d58001c616010380340500d4204070000a108407001d00d4a12070030f402c00107130303130203035a890680e03101c0500480403041091b6241c0026694068440355186d4000c45200b100340d1041d66405200c2c4e2249840c6990b03408001400c482420462058031071905070b0100c00d055021041038483c92850a0010380000c0c407843d41860101c044440f800000c0b4085101d9444e424100103008040c101c55841940107500801200c0c00d9070000d030422009a170502c103401e81d098808000c0301512080c104001d901e000421884180c15100c001c0036030b200d031103104150104000c0f80340d20540d0852045d18002c0d49525885c50403613103c1e0100d1005031000141058003181514002c01d0040c1220016001400d4400745603a4200c00458107507000c2d1003034081800006a0b6460f204a40c0e282e8a1403004800d98a14000224004440001c00e00050740001881854414400001110001c894505040043e03560354401200c05000715000150001c074041641c8443c100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 183438381 1250 183437131 183437143
    0x6040501020306042a0c021906050304021f0504030303110d0603060b0907090f0603090515090f0709090b0a050603010e030c0d320a020c0604030b01051c08040611030d0c02 75
    0x110480d1305000311020b4414407038100d940300440300041c440c000d80300840ca038019a100c0c00000d02c058881e0301480c12428000e6420a02c1751301850200c0c000004010451078416002c0d49c0310860000d80725610514044002c009000e01d0100600341981c030385014840c94001000d94010650103d4280050b0b42c891400354080c05c21021913500880e01c00b03000c104103034014103284060f1280c003860f610203180703040c0301280902501007081d00c06000ea14035501183c0c0c0010030f424401d0401900602a2003540741d2014a00701c501d5101e070032050f20f4840b00c0000900c4030702045030071180440000c6072946400000a0040030310400303c40c80d07440000f40c0360b209040d000c60500002900e03a01d030641840c0794031300701d05503510010310b510460141c03a503c9070441c4e403280380140590108610456820016003c08114254815001a500181035000412491030036000283e9070b82441c03003034100c04007a256202e150b540100c1c045c13003091080c2d1400e01003501004000766001110000c0b418403841841c114080d441d04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 183439631 1250 183438381 183438391
    0x307050d0e07050f0d060204120b061005130b091c1b14090403050705160602211303020103330509010806130b04020105090d0309080d0c15020a03020c060405010203 72
    0xc1c2801c036034201024001c100c1c101140c0703001d007400354004c0d90201048844208401c04507030740b40d400e020200706009140c06100d01c00d440b568000300541810820030000c6012a10000100013080154070912442d05404e0310483e150320320b8803502c0300014000501110684080200c0c80030342a0032030710900600000c01c40038502009014101d50742c4070703100082c00c040002c00441d00311004202060029108400505416000c0c10903500c050380890204044103d1650101c0c005031310141c084081803c0303c003501801c1450b0704498900e00712852000c0840e0407010310010f818155110385003000c0210325841e400c490b003000203ca240c00302c031504a000c120a8940503440c00340f80310b200007080c00d04c400a0a14003d195888142040d004143c1c0c500d80e111400600890400c9000e0100110503108d011540010324030944491003080d060604841c5880010103020307040140184214000c100319405030041180d40740c02c056611960217400343c0103403240c5002000107120398402c00050003010341c040c40c020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 183440881 1250 183439631 183439657
    0x5071b050a120b010302120102040b03010e10121a07020c0d0302011b02010605180c09041b0e060a0f080a0b0d05060106020714060a030203060d140a0b1b09010c030203040902030705 79
    0x540c2c444035405040d440058000780030048100050015250019003022a0012400003500d8151a14180c90460b01f003a4010a50480300c0018455143c400080380c03400f9001070300c0d6070760b050390450322a03050220081c0640b071103c0714500c002c1380465109002c01400c9140203010984507004030320b0000d000302604141c0c201c0e02d20b130700034114207400e1040c0103440481c0d10090004015804d002000c820f2844003070f10440f4154000c002100f45900c40e03020b08001c603450341544000940742c0000240040c2c0c0d06682d154425101005003086281d00074240e80c665a40900d8075044030342e56524228010001004005d0340002c111503800c0c200100052998140c8849609440755181e95a51342c01b164288624501e038010310501040748003074840d034042c42d4881d0004206d41000384598480444c0c18041000601e1103400c24403004040c0141c1d2140340380c000e9000040d00f41c0343e020300f0a0665041c01080d080b581003000e6940301e40103140c03080055401509210b6811981c1e03080080c00030b015940184003001d05c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 183442131 1250 183440881 183440899
    0x30a020f030301050f100309050105040b010815220c1a070c0f0303020a0204050603190602030a1d061f0308040608160201020705060a0f0e0613141b0607020105071b05 73
    0x8480001c402c2d01c0c1200c3c07002d030035250504800020414007081c5100350740109580c900c80d6a012039030900501313000d1401303803032800055410682c4884c1080b9080c0054080c100074030b001e2005d041030a060216000060081c814480101464070036a00581360f40456900540c0c26088841c40b00e00e1030041013514451404903580030b41d1552211210071051102402503042040030341d016041513003050340d10590080030b541010401c02240c2e080303603603801800c3d66801ea010041003032a00140c46440d101080c001b450b072481d50260505a90780d035000400100100070301c490301c9034104800030301e007601442d0b00c148076649071070311544001c2c14942d04980b10308643c1001d0700c2c102902030042c401c0700c42003500100030f03011643d2801545000342a00d489454071559941d0035044825605000a5000c0c0c041c480b440f820342061070426a90140740c002c6103d01c2c0b50489030710304050005c410b03841c0c10791000c10388030345803154a68001a5014001c1d4540607140305180d44041030301e4944802e00d04181c510803658049 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 183443381 1250 183442131 183442153
    0x15151d100e0403180510032004050a12050a020d0506091b130c110a03020a0c0501051207081e1501020618070902030402130626160b090f12030a02 64
    0x560481446046412040c05001c00d000c240b180c0014140c4081c0e2091180303c09075070b0300100385129000c200c4080002d030f40382c1480000c0c1005100303411441e106410382ca409c1504007800110510ba49200317810f125141030120004008003404585c202e540c0060241c0104101c40c200581c4598040b11a080607006542d4400c6210340041280710744104040c0041946040c0c00002e0b000600004000728240644003220810035032041140900882c8658042c0555007080e2829165840d401e40226041c8070b807d0040c4203034a040e83c54000d6002031146132050b46511119040383e0010b050388114104000070108011007541c000c00000c2e280202a421642d0035235032401400d40e00d9101e40800c270080d400040007000101d00c036401031900240018601c80003461035040d4001101e24a5000b481c85000c0e541002c1800e03c050301d10004c2c0780c5210800b60030340d0130b00048200012403507400f600208038004110045180c032080c440240c1d58002a0540d0200089405070550ba0303000417520500621440031514 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 183444631 1250 183443381 183443401
    0xc03041809050d0c14011b03050603010e0d1d060c0c0618040204030c06110a02011e09090204090510060f09090504111815010302070b060603040f051501050f09060d15151d 75
    0x70b80a0031007c041d0f5000405440c200710003801029000a900d9034a07500c0c82024220140042c524992082e281c94102615054070403607520507071441c2501c01c50042c06040074501021070000c107104812600540d9070507441c010222246180416030f038101e4400300740481040b0070380398200107486454403045400880c0010a03a43d070282e2001c0203001880c41d0301340f2003510f850940008010740442c1010800c10f910b4099001c200d030800c0d48100c00c6d00303803607100b84500014001c400d076001c2e0500d0301d01000803d0000c10040e0000b80c151040701c4a07550340fa8001814030120701c60700d043c5190024102480d1005a034008948030b002920080e40040b0082100b800e5036000744221652154802540503c0d81c1d2000100101c0b600000e1054aa00c000d22000c000040c00a120b4200700c00c5100c0326104e03188d41031400380712800ca0083d03103c42c0241541014880595104080c4808003584070407100b0faa02e2104021602415804584440c215072452020441040980464805c00030042c0206d0039540e503d0001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 183445881 1250 183444631 183444641
    0x203040c0b0c0c0904060603020f0a030c06080c0d09050109030806060909040602071e0c0608060919110d0e15090d05070305090604031403070203060c0c03041809050d0c1401 76
    0x4058003030400c410445520600090409034555409540103007814401040401004441c1290060794840c011307c11032030030b61846040c02401740c801c0c0e040181599200e4954480c14007820003030244403000140d82e031012000b20f82200c1c00707018003800005007a140c42406400004000c4001c250098000340841c14000180e4070040e600801085854690780c0341c00300207501c48441a12044443d01980004c401d0010807096818030070340500c59007500d0040001c2c062800504041c1c030484094041c0301912920142034080c0c115000e2000688090440b0844820f206240894462504100150119140119540c160350711031819550a983d5402001c986603a2402803100204005000302800700f80f081010f0002c101c40585520320740790f121340b10141d0313810288020004641c80040d0020071801c040c040140c11032592001c56003441c011038110358807806940928005000840140400d415180c4c0040324007607040416940b00440f0300031b00030020310b04035106a07240c500700f40c81c507000300c081442030f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 183447131 1250 183445881 183445883
    0xb1005010f02101503020607150b180103121205010807080601050f090f0c042402100902030c060a230406020f030444010c090602060606030103081c1815020304 70
    0x2400e483c0c503d003000d00c0001c3c80c02105018200740114808030068444c2c1d8000c3c038400d4014040d000c84030b2442c0c04160141c400c022419402469440c4000350620800003046040d25400348282c072010344065021502ca6407070b13200482c030042c00c000001a5100703002c201001510400340c11b030780481c3e0302d4505100d04e0341720100c1e0325074204250400040d00441c0c0d070304006801c501115091450565204e480b201c400320031040e19001424014141703811250100440c220480c0b65040c01d200d401d64940001e6203400c01c80310a14001d05000400d444c1c032601c04e8032014074071070815110041d00c04c131045d0050dc0341d820900482025100e96204c20172081400015901110109001002d0700a00b541c61b440d0142007482d00400c3e002000d80320710001c24250014100710b580d0003c0000ba64a414143c0100740300c941d94001c4041d500007400303114842d1100d00841e41501d0708600700701e43c1c80110890b154000348415003c1064103103001d060016901c803080d01c03c071119011383e0592045208030b00e0200300701e11060ba0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 183448381 1250 183447131 183447133
    0x606060f110d080c0412080a1704110405180102030103060b210309010f0e060307020d030f0b0108040f020d050d050715020f09150c1006080d08040210030f0b0d0b1005010f02 76
    0x264040303010301c280d580691000740c9071134a41c1042d540d10400d55114942c810101c52420340440c07003030b1300301e0360050400d07001000c0b59610100c5814aa142d440800100304c2d0418007a94440e4006038001c400d00341d01050003a0340d44001c540c0e80d80d5901304076000384081b001d2030b4810f003001041a01d0500a0589062050041c1c1303001d1454049213030700550381c4e9801c040e003d4090110004c83c00c1e029590b048043c6108401d80e4020300503000d11000002e0480d40795084035040c51703250182041c00c999010003500c0e03000d540a64584d141103d40e0000070304036907800300014030320b02c034151131038081070741c404041e00d4000d1192404c42c02c440849403544050340981d000b0303031800040074001c1650510306000360718042101025600e03d07140700400300700d0030045401300c192141d5440700001c0060200400c1103070325103c40c40c50102c102d070038a03034001201601103014040c04c00d6207802980754030b01c1e126480244407900c0148800d407002d100b8a0082810101112201581101100001510b500800b590307282104030364 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 183449631 1250 183448381 183448393
    0xf05010503120a110c040204180b0a080a0221031c0b03030304020f1309120507140a021c0516090e15070912030e03061003050f1f1e05040606060f11 65
    0x243c22074400c0350318080700000d80300310100981c1d00d440f14070082010b8000c10900d01c080b00d075201c1d0145d041c1c400c000c1107a40107800682c03041054000100362041910740c1181c50701180c06042c080060600301d6241e0380300550000042a65207842600c034130380900c9200d020300380074140b48881090f03168001140c000e500724154452888542c5400809183c100030b03200c8001070712083c3c0340c86154020203410580740109800082c03440c188004044062007031600d00c00204500ca0603a40402c480007403a0061545174240048440c04011045c03004100045000900d050540d9075007600d400074256800d0110900d0203100b000041c0000314076036a510511294807000401490510340c40492510303020706904100c1c0e403400c590348a540600c5914003d01204918401d0307141542011410050301080e00030699110300801c03d540780041d810300c031044d03494040004804000c458085c0034030004001c0140d07424035110030041000000e41c496000c5da507541c2d844400c02c40c80c92030240d508002a000400031035000c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 183450881 1250 183449631 183449647
    0x901200304270c0906200d08220503070c0b0c07031e060608062e09090f051509010f0605060304060b010c150912030b2409060c010f0501050312 63
    0x200503184120071403181c6034103000034440100c2c0c04a8002012001c00144000c80400c400b80d1b11000d8100380800a80200f03180c0101d01d111503564070040c0400c04c0a1003208070006000c0480000803281c02e4004a04103000b180b114a806a181e03485000211a60040d60b18082003811107041074031001e640d6240244030755825512010205001c2008001e078009005881c840017900c280641002816494010702d02070410507410b41000160320a1860490030005420010304282c6814000700d8101c0200010030300744030304201c0d035400c080f1000900346128923151111903901d814045841070820314000c00c5640c03076200304c0f80103481040c810254050400d01c04680854003560003c0340410050521002c0d900099550443d03a801981802c06031551b105d0f101c8090011400000909110a1800f041505444c1c0001686100b140d0140200351085601c41d8001008800440e281200c0050095459010109695004e8440407402842250506000045030705002450041c828001010076041c003007a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 183452131 1250 183450881 183450899
    0xc07030c11040b0a0b0403021e010c03051e0c0d09090b01090302040f090f0b150a0e0103230f03090a080712120c061d010c09030b0a0c050904110901200304 68
    0x724000c850b42c410b41c3d50b441e950566480c2001103000704081c03500303581c45901c1c6004210f08101d543c500b051008002c2100d440383e07683d20900001d00550300d401c040303440d948600201c105504c1d03540c401c00110325001807075840a00000410540c4078941d07075140b503042510384c500d81c8241c9407100c1c1440d0215401503001d10051520750481c01c0a03440c08403000501000781e88400d01c012401480546207401005c05108a50403018846454400c0c00d856191b011850024490812201484041d081484285124618040c2c2400c003001b140401c2c82260010036034203425542300e500010030740c1d214620821000840700c10104400d01224600204d115030440a91203042513809108001810402810b8035100000c80521401c1400d03420900a0364002d10070807015401c540344000500b090040c0341108200242c9028221070340000d034800c01283c448c4071420285d40500a140302d00360b110381003d820701c001400c0f88016151660b4244e9641b43c10004a400b00381ca500d00c00241c00d01c0b01d4104201c24012843c4c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 183453237 1106 183452131 183452153
    0x20c06010e18012003090a060c050309070e01080c060903070e0103080301030b0601051206100e060304051501050d031205060105040b1b1e0307140a0c0308030f0c07030c 74
    0x490813101c00b450520800d0314009040000005104001d00303005000311281c1c888c030305000900c40f0600c0076059810448100b0038511940000080344144112072a048504440c040c1541960020a0000940c032158602e5007510441d07900184000c10321090320b0095008182c010340381d50440c640401c0c440310282120341040014031004848607580002d07507030421011190081d0550f1408001d840d03a922445025501200110400090000100302e40000301d08604680b84140c0c1c0351001c10156498010740036001541c482c94507480d10030154065600034105041441c1000d580d8183c020342d5a01004420588012035215034400d0b4004202c00c0b240451103e0031180080d240f08542550f81c040c94402600480d0860703549058040148102e01640c0e8000e00803252588e200e082c050425030068540040303841c2c40c1c43c0040c0840c040c40c41540d03421645a55000c1060000d03072601075400d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 183273381 183453237 := by
  have h0 := BRFrame.cov_init 183273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 183273381 ≤ n) (h2 : n < 183453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
