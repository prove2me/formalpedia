-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2631
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:16:44.24384+00:00
-- url     : https://prove2.me/submissions/6c08dec7-c279-49b5-97a3-abd6218da709

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 473021582 ≤ n < 473201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 473022832 1250 473021582 473021603
    0x703060c05040312081b031012050a050c01211e0c11060603030703050d0b150c0d03060f12030e0f0409030c050c0108010e0414031201080d020f0102040f1a070f0c1809 73
    0x1b030b652240d131358100801440603656802800b003180c2001d01c01c4c140c50340348100018480f5004914000d81030103280040c507414040442401007004912054500d40c0c42040b1500040740c1402e42d401e138042c1020b100d07903461414070704400c6040c0e40350b10506039228119008212419500e450083c180e4a21601902500140c414480b01d030316138800d5003040002100062002c1103881001400d900320768406007030a200d60307000300024040f0507094003840c0d005086a80350168017500d04142210000140d000042c100405d91548440301c0d941c42511903400e941c048e201f042010400c0c03a01030004c14501c0ba00b40c50b1071140030b22601c483d40c82a0700d014103880c1c0d9042c40c1c80d55038549903103405449070210100e46c0640001c1c0490000c21a003072400078024020301000341082400004080d0a00440001c0040c0076401000309200c012001901d841c100d5006203d03503003598021500e1010540621030004102d0300c3c01d10003503000c0c8640b49203101c050302c00801100441c041c20719000d0080f6108164000c00d6184c3c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 473024082 1250 473022832 473022871
    0x909060624071704090c0302040501122307050406090519031704050d0c0612090c050d03020a05061602101803030507030b0a060f020c03060919050703060c0504031208 73
    0x1128162024501c5000880b070034041c55654078181c0200f40150007800030004201000300c0e41079070141c924101c1a40c141146414208800200115000e0358094030050f1101c09451405840c038800701c400d21400366a403905400c203a40300030260b50091240000080b0360020204c1e861502c41c884000e10039141000040c0c052440d40d031044200e082000d040d10010f0180130018543d114000703848000c2d0711400c000545503003810b002070720f01640c10000d1a09185486003180c001030010b50b000e41901c0003210341c500600402c1c40e00300e01d01080d164008003a406198240070001c44c00c80785c09a6620b00c80d4007660381205000d108074040751211079090107801d011610041c0420f009503c02038011905140c0072400f8034912002c60444642ca621440000c2c9944034005152030381030003203820030302d030031009000c850800d40c0c80c682d03844019010f80b01088440350810000c021081101070b004581c000001d000400400740050300b10340052009641480c0f103a02d04885403445015050f00c030b10801c40e00c8004140c131 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 473025332 1250 473024082 473024119
    0x1a0a0e071503050c0c030a050403140109020906060d0e010f020903070b0715020306130903080108071e0308090414040b09070b0a052218020310080307021302031f120209090606 77
    0x203000d4060b00700c04d042003118025000341840200030b035242ea919441d81c0d862941c034140380c04500f4540c07030701c525914080d180c90060391055089500000101c45c0580c40d103085804030707001001152003074120f80d86050716001d1207111076005441e66880c2141583d004a946103840328851159000080008015031102e010ba031441390301554120101a20304c0000c202c0e285007001c1108e0401e1000c0e0041110500100b0000e207041101c0c1010b494501211000301c5540c052400b01c1c0c034410300005003c0b80000c240001c0c030391100d5201c0c1c402c1c00b16034190300c0b61078281030500c0400d07100c0070b491074001c0b401003000c04a60003d00c60708440c0c404c81c2640d2918a0020803210b1175080d42d040324034103404c46400040c0000c18040c1c0c4405902200c40f200d90050b5641040c01d0130a880d521203611120b20768005004450143e540e1803404030384103a109501594070382d600c8092411401601e8100508060001c902041295076164140c1c81c0c184241c1d1120855100c00e4074140d81d51030225851035018010a10310140d009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 473026582 1250 473025332 473025341
    0x150e03060a1e15050d0803040c0605090a030b040204020f0f0d0606020d0c060b030a0204050a060608011d130f0512070510060f14123004150507020d1a0a0e071503 71
    0x152103e00391600e161103600040c10034500708020381c0c10302008418002480260030605004200a0500924000c00200890461311040c07001a02e4404c5510005007551542d4040303070301911140030500e80d5504650001c841d81d0b04116140280140390180104500f400080c8101041070070340c40d000c082c99001d56801004d01201d80c419034040c000d01419000607262401454010008810003082060030514000d00e07409050388800b552510035965000c1c040404030a06412100014641016842600b0005401d01c02003600070700e140320345076401c29150f5001d0050004c0074401c03815070380ca007101c02d0300304001c4ea005401080400030031150108050303900315080d003130400c002420030403030314002549050400e43c4201c818023514180701a01c0040410703e02d4000d148181c103805880c207190a008442c1494034100c1c14480c00c1c0840099110306664a00010054595020012641809000c03101420023102611148081ca08180c0b081c030030290040344c064140c0700710100202c40110305a000305d0150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 473027832 1250 473026582 473026601
    0x5040503190801090b0a05060a03151a030609060f030601150e031c09080f1009060603080c160902040e130305090a030c05030717030d0e07150e03060a1e 67
    0x900c020081200d07088145a1481c900c0d0074261501038003507140003001d03820b0340e451952030f0303114030044130702071009039502002d4412103407580c5000201031603070126020480750a500510000c03810380541c2e02804a64000440c851a41a00c200c0541e4442070140600001c10428041d89134012200511000583d528464402a11883c0c05404001e103500424202810b80c0c00c003940c4003044041c440d0a0760b420500e4140100380100042c013a840da1284080c0d1600d43d445484481c0948a0340c181c3c0c203014058111001031a00321000760356030030030b00c910156140981e0785401849803640c040040c0d8080c052007036a00322140703d000f0890307035070f1a4690540c4094144504a051140900c42c0440c0c5440d0b140003400036502c24004150307164244020149007101d15440f82101c1d28846201c100b0281000c030640344485074546000c46c0d58142855101d0804900f5000840ca405038812804083da07072043d40c0d41040072040e401da5078181c4900c00e06000b330782c40f03102030303030b0072031303608d550316022002019489420f52 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 473029082 1250 473027832 473027843
    0xb04111c0b040e0303100b1303170d051501090f080d05091507050303040b060d030f1110050702030a090e010f12170301031101080f04020a0b0d020c01021b0709020405010504090504 79
    0x1d48400e0300010221404403040c2c1525600c040100400344166003c502c014085451510f810704540388003c034540f000b140001407550a044069854500d86002944d50080f56060207000c00d28040545c03074180004095036038002100e04400040c0d032500c5000c0d560681c1c40308806400201102d800558440d030042e04110703080030b109a521010700004001501d1910b100b50050355036410282000c034802000581014440c89441d14074500003500140103892004041c104081c0354a1011140d5040c09185581c1d80c801074204000c0100701c59000c002085940c01e281c40300d40c049921640144810b141c00d0044035060540e41c48148620900071402c41000c0303124042c04901040000c41d081c1e4260000c4c0c2c01243c40b80f21180d01644507682164600364003100d000000340340743c5060340010f101c0e040c603482000c2014900154560f8102013640450b07282082c198001d656a0080c3c04400903104030768101c407801e900075884046009103040c0215000c5540c16502c0b1800c1600b8050101c0040c00c018008446 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 473030332 1250 473029082 473029091
    0x9180209062505120c06060d0f0203060708060a0e01030c0e0402150406020d0e0f0a0b03060301090507031a0c1912020d0f1506051204060507020f06040501050a0b04111c 74
    0x21200c820003030104203403036114140042035143e1501a01c0d001e007a4003070700aa100d0078002c0c140034190020f125503014030304941001c07800a0303900b82041c0240d4048000394150003418108240c95800602e082d002d40000e4800640c690360ba404105d05402d028000140300e244102401c100c001c5040740f0103a08140002c2481000400a0702d03081c4a0f030340300d6800310000d6041005110350407030b0084542600a081990220000807514000900c006542e00a0903078006d030110110b007143c0ca0950012110030344c0202100c10903522410300384d001100d00c4d003080c94058200350000e01040d16040c1522540e51400042002c1d0039074521056510140c0468420f080039420b20542d10030081d18044c5010086080a00040c48803544142e085a0b180c0c90308075009005d010491840300c0d050442c03205621641043d00090700352200d05c412410081c034451001d038607118040a00007841010741c00140607030401c0710f0070040480d44030140815282440e0740e250144000303000c0302208142040301007001103101c200015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 473031582 1250 473030332 473030347
    0x901030b0414030304050d140405091603020d1a0f040606021203040303020d11030411061303030c1b080f0c01020c06071b0801050901060812031005060c0304092a0918020906 76
    0x2403039a00102c0d42986c441d0300009a06420b640c102614048401601d9907881c0f42c5800d140102e07807030900243c061100d25150345480072080d486681a220440070005040c41802841c1c60b95545503204040c40501c188512601c103502841c00b481041d00300d5440c0d402030403070400e011000caa202d420042041d400c0c182c00700521030454005206001030070b010f0100b117039100c1c18581041d40e091040254040d00451081040600d407800b8514008120fa03418540700e91910040d242100c61015007200d0186540d991503808100228040760140e24a515801101d6148100500483c5c0d01c1c000e80f896550000d100704076520101e0025400407900300ca5102e9228a0f059980c1203150844000312109407480c0d543d004248a41a030034840001c540e8607000950342582030030160002c04000920440303205090000b01c4004911050041d20b00820070102c0402c040400f000745000f01220a01a25009003240e905820100740200c04c1c803000d4480340320030580840c581a00010003036000d041f1555001c40e080c041c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 473032832 1250 473031582 473031623
    0x2104050c0d11040f06060f080712180c27020a080105090a090f0813060201050c04050103020c070f090b090c1606150e01080106090507080c2508030a09020909010b0901030b04 76
    0x56140a0513540000304c3c90725204c0000c2240b203c0d55034030010040031000b44507501d41d00007012aa00d411a6000046254403450360b032040922240c0000c003000e001c5800025844090138586d03011074020310600038543c0700001150100d00c11a10741d80b010501c04001130160313080c039030f0714330b82c5c040008600054003407259141c050618100d0681101c0061001502c40200d40c5070681090081445000a000740d05051005030309030300842c051207040682c08542c00074000c10400282004003040c1c84171a0481d0349440d118000340c089000628050b629103404140340389100401c07030311003644410307603980c081d50245d07100000f809070f0742164008040e008001040c2404211011030007802e03000c00005800b03107403100b000c0035aa001403010341400b003402c00f0400340d01d5040e012195035851a04500a03480c0c1d000600100145034040c1c003428600f0084204155502164080080e450007151940320682d0780100103170994410070710450f08130710380600400024064600e90707900140b040280c420100d410342c064 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 473034082 1250 473032832 473032841
    0x30604060806150301150e0408162f01050a0c060b0a05062101050406030c090c030615050a1103041a0702030312070203030a0516050a0e040605030f01022104050c0d1104 74
    0x2403400d80c9010f121a242e40c0c1c5401d00c118064107000100003802c0070710b03015980203035440040c0081c040c12400619032640d22450081c000480f86d01c009500100901c0c182400320501c801001600c1d40300391a4008065580500305543d04000700c8c1c0e50740681c1c0000da503201c0b0701420f4a00c0d0366540181c051000401c040c0e44400141c00503980703681c01d20300f03401881254940b60300740c11707172243e40039900c0c0c14414808070368004032441c02c1e540c03000004212400410011401130143d035020381d450780c104107503002800e5800f00081000b5059642c51880c9881b00713054560700c9100b20300c207008001480f90a1148218506000b034900f01d80010162401d098101100c0c55800d8002c0396580e0050700000208800d82c1d1051191942100e020003099002080900000d005480b03110b48200500c8000d040358884e55540350441d0016000c0501990305450303540c240b8038041e41182205d003481c04440706d10a5100005464668441c94110004003c203003103010a2128041d040745060f01c000d40d41540100311902d580c000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 473035332 1250 473034082 473034091
    0x70308040519030b15040f06061704150c0c05010f050108030910050c070e060306090615040e010b0d051c030209030d11030f031614070b0f1909080c0f0708030708030604060806 77
    0x2034610042e0245e010002154a012805c45449141c207500740501680500f050020001e10400c0d00c0464445082545a54001d922000c01c418202424490541e0f802200c11443c148144000c1c072240c1000c825240548900b4010102e40d648107100210b082c0ca016501c400c00c105c89420304500d0948110046403d0004942050030801820418009030f41010040e1581c0155024003900d0641400e20001c040144203540381032142d070301c8501d0300c03261001c294082083c0d100020412401c00303015151842e00d40c05c000308070990811407a006244214000d000f10381903040d00a01500b284081084261650703e8100c1203405144402c0c0440d2a085c0e251100031400340400302070b00d14104080c40c50040a400303e101038120391b5101440754000150100b011540c0100c1542203015042c0da80c0052000c1d08069102000ea80505040c210411301c07901030b00a00034106180161001e0342001588641d458070701c1c0c490f0754240c2e8003c024960201d0414000f940d084440104049034103039a42210743c0c504001541e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 473036582 1250 473035332 473035351
    0x212150d0c1211150f09120105070e0f220e1c031a060901082a070804080601150c0308070318080d0c090506070611090d050706020708070308040519030b 67
    0x5802409019205401d810110011a11901c002030300e520000400e014045151740c8100d00810a03815542d00d180b00c01081d005408000c202c1850324030030041c0003000e402c41050043d5203450450349141010442007034a241021540641c0511f8040c0c00307002003041c2480b40000380614141003101031640407140300103604998001c659103803400c4500000351004880907104d2035040000c90b40d140d8001c05400d611001c240700d2010719201003034240c00d0200b2a0540d411000d58000b42000400034000302070800d44490804440082c2e8941c9035841100a920a032980070408440800000178800c0700e11a610240c207250104070f090540b075441501914000e400c03a02c490002c2142480b0182c2485038040c466202d00e807601d48140707010082690352140c0319020301000d407209030746a02c00100004841d0f01d41000781c030050940030b8904100da216001c40c000c81d00140a40000002c0d00040040d118003965004032000e481c040c984402c20031060207200c84907003880c4140c6400404100010038651150780c0e0314 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 473037832 1250 473036582 473036609
    0xc150f1407020f0105060a090b0d0203161a0405010215040c120c0608090d0f1107050a090b010809030304021f210e0f0a051c12050411130212150d0c 65
    0x4107029081a04071400c3c40510703890a400c1000d1943c07002c01b44000c40320703140400201607085c24003060291659000c080d405104da5240c40c074600105042c6030040b50f1000d5120b441605d552107070080301d13100c5c034460140107030700a088a8800701502030b402c0740c00c94400c10740140c041760780f4281486800b004c080c0a80b09501c00c101c1c2082003907089030140f584414000040c042d41240c02d04007402500040c2da621080025032000c40031110340c10041d40024000007400250713020380e00c0a50704050300010103900e0010f8414404911140c0e030000c00c0d02c1c001c0341d00501040081d0700502205c0e00c485030055249080226150f00c0b000301003c6084944134204c9030220214240411900291030714003903564041c01503018540310008110301003440301341d144050b000307001c0b400e04414045840c0d1402081d1030f07203000e1406080c80100400700709280704081081e240c1d02d846468102210049000f441d00003070600c01c18400103000900c4500107242d002038014503224185c0c0c416100e003401a4a01d402010100040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 473039082 1250 473037832 473037841
    0x20f1c14010b0406060c0f030522080a06060b0a0e040f06030b160f30020405060a0c030e0105070f0210050d090b0411030708100228020129010c150f14 66
    0x1802660041c140a00b4100061701440d40c4601001e40000c1f0301808106c00460f04442c42c0041d500180d030707880c01e84201001c80a03111604d2945a1880324400c548440c43e2640000e8901007840c01e5450090f0581c5440b400c00d4280d07400d110180403241c0e0350383c0c500f075550400480010290f0717031214018680030b8070a0143c1c8034680b9000c1c02140d0340c81d8545061114000660f11000d4000c042c10340900180c4a01d080f5003001004494064065038200b80d5105201143e08000654024156102c1c030f4081c0e070b150300322002d0300720042d60303c2d110390b000c081c100e014031020711741c09410300382088000305865250061030101c1c0f84640f40304844c8060002c0741c40741541000c0c13009028803ea02c22081100440150412078585918175035138501580351504a16000b050700422500083d0564504120083c544145108058dd0003802403440844003030401c82d0611021024401a0283e184d01c501c041c2c40d0018102c515460740019005010200012141c64521a03c070002e068002d107900d0503000e1741b1f141b1543c00c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 473040332 1250 473039082 473039089
    0xc0309180609220f050111070506070e010503010f0501030203090c090a060504050a02090f220906022d031f08030403060207030f0201050402150309032a0106060c020f1c14010b 77
    0x1405800c800030b890141c821400f03040c95034000104200d0703005503400f64000076464820701400d1882298144060080b89100a0010206500d44654a40d81d50020307004584001901c9600080c0540c07140d1024508051241c3e5001c0d074003c681208481084411420018000405000e4101d0725004c04039211201080b5500f440e00805802401070b04003941007400c504003140c00c1c0c10710000302600c07c10749200c0340c10707490118110340c041e1314170044014040741c42c1c0e90900c032002c0c0d070014a804010040b200386046411480200b908194402511500c0c595100d06100303035800140341e500f482920009400020f00d00d48204001e02c000c621030100940c503100c1505000e842d081d017006001c4e0659040408200c0160360301c43d40b0218107141e40800548039198000c80602e10301442c120681c0c42e005a2581102480b2500703100c0e56a151160003d00c01d00e6140d00044841c0003801c00c1c000e4108020400841c442d20349109070b003048240102c060400c4e0340450303c0d40862081070440d02d040503507590b14030f9031707280c10b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 473041582 1250 473040332 473040349
    0x1506030c02010203131113020a030b0907170c090f0d050a03032007031412070201140a09030905040903030b101722020f0604120809190e0703020c03091806 68
    0xc4280c0002c50861a00094007513966140503001001d5043c014411540e5a03628030081204884054045494020030f480c0a001003c2061010344200c030389100141e0703180d102e45514080b11034100b040300d0340b684074514a00940c1e00102c000c5540300c4245007a488170380c1c039502200300000d409040184001042401d0140c00c549004140080095050700440d0707034010325108840d00e503a4103113820030140c02a09040009405070310040c01d0581041408d000103280d054100746008000c2c0e000200f07050f03c40c80811030896400c0c0c90010007080d014a41000145810360000700010302905003c11000441800100041c4031a041280802c0c0004c603c81d41c00303840d4021065000c03400030490400ca40028010103418400307403000a210b841520340030740e069220301c03085d94010816080c24030948445443c120480341c0180072030078003030603030b0449001400c6030113510741742161040d45100b415501d403408102c0283d0300c4091544a140300c2044162415151ba0040e44201ca584602402c543c0c02e20764108081e14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 473042832 1250 473041582 473041601
    0xb01050108010b0a050d020405041a1305070e0108090c090403020312010501170a0902010909050703060317030121141603150608060a0906060e010b090a08071202040207030e0301150603 81
    0xc032101c0180140802c00342191070088203403c000d07880c1d0700d04500741c001a02c40c0340c104a403c01d0600c00c0b00c6040a1042200c00316007102200d182050f02c110181e2141260402c4440800050342c40c40101c2d1154040c0c44001d41102401098414080c0804085540580103490890041e40000750800c201550b45400e035014204c24640503414541010300904500d80c050180c0300510346c1ca2400504581c050b603079000040200c41018441d600c0c22a102400401e0184010b4409000180300d0f0240b61044000300da05989420020521188101410344070b00c2c64079507002c8407140e0308668901c203030140800031142a00d10a1401e8400d103070851600c0b03210107000f4020350411500f454014001e2041c041581ca0703200a1002c8006100a05800c0a9024042c59400340014080c058008540303510f440c3d00502250005660301e811240c2c1e02d86505648401c2481051440200f031700c40c4100625181d00101440b9000f4908800c5050400c0000b900312850b01441130fa040e0030380c00c020009141c1500401484 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 473044082 1250 473042832 473042837
    0x90a0b04050102060a1a0409060c120513060903021212012103480611070804090f06090c020a260d0f09120e191409150d0b040b010501 59
    0x910303281c400040d6540030003800c13100304652101003044d41c0c0740041c1402d009a80703000344140480c0903a800c04c0002880040b51110009118142048003000303240505806075440c420a040f6014841d12401d0040c12111b004504500800c00c3c000345000c000c00184c00da2500d020ba404611b03515180000c14500c1c5c1d1012600007207a040e080020119400c0724103298109442580318002c1e00d103409003200c0124041000070a1901d0540701641100c207030504101805110b84420840142c408041900340d0040314002407174900c04020a01503080707542c01400321100042000315006440f040000107444c41d11303080e4001070b4880003001c2e091000c000320b0364038200a407100a105003a8a41c1c084880340c801d074105000c119880b4040010381c1543c5900501d0041d4000d1100702c0d059001c03aa000f4100c01c1201c600c90310800850740d00002c0c200580c01c0240444006507100e124088030741c2c0501c00181310040050800d0349028840c0d850039101c2d2046216224460010446d09203460b00d441d104501c0103070400c504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 473045332 1250 473044082 473044087
    0x206030a23071e0210020409020309060105030c0d06112b0c051608070c0324060f1d0414030c011d0c030607141c29061803010f0908090a0b 61
    0xc803541003c2d00c2c00b0040d0011680203a1003041c1c0d003090345031000301c01170040690720000d030006031808a40d0280d40686c0d01e040079031b003180e40c0c0d49080503074502a0010455201041d40c0d00c4400054459014805100050340d0340390030711102c4084448001d000400742c405031050300c4a04422504207200e46407000726103042a9050041c40802e140054115003070050854000003500701c180000e81c1155001103512400000c200c00d2151041021250142000f9541e103003807000204058503c801d8480544013200301141181c0c05035580059503040c003038800d07030342031007030740c40502100d4030030f0008041c4108507100105018a8041e00c001011180406004850304850401e80d419a40440c2c001d400c0070f29403030500c14809003800e1800141c0704d08140e40c10043d1003042d510703d84010340e81101c05104125a1089005010514411360003d40f041441d035002008110b5402c5411840642840400020b80001824000e1a81c00c03812908844411b03100704102064444107450023054400140c460b4015590 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 473046582 1250 473045332 473045341
    0xd0902010f031a060703020a06020d1506090305030f0919031101110f191a0f071d03100c03090606030f050c1203123c0105010201021e070206070206030a23 68
    0x35a4481c0358440c13000024100c0a01d842044030348045c50b003003041159100c1502c40044014980d03e14100c1115000b00302c0020030501400c000310440ba04040034605d00440f10311404156481050900c0c0c2c004110b5448260000219164002640c805e120090300241c1c81800940031420102080702ca5034481c1035620082d00c1c01181c0310900b4050f500c508034070f103900303480c00c4400e54004003070300c454558030305040210034081c80320a54020195615010310913012010090702d8070380c4440380c90b42c1683c0106c2c004141382d2415441130400051a00d400501050140d40e201d059410581c41a180100300c003103041c052000901c08070510b0141110078140510141e00195224050b1510111002c2d02c3c8000044150a1401280042d28039409540701100f8502c607004a82400c005c2500d0050158100007140c2540140300f20b1311030306911801a1450700a8900401480c2e0040038101d8004106002010040c1c644401a50003000c245602203441e0118070540d0360b542801d804585031101c482c00c20b00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 473047832 1250 473046582 473046611
    0x50112090818010509030f01091a0103021804210e04060503150c1e04080a060b0915060c1507052104032a080c01020702040b030a0c0620030d0902010f03 67
    0x4400102d010910710780c0c02d5600c0c80040c0c800340901c42040781c05000f811040740452806601041e1502d04c15465110213040307041141184501c2400300940109808141448440000c600154882d1188103c12400304c1134401150721841980d0114011030289104815149002c4c042e800140c0401d8000b45451400c044039100141c101038601a0020000500107441d5100e0724007028000d810f1600c00c03580c03165900d180035a9540d48500c140d424a181050b21001c9140102400f40901d4100d000000a07922010400400b5404000c542507a03115441c42c041300c00782000946840b030802515655250440380e0055410300a1503000702450030005000c1100294201101010141c1a910000543d1406181c0300880517406c0d4409054280046416a62468150001c00c8280d2003a00c06000740d1000c0d006140d50340c1c440c4d42c0010700181030380c1d4042c13140c280324a8041803030b40d23081c100020151a940300300c18119804688841400c3d510f9600000070355030850394040152916180c1046a50f4500448 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 473049082 1250 473047832 473047837
    0xc0d080f07060e0a0b01032303031b0717042607140f090408090a05030102270307170d0e011b030318080c0609060c0a020a060b0a03060f060501120908 66
    0x8402858000318003030090060319402100480f241c0e6040340c2044240e401d202c154107100344400c550942d0740e24941e054032074850b008d4029406985006500359141d0030b401042010b4654081e00c120351060210700701254480301c10b070b6042020004081d64403828486081d00c0d568400701a8036510342d61100c0c40022440000700d0104848000032070700c000000d090b0000d00c0e030171521001c45611100700d5040c48207018501008140c0302408850451445030380354245400c1c1d000700c940182041001060300825a0344c11001c03980c10320f40c01401d07150090b44440004051071007110300806180d200f02d5481c0c0b00c554104500c201d481e1400d003007200e2440200860840150080c7c1c4009007010341300c0d80b8034181840800c07004030f410765200754041d4480d245030b04541d940398002c44520042e8854440852608000c120840b00000c50a0f4041c01c03146c0800e440d171343d01030202c42e031109402480e6840d00202040c0240700c0d0761070740307040c0d8000403924a141c1f60004044204c0303008030403007092801c1903140001c2ea40408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 473050332 1250 473049082 473049097
    0x30a050c060306130c020616110703060e011b0503040b24010c0302071205030c01050c0a08040f02030705060d0e0d111513170301090c0804023319020c0d08 68
    0xe40755529611000070808004400107000425420025104a41a000b05a10b0b11507810070440d00740380c20308548111141104040320304403035004000c0610200300c1c6034012003240203195001080c0c81400414520360210400f100d840043e40110601040200d07941516410180791111803000d4030450030a04403c0707006020050521a0b101000ba04140c000e01c2004010880650070b8007400b0203a0400e15242d5100140b0002c0551a200005400a966509452601e4482c0d9200d03817613580e41c1d0344c610b001d21540010036641841090000916079880c0e20080040703214110700418200710072101c852502c0880711740b082c24400e84800b110035080f0006280003820aa440001c40300ba22842401d4800101c0c0d0741014140780690345944054020803401903048421035042002f044441d1030b42111101760664000790f008038180d4a03c01905000740041e001d100070080c0c00b58103a50481844900e66110300264501104001ca03240205a01030042d1480c000c01a5480c0001d01081e941c3c00e1100d115010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 473051582 1250 473050332 473050339
    0x8030307090605070f170a02150c160507080607030b040e2109010c0b09030705122802030d321504150801060806010e0604020c061b0d0504080a020c030a050c 69
    0x2101410b00516885c4001c103140c201502c42004104c0b00b0b03c205155020001d00b402502c1a9900030120311441c80075244200400c81c0b08604005905110000300e20401a05540031f02c5411030110b50b21400b4845140144466140040e0b89440c002c03c4c0010f40e68036400004070b41d08003248072642501c9114440300303410a0318a4681e81d603400000140e4800d84041e1020300350070021820806032440000040003458043c9085a280009140801c1c1e000d11034001415403407240f105142c04802c40d0952011512901801a6420031041d901850112544c3c218954070940100721b8101700c10303000c00720b03070912120155019121840c1040c80c00d418000300c140c0b200e028990307a200c103004142e40304148001414105000f489065901d911160b07071180c0030300490116a0304003011a03094541403003141c158584c0c41001c0d00560703885091110402c1c003000013290300c500080008220001c814450584558812042d132921070001180081c641481440c03e507009511542e040701c04910002030703142180c807084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 473052832 1250 473051582 473051587
    0x503150f0a02070b15190305030d021b01091212090c05060901021f0c020d050301052409030a0803010e070c1a0a0f18050c01031512050c0603100306050108030307090605 74
    0x801e0345200038400c40340060a0419810141701d01c40000303c000c10012041110329100011a14240c09083e0344140310040c40384d441000490982d07400364018042444103406403103034009a4281490035624400d500303ea121691010b2000403a030066503030404994132280412102159503111144c6804a020303240c0b0899010a14060981c07081020588031f0769128502450610380b9031905010304484840070016004006011040740d100d841680e048403401400c2c1c0e0b602c13000380000e0301c0110000044c82d10200c40d04100064607074078200102c1410070301ca41405540e9600d40301880c002281d000e480c034420420f0311011540031031020b09a0360481c682c0d5003050311194a078220f400c0000e0070403803c148911410520b02030180f80481d100390121301c0c018029904844014001102241c0340308801c0f030100c84411009000c418025104461041d11400886140c0f4201c140010026003040700e44906104520a05000b0464180200350041944800440c150b040080e0060300e03902c2640109d504003c1c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 473054082 1250 473052832 473052841
    0x108210313060e0106120c0e01090c0c020105030a110f0c0f0f07150509041401050906040b010f0c03020c09010b2205150a0e0a0303030b03010b0306150d14030d02130503150f 76
    0x85d07000c10020300c500f4074000660845840c1485144100d803180954105000c1c000180341d20700e078000e13409190340e103581c1d6030161f1038103034015a0b140d0000382030203144c16503074841550b10403600c00003081810070183c4401d803101e030994415841d00f06099a41d400c0c40d040300d032100740c00d6a030004040301520703a82043c100f0b4100311000121140c0c024a681140e01a040c9580000a003500800c1c09060b54000c0d508c4c0d1a140e0b507044180300584e41d6150403d400a0130701200d0707662903840384440c800300c14828415900c000c101c0400107101800c00f82c0001c60b101d20000360011640018101c0103810756002d10481e14050b1420000544e040440c03034000d900014002055078480703205510b0300d444500020420842a602c90a00800030140700c000c5501070742c41c0c0702449005107400510548118485d803070b1a40e0804841c01130244c603071030810044512000640d102c0b8641e00041c00680798205e0074440042e02c0c0c13114039020955104440d40314902075041a900204000b80c41e081d8581e0022008241001d20b407507 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 473055332 1250 473054082 473054111
    0x40b18040512030a0b040b09240105070b150910030305120703020c01020c10050c090a0b0904020c190203150f060103110408070608040b1605032d010821031306 70
    0x148180c2440c01d02d03a00208211101c0b4243d881401600c500340d0b410840f0151500a0140f01501990341e810101d405464818042410503c007200c070351018903005080c860b09603140a43e0501c29036244240100844000e500d40c10000d14165124003015245000ca0b4615100940b49100d01240350070104081e06c002542d19001703804a40e0254004002195200340c1075003c261501d4032100401070840c1490081240c101c4001d0a6449450005046d001d02c2868194441c030b85070b00020f03185030426028041c02c0510300c000c0c801000030309256000320b0303110743c2948109400c0a09a15881502c440b542c0c1c24410f4900a204005070b00038401e00b400502034120b907100140d18090342d8401d070220300c14641c0100d0032a501c2007105000b80c2c407a5141c40c0540d00c500648042d00341c96005004c0c0061b5081c400641c5002079882007441b5401c0d000a14241d1304200e81816031003a000340c10010880c0d0004107042c101c411402040c4407002c0450302c0090850500c80c580201c0d00074603ca0140c000c40d01d840c0c88800106 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 473056582 1250 473055332 473055343
    0xe0705010c150915020a03060b1e13090608060a060b070b04020d050a080d020a090906030b040305070c03020604090e10062303031207030b01090605030c0a08090109050d030f0b040b180405 82
    0x44d005030f4541907040031041c20002035071014100d100080d0a1410008440c00c8080940d111b06042000380040b8403030000c140821500807003c02c0b220018005000070f0600064841c003806004141c015020501e040360300c00042d07416551042800e45410891305e40450040f0210341e800ca81e04646d07100d005910303410441c0c5010000900600080d100103484110303288540d005040c010044e40310344014075603550903442114124480503000820207400038000a1043d001084a1441000049003a075166004100c29030041c3d04012401941c0703605815184d2001c108110780c0d251941380500406080ca01c0d0b04069807405d800072001507991b00c004018079a4184195031182080441d641c400e8600000020050809842418003007800050080b481728441c0048a02c1441800341c0d4500c0c0058100301120442002404e00190b9540c0c0d514003070010b4004c0c0500002088582e801003030b11030001e06502c085440c04400c992046180203684038858503500108481011485002c180c1c0d5551400e01d2030610 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 473057832 1250 473056582 473056601
    0x18020309030c060c040512060103080d0b030307060c030621120809150a050103030f1403011203050d02030403090e0135031204030203120a020903060622020d0e010e0705010c15 77
    0x10f0007618200144420060041c1046810840d0b02c9504034072809005031b1a25030078000038051800030050b070301080b00d05400c42403400e0b00160850386402d03103d8032401c00321500c06201d440000c0d214142003190784031f55410034070440000300c255400c90714a07645540b03003002c607010000248520980003803454041072010181140ca20300a0000f14504144503000502090104801103101d1010090490b80b20305010482d9020650203140b45908200c051020380c0e102c4c000442c2088800c021480f009042d40c00550f00451107a29000001c60900344903550b504416000141001d40500d1039004d68811090b090740d08242070102076024800a0b44030900b036116400c04012030344485402c2c0020140c4c00401421510f5031000c2449040d01c4120700002640315070010300358035901c1240802c2841c9000c11312803a82410808000c032451881d0550481680c02200451205075511051204002d00a010f080300e0149944058050f150519002070214502d402c00a040c1000c81c07040304080090561041181 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 473059082 1250 473057832 473057857
    0x61d010f0e0d1a1f0e091c0809010b01050f09010318050d08010801050a060f0b09040e2a030601050108010605030c1e0306031c050f0d0b060705070f0f1802030903 71
    0x206015040c03512074400071010f03d5000c03c145500040304100034130038800f103115894418400c003500e450a401101079025204e020940074100301c4507201e134044034207010b07084545c1c4c990300d1140c544044040c1c211040e803ea80341c18070404110110380d810280e01151100e40b024200021049030b02c41e05944100c07205003000f00b1522503010102c08040d0030031340541c126480d240092201c4d035124410101512040e12451299103204a030512800d401e14015104041d0b015100082e03503440e04106500d0280d03e00144600f00050f801c0d0316411a184980d01c28590500b68002c040951509000a142c00340503c01d2204111000c408034203000f500404584174103903900344001d20401602c1c00c8052a61050304c2151003403041c01c0195030f288220140ba112113400f5501e40301d0030084620b03580445c80c3d00141e00399049503179a1881ca18641c0c0c3e0300001d4120940160020310500f0304114043c40800850342003141700361180b0008000008001c5060401405048400740e00c1c1c3d21070030305182c9580101f10b0407418 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 473060332 1250 473059082 473059099
    0x18050f251b020a0909051b0a0b0f1207030b01020d05120f100305251d0402090a15030510060e01080a080a050712030f0b01030908030a0923030d06061d010f0e 69
    0x250300d081a00524070a074003406c11740d60190607403a02d0700644100300700215007006040500300040e68402024000c00314031018054685240c0b42c4100002040c2203405102190365800c0e0001c8659042102e4900740906003895450b201000d800744004080080043d2210196000001d42503c01480c2050056074132908444070644c14040565100150340020b1a4805600f403000035024590b1214290410307044004003110340b582e03000d210035400002c08031201641c54034040f5030700311200c100e0340009601420141c40d010a200304d0400075203450ba44030620180c8600018001c4207404609010a290301c56034035603803003410a100f610240a102c10140040c3c02c51202c40e40c86c190503402030381d50160480000c01c4840400c100560880c0d03074504000d8004601400041e0985440b540709100e242e0003007250f806440756040040d4005405030790050301a40001c211450720000c02d0084070080c02840c244800d08400000440f1821540031100e01e04104030250311a50341401607074800d4884074081d00920 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 473061582 1250 473060332 473060339
    0x403050417030a0210091a071b0c08120405100503060d0812062806030e030f2b0c0e0d03030e010e07032904020d03030618050f251b020a 60
    0x54a94003c1940c0310054042e0044407690103c1074840c0f41e020f01e134848040b4a01007014054412041401003248c014081c0e841c000c0c01c6443c440500b01d00c045803158500591040c05e05102038140f0091407406a00c2d01000d100900c1280e4945201040d411418904161203681d0a0002090461140c0c0040d10321500002c03049082c003600d1b90320307902c0b5503000c2e2101060704c4240c1c10802d1903c40c03141c0100303e04508100b030a02500348681c00c240d2410244004076400c02c00058820200d03684070307001090360701e10700e0b4031580e1098020f662007041a0310b40b01d808100e500d00241024200e0074280319071610582d01d00784600d007014000c0c1d01000c541304000780200a018240c840c095a01da005000036210081c42c0c00300850101043d00c41900c0c42d4040013906402502c1c0e81d824030400c90ba0079901141450340b01c036000304244005554070094203403000c0006c5002c2c10410003400c250302c0081d00c165440d0383c0807003a003400c4841501e002d030039401c51840e20802e05100324a0f2003240a0300840c0085d405420450f001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 473062832 1250 473061582 473061629
    0x80406180605160206091b04020913060501170c071103011404121103030907050d14010203070c1226090c06071a07080103050c0d0201050f03040507030512070c0e04030504 75
    0x90703118144100d4070403406200d955084e81d0310a0115040602170b0b01001c5600c0342008a10300c1424a400c0182002d42818032a00000c0e1603a590341c40e10b00c030102d59500b020421583d0101d160442525a00e010101e281000c00901005101e00c03103018060007070201084625480940c80390700c1142140d4400361490800d49004244403105464801c0050303007091041080700e80100c01c0b07a020302004001801058a040d042c03000f054074104060b80d0901c41042c0c074612044003800118440c0705156182c1d00016030a20b08000c800c402056401d0404c010484035140410b01791640c01203440d0400c3c011a56079840c41e8000b8504807540310000d0f04520003040000070050703006407440036031401c45c03850042030783d403075004651502c000d100240c800d074011161440e0300d00b0600300e100342c043c0c010700d05940390280c12040e600055005031030480b2141d1092004100b0f0000c14030801000f2403104040d203281090b261107491184809000e00480c01410390f000c01e00305406001110020040404003440711300540244 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 473064082 1250 473062832 473062841
    0x160f06080411030d1e0201290a080316031202030903030609060609030a0605100911030f090c09090c09011a0706020c0c030f0601140306070f0f030b060c0d02160b0306010804061806 79
    0x54498045080c049017214a0041c041d003480c000c803a04c0d841312190b4040b03403104e91140001840a030484603040d03022400c0e400610040642c084244004007541900386401080e00e40700160601c0310074410310a000c0a0b25001c011660044411100910356898440c00201700b81f1450360039039454032607036a803d0108500394121031b118401021141d0700490380c4103044025a0703451040c0b00000002040010340c000d4466500031b4012a1007011030303104c1001e103c08220002030984661110f40d208001201151400c1e00c0064050138850400300c00f82c280640c011906030003044001070203950081040020600208900c00d40c0e050001c089a074540485c2c035109840780e500b0f01684210300590b00c40d007140c5003030001d0b5540c06904030790385001c540501414221480303482c41040b00e04040d00c0d00b044241d0307503581001411346d41c0190f101501c80c0380003255000e45040b4500c1c0801c1172582034041c0811030303840c00c042540e60040081c00c140000b9521740c50305000400e4038400105070074100140f00c00a10805030300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 473065332 1250 473064082 473064107
    0x50f06011508010e06010507170c19020910060f14090d03030b090906040215031f06030e100608120c07030c0806040b0a0b2107050405010305010e160f06080411030d 72
    0x442c20407998039009512960740c000c584490201d04100490380014803640448400300f00c2032a11301e03080500314410b1318109843c4121f841410300d160f00c0b001041d49800c800d459000f01100303050340c144a01d424405401001100042030900ca025829600740d00700403412507015841c020919582d1015501c0e01130010160304a90b640608610320014442e200e000690500440d0014880140c03000319403d2000030360710083c564031442c611500d040c1c0ea48041c43c08001c000d450030341c4000c03444030500c0341e0640ca840d03400c1000c84100743c1058010403ca080200d9016520740e14005520303600c10b41d20507003a01d0070045620082541003105000200c154011440c1b03802180314000941040e00d0f1203a40f030054079040380c50719078040203d10031003640d0721042c4000c0945508031000e486030390792f54030001811603030240c0c010b8600c1e075102d21944200840500c507060130201c452a0b0f6400c1c050a0440d40c0690780704500462044c42800700124040c002c0c0302c10101d50b0501c0c02400c0f02c030f001c80c218000078010000000d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 473066582 1250 473065332 473065337
    0x806010905091e0a02041107060e0d021618050c12090f011a01080a1d030a0305040c1d0c09010201020708210f01051507060f09030807020f06010e070804050f060115 72
    0x745401c6801a03103112042840e24410000d240544c4580c00300402403246a04044d1845810088130b0300040803809484074402c00d0340c01814080d800c1d00700290a04244203403520010154507402e0020100c40c1c4a0881c202c04404030005455440034000e401d107201c1c3c04040c210010800040001c1010002a070f802c451005d00300a00000701c0504140302c11401c031010990202d0990740008807925035591008104e448600c01d0b1400c1000c80b41c0c5c040382150702198000340026141c40812090000d403a0303042c0e00074003245807511251560b00c6079203002003101400b01496a0300000700481d941e8800d40503100d80a8000144603615400c2c201d4000c201d1304030710314004150110000040c081032511030000d0480d00003510306400200b000000090540c020102140c00c80d54814040e000e0021511032403043d240700e5281c1340b80e00d08285c40040e24184d0780c00500d4186901160050101001d910b40383ca40000b06810014104d032240d1919070f0412001050110451044000008440724540302c0310380032a1454 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 473067832 1250 473066582 473066593
    0x50703050d140423040606030b09090607050a0815130504050f0c06041e090612140105070f03090819020606040e0106080d140705010f06150305071d0307080601090509 73
    0xd030400c1e0ba211601030360100075900180410404050041d50f40c0f50400342e4051210045401c000c00182118226005280002d60311402083c2904022445541101100004092620340142e00801d503110710440c0004100450004c10070840801d150134040101c01404800603103c00940704004000450303040d14244281909180640801b150b0750110840c042c0845141600b040300400000d0010303132000d140748402200010702079819101e89805070030030254541c0d6016070343c1005850155510003040316a403415051048458008142e812440c12a00b4082102003c1c2d003401c5156014401d0414250202c41c00c0c0403407480d502158443c0701e4102100c080001c000001084c50803182c0c0c0c0d003d5201964404940b080720a8020102c600c088082c4101c01031902d48944d441e103003500c15110050a000d91211028000c2d4403031520503140e05e00c024034080116140000000380a8040500c8142226180e809040802d48062040798041c0408078101c2c0d07e82d507540d10000c03004003800c440402450048 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 473069082 1250 473067832 473067853
    0x9030f031909140a1502160f030311033105030109030c020102010608032109072103080601050c0303060f03100e16050a0e15041401080a0c08010c1d0307050306010305070305 76
    0x492100b114203405488400040c0c105002c03d1204600b40003505d080d03101d51408100192210b008a030040c15014514641c0b95103075282c003500ca40b82d4008600d10f0b5800502901e8400c003d0811004101780205440241000040f8545200d9408a41201d0b41650030701c80b0502c141030308000b503a08803a100303a000300101941c442c0401c1e00c81c01079031000c6081c841c00038100110210890103054010140c401924941c590360140c240c4004030114480c03091009000c0803a0915070407100d2140d2188003820030900e440d8943c00855103034400180399520914500808461a807410800d60001140000040001a0036600500da582120620000ca2180321980100f42414100c084608440040003008056111851300e046108001c2115030b81040d076581c001c4c184201c41225a030f000b084030a001d0a40840c0908180301d101580d40c00c64070341c03030381012414014070b0360144102003188400301900c41c072000341d400080d0500c05950b2059915226040000c0107010005c00e491048a105d1021a8140c2c040d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 473070332 1250 473069082 473069099
    0x1309110306130201050d0e03270a05060a0305040c030206030916050607050303010e13062a0f02030313020a08150106020d0f08060d06020d051503250b09030f031909 72
    0x782100e41c0d0904562080d2890015400b40c0003078242c818039441c001c139020910790841c40c59a08004031108040451240740c1c2c405041c0e541d400c401110091fa00041c1e06810712006c903c0500c00c0342018801c040da554009402c0c072610500c402c0265500800c20755603801c104d041d50f681d400c4c2e5024881044a01c1003000106860507100303c0c0e1085500030081c5095030f282440f102c1c28000c00800489142d03086030343c21030004004d4807802d105511a8110811401050782d40301014484e06002c08050291b010340c0510200c2d0000192980100d00d03441a460b10700b400d00c0818030258469012207010311609c1c5400e201d04c112082e02e00d0503140c00c0c1d8221b0b014018145001c6407848900755040012500c80000314007a800c00e0011089028010b8401600d0300e8000c5d400c40c0c0c126282141c003a207014540c101c1c0702959282c10b01c0201c00c50090b5145010500c80341a24144507416584500c0a0300303400001d01151540f4244482d8040280d444180c0c0d854400303048107169600d5100059100017880c40ca004a802007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 473071582 1250 473070332 473070343
    0x1b0702220c0f12090c09020a0c0b07020a0b0612101a0411092704030807031e05040506090a0309050d02010e060313150939030f140c030a06090c030213091103 69
    0x25007144045c00340c503180c20998030007540403151070f10400074400c3d000c8c00890105410340d4060700780c65004050342c02e42820107140002015003050700ca10507a60720005806000514030940c5050010001103c0401a80071201045141115500582071107040741c001200ca0000d442070503c155010b001c10950200e480d02d210255014558121403c200480d0109100342c0d4a15030140741030070001038442c442d8204411861070f04500402c1180ca4408000030800d0900550341c00506003001005e508400703aa000c0e0120743e1038007806004100145030300f03055a03c00c13102c80e050b543d000703802e00e5928100844080d01c1c0860780a81030f1100700b8030800c1d08000241d548600510f194100349400074054001480541904018141211190665940654040c1c030030401d840114850f0003440e450308007526045005034107011140c0711940012310154125200421401400759005100184c0e040781c9151070100b01e0782580029400006100700504106100c0d4412140e007802103840083c041e80711820141d803074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 473072832 1250 473071582 473071601
    0x703050a121808030703060819060b0f0a03200f06040b0d0f0c0f0e090f0705030c1207081f081e030403291b0702220c0f12 54
    0x189003000404502442108a40c28010710a9030208407159078444150a0078035511094440240001c24030850b103425210f00c03001414018041c1c200c0c03c6901340000207040703107950050036064071030b10301f201e2903540c000318401e443d81c0040803a000b09850f414030b04030103c5081145550348610846507030040c60130a80203a50898010207480c0b03881d00307040582105800c640d804141003038881c09502c00d0303c0e01d10700510001c00c008d699590046d101d070b000d0040c403c8002c068150f001b5220001404502468003907000e601603c1806c0495880c6c4500124804500c40c80d84620811260304040c0814650b01142c8c43d40500d014940c0c540c82004262500c12009441c2e00c00e200d01d65000040111980c0c1d000c42600d281c6030321120660f41401c0c0d4a480b40c0340400b00c000490203c0b1403000741c1c2c401d0b50048030010590010310103103d40d000d5040c01c0c0c0c004102446441c9000e4403d01500c0094a00d02150400c460070071a456081407010b0341c0750f01c502400b5012600fa0780c0010503140c40215410051034450907910 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 473074082 1250 473072832 473072837
    0x417030405060f251b0e060913031101020406080708010b18040509010908071a1008060601080c0d1812140708090109030203070e090106050904020d060c030b0307090e01050106050703 80
    0x107016100408201e01c0c1e02072403608280c1d040b003905922001307000d52994907413580506010f0285806043c01ea01c86028a6000803c090205c4414046645c032144101c5900408511040705184c406040c19070701c111a0425004140d0f0001802254841c0c0c021a464080c5905440c0e00c00709903250442c50b80f0a00440c50201c1e50741a15001d0503200e460146c02c413640108045000150780341c00384e01c0d1800d80f5880000705a501031980d62544910440011a003540301c4803c0300015000c070300313015801c0e4441002400d41410494581e011076440d0682c281140da032400b03001002c00c0040f1641889810f03180541030700f070b9844004034450800c000d00445c21100115010000c4600c0c0c90310a651352030154000c14402d40c100903a1070b01c040f0050301c0c100b003004080c1861941035452454404540b50968540303400941c003c086c014203100068031030b200e00200041d4008004100001d1210088000702681c0703910640c50303c258200000d2a845a5100e00d4400000c0c2c80240626a281d100c01d45a034414103c00400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 473075332 1250 473074082 473074087
    0xc0c050a0209100816180e03030403050a050d05090a06050c0a0903020105030c1306051c0b10210203270d081f0f06091e03021c060f0e03041703040506 66
    0x1850710b6004158086020400c4414407610344c00040c0c98080c0d1030f140050b00b100c8a040500074040d44400349900110b11070420710250b03200200f400d86134080030304000c0a126010480b006407500031000d036210500c101c0001c001c18075000c840d440d504c4800c0441660190701c1d0801040000032014200c81600c031594480e030007050b1456004481a91001340b04000c00c000c00d20251504e01c0908078404010b24081da0303400c0d11040601d4400c026035508180c4580128076100303040107680c4440b080a19944818240a6078071190740320b403c40d0b6050f20b07100c0162005d20020400c94190300c503c18540d01c0350380700072403192104210207402e551085950801004141c0c054001044040140d020560400340300c01d0f00b40d00d06170f0b11000051114050b07003141000c603031402420300580124108032000e0141c8240d00d076065502d1500132458040d804e611266020010000500c140040d9801403840101c1200d41000486101d031040b603243d4106015107003d4100d4909480402030b40001030f0360940d00d0003003a507131 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 473076582 1250 473075332 473075353
    0xf0f0b03031b032503110706020d0e030f0a030203180d0b040602160f111f0806010e04060807030c05031606021005060f030a03090e0a0905250302060d020c010c0c05 72
    0x50855000d0000d03030244020000c42c00440c81c6030510f0309001c540e072103009404c2181440d02502090410f0040c0840368000d250030447c00c1c2e80020039a802d017000d41051a4001c0e40e1801003420316812582c43d030390711f11400c1000030030190b002006000c1d01407a4841c0f140b07624114800c00c00e0865010401a049003000d401203400b25129500601010b0642904000e181050369509030500b408240240c1d540140020300307600c507080c0b050020003524a5010002998201c810015005240160046040007500c1e02d410226031101d5001c1000781c1542400c4940913a920319000200308260f001c0c15029015004155140c040548490425130b421500a03007103007481a5085002000001c0070b45600c1031410518039455102808082c1900d402640c81150301402c19200ca038400328041c00e040780341881d01104d4404908040f03140003844c0001000c814450342903090540255049800103548204005421130070360803654000c080c915000320003400f80700d130f503140c050301e41c1211190080d140307400441c0402c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 473077832 1250 473076582 473076607
    0x90906060a0512010b0702010807030612150f11030604060b030402101b0204060608100f080a0f0515070203040305010b03010204180209130f020904050c0c120a0c05100f0f0b0303 78
    0x1c014071041c62800e20b06042d0a403c5401c207004080c0d012180205e400200c900941d40c0c0084640d83c881944d06090052600e05260407100b102d4100020b00520050300c00009021440c3e0060b500c01d000342402840340e0228075605070302c954000d440c2c20b880f503440c188000403069408030603244038a0300101034502200b80c0000c140ea2101c0e0611080481c8c2003141205401030781c95120740005880750740c2d0385070424a4a15085c1c010003045030420307e004170056404200c220800152003607080d601144002108070246441480d02c2625015075216640c035100300144540c1c0080580304a07401030000303010b03106905041c5403c030700c00d90240c3c42d0000005229404a600c82d90000c240c0b100001e08034806200e080351004040712118810001d20540000e0070120500e801c1c000c07290042c2c0e8101e20549072585c003c2d6403a5072903402823401d064031100030880d840c40b40e010b4280c480c0c25030b400c942501c112030314100710034006000c40362011584528105050200101c035101c0c0032100400a03000354035110160f10b11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 473079082 1250 473077832 473077837
    0xf06251409040204090b040506180c0c01090501090f0b07111c0e130515060f180d05030307030615050307020c090603010617030309010e0d0207140f0306040b1b09090606 74
    0x4203a080020411200c99448501c010002410a803c0020794808030800300815540007609580c81801d2049403a098150928405600314103448d40300b65464240b2080540075108560010b011946047c41805c107020541d03500800e024070906681200d5035841900b520401440d403113824541d8804180c0b8585014040f04001e0b040c0410b0400110301d00c00c0070700045002407a0180031081e15154024041021141100320901c8002250307814109a80704180b4000e50040016001c01e490500d0000001521009100240309820005486c0d0321f11f480c42c800f0700980a1032160800b07191a00039104d8207540b1600669002d00800d41c00b030820b01304800d00300802e508014001030b03815507a0f60700010711045d00c1d4038088031a807410400380d62641f802129850855415030403150980c0c0bc65007560300d605070f0101c1d00d481583c0c5100c4a0002c2010000c1c00b04000e500802c1780987c04d0301c074600a100034840583e018504c110709123412840b0003030344441c3e081780c64001c1c41c03c115000030502e8042001c5181c142c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 473080332 1250 473079082 473079107
    0x9030a08130812160306060201200306150304140d030501051309140d09031101020a0b0a0e1002030f0f100605072003070f090c050f0304061802120f0625 67
    0x200d07030030500c84500702c00c3d11100503224200b007031180c04441429690140241d0005010b00c0c0003c010700080c0070400740e0300140c880603910040b20f00000040b5035680c0d16582034500c808045000f0b40300d26181c60900d0320080b003481500d4080c0300d4100f103100ca06110f4081c82e816140040d001d0b402c01000c0300c402c94040c0100441c1201c60345111000c11480000c00c014400203e09650f40c1e8458103451410070714400e40342480c40c41c0c1190440801e80010030803000b0080d80020301e804000a0944442010340d08001001744e41a02582c0004140020031811020b2280940241218100c2039207910078600740c044490b106c1e40c00401c606209510104150705904d072041c081e066080c1030303079485080c0028100400380d0849900c0c074405107410b0002507090b02c12008400103900f45640390240d0641c444225001c010001031040303440c0d0074280f90766683d0f100100e41c003a5000c0d1070309030f54000f81c001e00f6840300c440c1e1116038414442ca20000d26038800420400c802c4201c6007180003107003c6440811108030880d0b40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 473081582 1250 473080332 473080343
    0x20409020a1703091f0206070f0309050109030503160905151605030304050a031806090302131e050108010b0103090f02010804080c1002090a140f09101a1209030a0813 73
    0x204000741c04620300b0807414030324525601850b5901103103000c2190405180e2413880c40000e003030a00e0300360719800140703070f941040316824411000721841c03a044015105482005201c0d50034050074501f05500400518002e01e2141010540e020130780d001190b01c20210311502c1e6014a2070703c0d01c0700514040c0b500426203e10420002e0101c56555111300e4030f164407e0b42c1c1210b0755849180d07003e042c958080b40103e12000c0214070685040c1c81c10500130441c00003070001030311400085000050a1065900c000007018080b80920f0640802881ca14010002441405510350804d102c40c912503100344510080703075501110117a80e41704c0303a4004480000c4024400c03946048100300568a031a0704100820328110100030250365a1941c0c41400340c1d0802e45d80c041c81203016454095685a5114940c1d4211900140c42e005010368070b109120390300c01e603d070f4006003801c0c4907010b24074400c4807100e0090803081c403200e0000e5040e8031800c8409940b4840c20b83c0140008110201081c030520110b01e0034441c050050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 473082832 1250 473081582 473081599
    0x3081f0e063f160b0c010c080c0906180d051f090312020c0f030304060e0d0912140c1201020306041508061504090b0702010c080703020f04120203160b12061c02040902 73
    0x18201428a0550071403101300001266566205200340541b0b0080b196624210305181012152030149020310040c035440381c10007240b00f0b061400c078961520012200108042007070003c0e030030155101c0142029103c50f84070760106140c1290814042c0c0c251855043c0e654401c1990380d444200d00941059034401c4441c003c03000c02e5034280d80704201860185003d0140083c8031310080d400103180907440c01c1350070140300b030003501041004008220b00b208a500480e045881c02c19001a650426070181d600c1d0390b00104510901e1003c20056000d140b041400343d4040010400c00201401401c40900c103002040d4881000200e42e14844000000c3c0e00d40090408a44410141c1c1c99240000080300c0000061b0740d00d186540e1041d5100134165040580360400b107280000804012103940304502035526071300460320403003045440802544d20881c1d50302c8600850503845580c00c14040e80181040b40901c103007800812094a0b03d1201045070703070b500c000001545a22642480058106645c00340ea004a07030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 473084082 1250 473082832 473082853
    0x51c09080f0301031a0a1103040308040203120a0207061101111b010f05040f03030c031a04150b0c060601020610080706030902010e0910051e0d03081f0e063f 69
    0x64010b140070710b10600c1d01ca107010240b104452100100188842111810401c54884132542c04040301d820541500d00041d89940ba0300100349000752614140320307148400940001e81990106105040d201e29a5603ea03d1b8015141114261114803a1100c80c103241003001045519107044074089000100c800840c81d0304040f0700440845100301d41c1510060f400846942c10583c1c14407944400e140103040c02c00c0b0100402c0c24a04514031122001d60185a035030040d0342d0241c001001980003490301003181039494402040441d00e0700000d0700d00501500c01c12001c1340340f16880c03900d03000503110710707600404049180040450280029002c00e0303040c41003921080c0c541d40c513954244d03032250601d54581158a4075003818094010328038128045154010010002c090381c4100301c582c0d949070140742c2072041351190300544907001d00000d040d0f0740d4008500400101c104003000000c1c0314200c200c80080c58024100700c1207040c501140281852112000041d0f10702141007032500c1c1c50710702407400700d07a681e104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 473085332 1250 473084082 473084107
    0x60c05070e0c09100503040b0f15030109052103094605190b24030f0105010f090516030c02010b04020c010203150607050303011401052a0d051c0908 65
    0x419151201440000290f442e014200744007041d1000381c03240317843c0d4a1843c254841b428441c1019002900c100041c0300451035a01c280146d6498070307a0024003c21444a05181c6180d84101a6860402d0903032002022048030440a0a0300e02c0744107000060702c148141d25481004404104180d613001d121610080807800d04001f002c40362881701e0450101054070b00313062023480c000d048204a50401d01200c000c000142c0be200f12140c1009400f80f8501d025200340c0c11b0302152810b0b440507a50035125914070310681010540241307040300c0c007083c0400303016920b40c00128250b5004856014540d9000c036030001c4140d1003a401010700b50302c180700005003a40f003640090140d034014a4001620384d004024009aa140c039047c07480341000803500b542c03901e2035a51703601d500ca01052082c1d421102103000054040c1e4081c00840d6410384a0140e60001065081c0c281000426113000081080c03051900c0c521102e405902194a0321070590000c01d07010502094503009411090300880e0421014081e0804641d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 473086582 1250 473085332 473085359
    0xc050306131e0f2324040503520b04020307051002010c021b15030a0612060203011809020f0613030b0f04050d080601080109020c010b0a090b0325060c0507 68
    0x1e00c504045054003040d03502d0348038002c00004e0240010b4011490001c03501c0040c450294810040c440c049815070b070344d400c0c81e50642c05a042542d05003103a5040c024031001000030010b4101046600c0c41c00c1401d40005500b01d100c8003e40003c50302c00100040d0404a0f0000e00c035182d00620080444450907140c001182c500320a0824443c0580e459500c0d82d8980d80e01406402c80805524a25031160741c1d407480000d81c511010094459004000000700d12001000d40001001c2d1800f54030b1911803c4462030084000d40c801d1096002c0c01c10500c01c0c50000b85164051141895002070458004840110812442d44e0200001c000d203608081c800200040304001da951013400040a01642c0d03140601708075050110b501420410000010304001840ea0001502815a900d01d0320058907030380e4000308540103000b0001029405450f6000c00944501950480703500314005400f0380384500c1e0401403040b8804083d034000107241003180c00a0160900c1503802449460054045405599940c040900d104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 473087832 1250 473086582 473086613
    0x1213020d060c111e06042402040807060f051207031a1f080c0c030a05030403050f030f0106030b0d030210050a060f0f0806100e130203030f0a0504030c050306131e 71
    0x14803100c0f408480030420302c40c20080484160711640001c481d032185a03200d2000800c01410340d248126a054040141d100301c142c3c044450801315a60358940c18165a5400180b00c0d40e000143c41c104c11000e59880f03401a03540500c03100e90a04141e0b1510441500684112200c0e41c2d600b038422100001c165903202c03200c0c50140e07011094510340410760701000b441c0c50801400c000e0035407c200122440c001c1d0001c00c07260b00d0421454030644a848503d0100c1d00b03803144809100c08014044103110702e88444070706440c100d40f11914100a902c500300d0522071694030074800540540c100c141e64005d9080540c10132644410070040004205459590b100128819508840c8603103205000c140241082080b45640044840c40d051350404d00d00040540d5403a00281600d084c4e1311030ba80d000c400c41d10100103a840110044e0030030390315141e0b0b51100500a82081c44240d50f4011059000605400c0c0490403500072007004006000da08460f4031aa00401045160101030044288510011515407103002c10328 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 473089082 1250 473087832 473087837
    0xf080d0f0e010608010903050415120203010815071404030602030406091407080d05030121060e1c03150302090f130203060a0207030e040b220b0402040602160b1213020d060c 76
    0x1940005041c64215030302900040c04980c90709070080b0200e40c124056404544403010042c010401929040b143c1c45240d81f1100c91560008c0008102450b01044580448515802c01080350352140e400704c3c0c4140130f1070f15060036107804100034404148950011603000380240e00204000c1c3d80d5640f40741c20900400710241f51500146805c0c00004011f00002c8001105484e00900311b504042a100040c0803a0140401910700355084104114054109891240c0080141d4940c01c40b0403e42d100d0500c82c113960640000d03d132441800307110b074004000d88156034020f02024050707902c000c00c0010a410151501007003103508403414005075001c001040c800c8041120258a5810900e005082002d403102400d1259051030486010354079081d6a0100c2d010f0000c03800540c000c0c0c0c1d5592800103010401c20a6040b070300002d008907001350002041072a4070503c102c001d40041c0d407a01e605500e400344018413207840e11548045105403585143c2c00341c8a50000304a03a4040d0200d40c0c40e4011a503820300008007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 473090332 1250 473089082 473089091
    0x6064e070305070e01030c0e04020409050a0c0609050301020f03130c0306050405010f0b040203132a0e1008031e0a1b030e0915010806040203040c0807030602030a0506010306060c0f080d0f 82
    0x8202c414801d4600401d00c1900800c81541076075100b04014110340030300d8581e10040740000d01595038030703004121034641110a5400300461410305400d001018000d202c08503504c0134002500f402c1c144211405032001d0440d550a40d01c606090b2503c102d841907090350318a807048030110200f0860700c1244e0040b48500c000150328803072011404241d495211513948518810302c108420082c1d010407119840303030b01415801034039000d10b0030b051b50740c40b5654403110400780000380410f8a180701951180100b00b04281d044000c2c1d03503807001d035a42e4880c00c034190900c8424501c448100c02241c501601403802c0720f0034801c924103000c0c0ba040c0716500b050703d0103600290071400b44102d94100103008580110840040c2e60b19940c003000042c1917003d015150b00c3c041e90b0f0000024080c00110201e0f41e0280140801b03581e081b540d2404d0940c069042543c00c00c2e0a00d1900000c52120341c00384c85408111403041d01e4008215685486041c4520300480b000d80c1d0191007002542a403610724480c005007608490300c00907 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 473091582 1250 473090332 473090339
    0xd080702192108070b0c040810050a24032916030606030506061c1805060703050a090f03050a030f020a0c051603020a0e0702030903010203150306064e07 67
    0x200b45001e5110400b401c101c0c41240340d011a8014044414864206103990350b95200c03510b02008500c2181d10408440c0907034054200c07400f910703811860140640c00421f0210308506200b850030b25201d0714464081d40c68591040000035a0b200c40006040c9280b0240300c40c01c0c0c20203c0c00294420b04a480025200b000d9462031461034040c42a0030151045250030072140c03038240e021848901c5003548200001c40c0c260f0b0000c4036210690003ca10300010381c0c100c5626003415107805a500c40c0240d8550010900b00303400201402424410303200c0e155001030118403820690340301901d250b40000824020035403034907002483d03105240018244408280e0701c580c10a01941021401c005480e58444100c14a0903410005039803005012001d88550446c03d0140e034a9081003a440c5104840340a070701940003108024001402c104c5004034a0b50603411346180c0d55800c01084030301c102c0d80d120758070000700d2900466002c80600380b1245440c030001b0705401000841035003000d5034105071801e40815500144060 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 473092832 1250 473091582 473091599
    0x22060b04020a1707080c0a210204080705150a0509060a20100609060b041a130303260f16020c0d05070614160f020a0b03090a03030501050f0f0d08070219 67
    0x7180e20078240c0c41c5c10142814490f120000e00d1050040078010042a0410100303007440341125400c0c0d101c2c81250440d619580c41e9112030310307801d0500c2840d11030944c2049007841030203240e00316503040c940755403001d10388450407040040e242c01c919071807002c0142130580204200e140071020344400f96148000d0400c2006141c0c02c0c002e0320b200760000c0b5046c904007142044100700720702c00e50f000d90382070b01504076940042c5804001540280c540d1880c840320300207000001c0c0750700101c40070700b045000058061020306000541100c2203081d5002c0000828180004100a00807040d1150300b006030f20540e048460008005000c90040f1041030310b8a4101d20000c02c11386400040d210400048031281e203080095204881d90142003c4101134130f01c07040b00200400f1591030941c19400b40408825280d22810900140c507603d0320901021400b191800d400840c0525020300c481042400040c100c5030801b1130003007804000301070706004942500040c0310070340045c3d0742c15000d02c0070090401800d00710646041081c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 473094082 1250 473092832 473092877
    0x1b0d0e030c0303271f08070306120305070201111903080609060109182705030a03112b0612080706050c0702100e12030414090a0522060b04020a 63
    0x1603100e94400c004e0070303810f003204401c011100d80780301d4001004440e5030004581c1c09100050107000c1201408940d501513504021001d01403500355800b04100e6849000002950f00005005004202c0c240312105c0151303c900700300e010075100c68003a0ac0c6c9038400c0c40b12613403d1010090086004c910100d04005481c103122100951000f024a8101d20301441e01e0045088000140e40072100d554a0310031004d1004001450200c4460b194488440641d01c076050141c1c0700c3d0000141c950009040c240340740d01884c1c10606403240c0c0c0000b0900d5040b101c02402c95001c81d011903917032038403a145d159800000d161491615010585010303c1c80640c0d6441e846c0341403001c49100030b007001241c010601000f03015840b07003541c038050300186080c000c0d8020b41d082d00103940c40c251081404158880080c021401e00700f11080801c0e01201910030310191b880b040c03060400e895085484000e1082c01b110007040381103200d4022104030b03000d001c0000d21105020085026a4086052500403c03008500c0a50491a0b07404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 473095332 1250 473094082 473094103
    0x5040e03041a18090c07051005071d0112090c081e030319090506040501020c010c050910180b07061a01030e0a0b0709120606210302121b0d0e03 63
    0x50340c40e090900d0400c611000c054084800094000710310110070780d0b2040460581c085000380b03425500c0c94880041542540002c104032440e004580c1503045181803405550b018440d80d440d8071130b60310712501b86184040394503c07144d41000001c00d0300302200d11152246508103402040603136000f9007086840c2d490051010702212009800d44071400e2161004010359402a032145c046401c080700703441005000d004201000f800303900484d000e000820105600401e41d07000120002d000c0071140184c15200307030150130481500040c1c0969440782da20310400344501024240003102d020750351038191000b0260080ca00031074040d65a118040b0000c0e9400b980c03292540b10902c1c0501014204039000c0b5150751692100805440e02000421034043c02519040c6c05840808025003403614903051a00140c1541d07c00d162121109c1561600081d4001c0801300d40b4a405400825a140440c0b038810b0880d400070b008601000d5140505203a0f100052200310021015540e45606021031881058240740c0c940b036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 473096582 1250 473095332 473095361
    0x82e05010915080a020304020a181b030c08010e09030c0703031119020d0f060f0c0302030f060303090d260403140c01090503211209160b07030e0d030e03070801060504 73
    0x1c02c07a40c0082c0c1c0a401d59501c007255000c0540c0f644ca0b60300c04a00c802e4182d8100c11848801e900d82c00c0003001da42c2d4010b007550a40280082070712180001c1c16022111840500c41c0060014001800304031080f4002c41c2c0c0149005080700d25120f0030091190031720f10260806c4000519a20140c01c11810401070020b50120807109070005600e07036800598081c0090382d0081584075400c44810502c9256400b1600c4c090407150207001401490a005009600481b900507401e030003d00866000c0c20004280c452014001d4400b8003980102c3d110400c29100000b2007098100d070801c06211000da040b40540020b6110b040349040c40e00c0c00c000e02c642060038403d900d50411584c2001005141d50005100c1c1d001d61005030214206000300c41004040e03c1440185264215650240242c5050001c1c03030320045000c017481250b03042d480345a9845248280306c409000507a008040c0b04051401b098603d90341480783c00c1c4110307030901001c0401d00744507044d40031181d165501c9504201c0f9040078002c9491146002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 473097832 1250 473096582 473096609
    0xe0a060c1e0801061e02070915031a0403020c12010e0d032a0e2206120b0c0a0206040320060103080307030b0f100c1509050102030414010b010c03082e050109 69
    0x82c034020017003080245115050311201510042860082c0281000303408540f8040c003070844200e62a0100c00c90310304c0b0444036141032040816448180e0704019005a0341607002d000c119007580b08100c081c1508803900c884c5956902384940700a1403c00002c800d6140c0364034085070b140071011400000b01c04503012021117000159412007010ba0200380c82c0b101107000c4400c3c0d120007403008120324410384805030100d001c4e443d08102040e0801740b02c0c2d042901c0d074850480306070f4030360758180d580b103190045404d5400984d0205000c9000240a03039141740c202c9a040010411014903031001d54a042000c2e4400d0b40c602000100740043d1941c9409503094000040d01c250711081840c0000c01c1445100941e25410030100c40c00b00410020342009480d46c5580c2c1c0c503400d00586644e820014000c0d4000da4044800c0070380c11041c01c400e40410b008000916070142c450010300398454a0564000000505210005c0c004c0c2c1040d80003001c005514506080120b4550016282000005810a001070f007004007c80e01c40c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 473099082 1250 473097832 473097839
    0x61503060402030606060a020304050604080102090406060507081608071e0c050f1e0d0203030c0705011805090f0601050d020a0306030c0602030f0a1407080705010510170c01030e0a060c1e0801 84
    0x44e4040d0060700560344075980d940c0c1890304031b055020701d410055202100081c00518550150068600040102d4040203d140d80700015100c46c491030100130480c44040c0001c1c1c8100f44040700c0785400d24094140249080282d03561784003200c05a00400d00c003100c46000460511400c0007000d006040142c0340c0c0e1000703801540006482011070345600c0040c44c10b2010a00c03071505c03010b0b0590481031b07014040301c1c0ca450b4250b6201c0d8460b161400381c6400281c880c4002d0b100300b901e100d500c4045820180200c2100c2d02d415160111440c00105034506100f402c01628140790714520007808445000d5400140d081d0440c07800c5000d006444d400001103500503c02c243c3c182c19000225401d07000b0318104081c240030086240c0d00c160040c14005061400c0200d091014044190840c4e0300c40d15056020105140d1034000c0c80b070003c0c01c000c0241c032082e88000c440c15000d5001c0e0781f02c6c0070b2442185c000c6a01c1c0782800d658450980b080e150241d40050902184030200b28400703052510f46e41e01e41c0c00e10b40e40380c0d0306 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 473100332 1250 473099082 473099089
    0x1b03030702060d0914210c1e1b03010902060909130804141f02061f08030d060618140112090501052d01081507031e02030714070b06011817061503060402 67
    0x110706c0395131107003100024500150040030020300c15800040b21a1900c2c1301e4880400e41e8451590720b180c440316011240400320030340707410f20511181590080803907040801c2101030000108008080c00603001e0405482801300b0010780c094070082c82418000080c0158803018085581d082c0030701c0c00c0043c80480a00d42d40e040d00460300d1544001044622000c40b1139011800446072050340c840383d024007000546400150041d0001c0c01501c100c1d403140c556204001c0d54820f004081840ba80d00d03403846240341d56501d5807040c042c1c080214100000803500e0941c586440342110b0065810801c0710244420291080c800e5540c64a048040040c2c8010250726091586032070390315600715001c4080c035403800200098082d621002504603201940c18000ca003c000c0c40e0300a5009a644102154194040c0c0241d49400c40898001d107034046c842541e02d480304001904d0321028808000c21079400f0080102c0c60b14890f070302207107551010000800c1e10b8141580c900d10400f900d40340c9140a41c00801c04c103c0980c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 473101582 1250 473100332 473100373
    0xa120207090228050d090305190509010f03020c282901210807060501030203060109060f09020d06081614271503010603050a2001021b03030702060d0914 67
    0x380301c03040c0c0043c0c150344094202c0362071017031070f4810021900d896040400d240d40700300504902c4407660b81d94100b01080c44402d032803c2c084c0305070b02800181d91103003070303240c1c24404d40142c080f5403400c80445961620302c90554a0310359000c0008040c540e0485e0044061104404010001100c0801d0210303250420141161040d0300500400000c1d981240900c0111010382e105003016079040000c0c2c680390f03040c1d07283c14006880c0031b1000340e11a11448001003543c7c1114030841d401c42e514214284d51240c82c00903c030340607402012a028500750354140c000760128051004082c5040302c204102e80c041d082400b18924020348089450181c10703010010104441c0038200e44825100055800310103a440b8a2039181d003002c01450f064041d42031441c004100080090140181e500c0ba0342106948001c54480d08250341d81c010103a07006a201503080c0d828010b1890b074071624840c001d419286000103c2e000b080107540b28080041d00180d031984070740300344000f00d0040d16100064070041e00c0b503010300c8041004030300c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 473102832 1250 473101582 473101627
    0x7090b03070c0602040305030d06090e0318030c0619110102090901120c0503031309112b02041d010501030b090603060a021b0105040303141806010b1b0a1202070902 72
    0x1a000400304441d14000d200d41031525501c0202075640c3c0d0740320720b4010f46a800000303505c05441d0174007202203038410090207500540c4420400842c101a40703850340d00c1d0100b01110700683c02d0301460510140540300c04000b0f000500da0844005444044100c0091243c866030410503c5039105000d030040341e80d2481051811103035812a80925803010707081c034a01c43d02c410380c0030a900d0722000584100004414086104a480d2842e041081c5044416054800d1040c40540003d01e807514480e101400c102610080c2c888218010041c18a51541081d0102400c060701c0308805840c2d00b00104210340c1d16000d101c00c0030100762a982807608110011a03612503001d45440440c6401041580c201c181d40d110151104490a00901490030300c3c0c240074009140b0601c42c11450b040490015003400d51110001801d443d00710b00a106580c0381810410203600940c000300350000b000c20f945203010b0f50401450b444c1601408240079448242d0750040d103030460603809a40c400d4014001a8941181d000000201 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 473104082 1250 473102832 473102849
    0x31403040c0902090f1002010e0d0908070302091906090605130c020706141c09020f0d0f0308040816031106091b0f0103060302091305010606030b091504150602010f140709 75
    0x21101004c00150304084000d0016820014410501d1410b03036054010300f2a4402060030385400d1014140f00311a4002c0e41d000c0e1a803580d20403941000141802103d0950140c0c2d440794941c0101c16010300a000d40f04ca56001800300341e01e0b04400c0c40103207804030184c03080c15885901005000394884010352141018400d500600c0250300c5440a44083e4a0445c0c01081040d0840e411111a44104c0340c0204104c0394207038002e60401c1f00001490504041071030505410040400f0841d41c0c80e5011030301b6140c020411610414188004c07103941e014001403e40d150302c46d894a042c0c01c03100d09140d600e4050300a001c040180d2100c40c80c0d00c0c00409076802c0590000c000c2d24a550240c183d000140c020b05980e45c070080d00007689108000e100140007851010203441031000303003c140ea0b10306084080d94110300310181e0041124020030501c2084010780c2d241440050008521201c00b60000f00480000d0b510000143c1d4403003000303d0400500d8421080c2c0e654018840d4642414003101c014100324940c0a9141d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 473105332 1250 473104082 473104087
    0x604060e0304050604060909180b0a0b010507080f07110307050f0d060e0607020616020303040b010603050a0e0f01020c0f070b030622090804080c0d0803060d0305040305010c0c031403040c0902 84
    0xd440c0c60510480b00a40005403080359981c4d910031005010740c0c00c0e032190f400c020b487d05035080829003500f03081a8a0a8020500d0b41150b101d072030071500100420080c56050100c1005103000003180c800252504d0303000c01d0491a11000907082c488416a8180e1a00e0300c0703500810350901066680c44156000c851007500d062541043e203180550041c08018030500c10f600ca08804c000e2070079400030b01036200d045028406801c540c4000340031f84c1d4034001540c0041000c04031030300521006101f680265030248201c0d5001c51189000c10140303082c50220f0002004694000540741800780c01004503640d40741f1610020007113181741c0ba064040601014040c20b01c10b04640510b1241411780700f035280072a02d0f94640800440003cce00d80040160b01500c03580c201801885100703030700c502c1c141e4078810645410001e124515500d4004025214600440813801d00209000101c0400c0003446520f13aa00119111007a0711000340c10058461000e080920120703582c00c004000024420007407038001c80745510030158 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 473106582 1250 473105332 473105351
    0x8090709020d090b2d0114300d0e0a080d08090708010513060e06060f01050c0f12030906062d011e0906091703040b0315060f0c0c1002060406 62
    0x802801c2d1191021348500209030622050803001044501c50495407490401c2c903c00142800c00345c28802d1183ca00303410720303a003d5800d0034200300310210490001c500c0307201c44904521211031046a00a88203450079846101c842c440789400000c050890007040702c5500c001c81c44c1c00641541c03950608400420840d2010100d01c0b0311004021640c041c0c401c0390700a01c510310b0f00d0902c42400700411074050307860b60b0a000303030680248404035045018a1004e1303c80d03000250000c005603400e030300040780c01a40d40320b00c1c01c1c20030700c00e03030213011101200348040038682e52803c1540b0140e280020180040d80b081c5110318071010901040704000c83d045d10b10404080090700c410005895000c0080104130800b02d08546883c003055000c02190145d030801d448544000f51504070382c070942c003040c50908480741d100f0042845060f9140020710780c000c9000f000010115000d4011031025048540e01d540c85000104501c003038108107210001c0d5200d01910482428a0710860007581d85101600103001c041c1e5460441 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 473107832 1250 473106582 473106607
    0x1008030c1002091903050a02010e10084c0812030f0907030b130209010e01050f151e070c0911030f04031707050405011701080a0b070c0f0b04060c0809070902 69
    0x20203c84080f20b0482082d0b45ea0303818044c0d15200007901c224001a800f441100141c80d040d17078410701c03103142aa15584140c2c0c1c4c07046056040c04521424403964000703c03074043c005070f130b490100505481042c2c920043c008030060100000c8510b82e0400d144c2d540042e1401d5071034440d403806807030384400e4010900b0f21548a4210280c01e0241580029100c034420404114030740741d00748822290184242d940c2125030381e988050356074204080c050154407003103611030190075150106020801d94049405c8a251218540300340300c4611403600480d2004030b02080c40800c1c04201c0c0220340040044410a0040c000001440707840351000800d0712800b07038211400f050601d8400c200044070b514140302448894104142c000d1708681043c411140090800300c002000c081c46000440e0480e0720b10360007806140000d981d41c8003000c100070302003001c00c50300341072070000f240002201d0b140d00c9008402802e12400c0038142041903c135007480e05401d01000c0c3c1d0a00840000c0000c2c0c400842e00c0749800180c0351080301541 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 473109082 1250 473107832 473107849
    0x41e0f0c09060501180f0603020705011506110601060e03060a0f0902030111030105030d050f0d0914030304061a1e1302070f060c0221030103030807051902061008030c100209 76
    0xd051030a1003000820341920680c0514180e64098032804007804d0700381c00a07a001007480c0540100400f0307450040002600036000b9001c400c0c0f00c0d1001086e0807001005262003c0101e901c10700000303018036602d199000b0b0622945014107c00e180c1402d020481c00c0109a072040040c003606440c1e82c4d1400f07180c0d0306149a51085120f0fa0f4000c1c024001690140240009030304207009032031080c020120b003050703054060021910381120031160541070032845504035005041126041c0e842c04046032440c0c554910900007103126a200741000502c1008805c100c102070b9190768030180c0502005140252040f00030807000d401c000302210f03003401c2c2c40098107000d0080d000d07201000b4511b64420071140100100c540041e49160050f5085404568880c0403580304610510b5141d240c4420030001403021070f100307110007540b00700d0508044d4070b49111001080440c1d0078401020005070080014000c0f81c29544032031800400004008500341502560f52681303031250f40002d2000140c1c002181d16649c1c494224 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 473110332 1250 473109082 473109113
    0x507030915030504140708070902070c051003050405072319082b08040f0807020312030c190e0105270a0602031801080112032607200303041e 62
    0x2204510085050809005804203843c105e0750030100c1c101c4120001c0001401000700e40c404801422118a0151440c00940c811042600c013944001000304c0d60b900c8294101c0d036031001030350b800103443c80c1500b0b200e07042441c2c503042520303071030284d0140b00c0360460450050000200e04031481ea85103040880329003082680303603100384914001d1900005694481010803201890030640c2c1400100c0d0564080f0360714a81150010f08065040000c00041104a000b401000c0d00c0601104c81c92280c42c41a594107400480381d03200c1d440c01c001030408620a4074420101980160304011840d1840000041c1c481d010380341c02d0110800e059820f2900d000c2200500c0c0c1803150b00500140040c45d101c020003902d80c1d00c40300c101070347c4150032049011154445c1a559040328502081d40254030615034044600e0b10b04840301400e07a031409400001401d00f0390f00c0030790007040603490740340e03041d041340152082010584091003c0c03034000b4010000420642010600c050b800a00011142c0382c2c1441c00200650349941c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 473111582 1250 473110332 473110349
    0x6090105010c1211072603161b0f0909050d2313030b09030703020d140a030e010f32041101081017030301051518101b050607080c0c06040305070309 65
    0x4000080b507a10240d00003090466400c5546d40700005001e03256a039108210000202c880d41039800700200e94000b0445454402d0740402d0494280d0f10b44071154224a541c01041c0c0c180d03920b0015104108040010541c0715502d0300748018800119620180c051030a940e64008020000501c40551150001ca120140d90310501845040c100a140e0540d650404401200548500c2004000c801d000b00700b2802021080611149080880c10044002c0c10200524031029034072000040c501705064054035480303018954541c2514032400d0380782d0203d010800140180d040080090101013184001d140003404020b0820003040d8486524600c402c40c45980098012450320950a01e000c201000660481c1c0c0300715840200c1c40f010204840d070354800d03110051040d100ea8128200700d82490b0040d82c100b00113038104081ca40c031340600d0a042070b000041d000c461640000303081000365500300721003c0d009846444803504052500860716695500035001409010002c15101c003014070516818007c2c00c20807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 473112832 1250 473111582 473111593
    0x4050306040b10050d0b0402010c06060e1501090911030109020702120a050609010c0f02060a050703021606140705090d030507050102090a09092102071809020d05100506090105010c1211 81
    0x103040080d400a4107880202c05111120700024051410000181d0290f0300046e00454540702d90340113456480d88443c08903000381e124500050000303292190203106400d01910080310900c40c9000510051f6690040300c02c06180c40d90030151001d1a0b004d07203041d910800001a07845841e40000b030742c529440e003074030303004c500c20341c00355404110740401c119000700c03214002070000010040c000d6a40b002c01c4030f1200c0c0180d00c88400100d000346950002e0f0741209050400529021044c4482840590f0b41d00e0203651140c0c0300c12514034080e4100300705981c0700f049894001d05004030800012113a528202c0c014003081400b254800034450298102d582e141d1004003a10701d240d0780c590a0602030300c4001e02c02e4420348032141e119051418240000c80000d02d841c3c4c0a01042e07418419a00303840c0300e41a443e481015500c400340d000680b1003000c5413451340c3c000c40040c25110b4080c4c107000c0549100402c03080c01a03e100c070041100742d030000203041d00154007003d00065141300c0541190158040c840298240c4a40c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 473114082 1250 473112832 473112841
    0x20c010203010611010f02120f06150d090507050607020105070b1e010e0603010e0109020105191107030c0e090c0d0b0c12160f02030909161202030c0a1e200304050306 73
    0x2c42e10112580951078024086c00c00071218038012800703400b80c1000e8141401000032007415848102c0d550052000301015022044007103215101d410100b900400e1a540718441418400c042008000501e4121402c1c2e103002c50760380c0024a54014075a009202120b0725001c01c000c03039000b10310b05c8a07a186d000d8030748030150ba448841c0100c040090315500c0c029407030f00050084001060040003920361301070316502c4c94200c010202e85000d440068644080000280c900100c81c1c206004a030011400380c206900070501b4880480b06401001d4140945039214010118550302c85081e05200103411a6a4000d42ea8860111541e80d20401c0e0010310307501802c404001c801010485003070302c0c034a06075031140401c16000b0016681c0348103008049070b0041d071b40c42c0004d18002e01c68020295021851800280c42103581c40c0e5107060341c1040d940a81c0c01240865007989103644081d0800700b4541212142e0071880030594003900a20425500d10a0603940800261741d084041040313400610001c1c0860b071f0685030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 473115332 1250 473114082 473114087
    0x30703020a0b0a200c0a0e0f0402061303080c0106050405010e0129090d0b0a0b0a030b0c03091f050603161d0a180609021908070b0307030f05070507061d03091201020c0102030106 78
    0x124001701501c00c22081c1c10214840045101c260f00c608503075540350300b40d91110313001c000c40d907040b1440c00e40700c22311034290200c0055145000380c00d030980a0750010415904100810058030b005030810400e280a10004000c6c2e55a601210142e10a286403d00b0b8100f00c030481503100b40c030400321419080303105aa418020805580d540d14458002c1c030b50200110409801084170114030740c40060300c1d6200901c00306504601410003982c116803100f040f500c009503d242c0140351002011000408660f449040100134201030011403031220208021410346401c02941c92444c000365141c0151000d090b60000b100004075912401c0402012501100d8402943c50107801804031031108070300502d040f56040c030b406920f42908009642c0e1001c080c0c0342090030300b001040c0e16003004109800b00740d218001518018042c0c0704d102e01960b501c0d0307200f42e83d440031410404181c41140001c0c5440c2950001c0c00c0c0000302c0c0c0401031751066081112141c0360500030981c0a8068000c1d82c807411503651000000250341074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 473116582 1250 473115332 473115343
    0x1506020303040c270b0a12080a0f1404120201021501140f03190b0703140f15100906110708070b21060a0306091a01030818030703020a0b0a20 62
    0x307202e826076644480d242e01c44c0680a00c203144e003555580b1142002100c0c1c1030f860f60003111982c540980240360b156900c004800c54944801c030300b03031030001e0000b608040e075550000214420070400d040004000d0003081a81100d03200d14410a581000c24282d042c0c01c5a200740900920502000703160600c82d61070fa11030180448034080f620384180d1502c0388070044c41c180829a40e03a1121030f51a0f03c0c0d601001511034540212004010361b042540d1012504001b106107880035024018490f40c04050346800c10040c1503031410303112a14854101c4804451089600c40707c0e145c00d6984514000e0307200c08508400d14a80410b6801c04112400f0700000800c502000d030000d0803054158100400d0f2a4a4891501554140a44007a07070081040402440840d903990003072400d40e031151540c40e0240031440010b08480c2003c2e08100c40000002998045213122501c05240c0d01c101240a07040c040c0c55030740004d01e0b4070107611800e0010132010500500707140c0039164a500199031000702c1c2d26041d07109940a42c684 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 473117832 1250 473116582 473116591
    0x1e12050c0c0a0b0409050705040b070b01060917070302060901030b03101a091506130e04060f06080c0306130f02031510090c0c030c020316180c05070f12031506020303 73
    0x34401c02202035000d180600040c1c0480300d01e095078038589800e007250f880140c0801400710b02402010000002c150081e2002092201d000700d07080c000c0d950420320010400d11096010301d003c007518442c814041100440d090b000c40c1da0440c1d00a6070b0f41d0030350b001600078028550310310b0791600030911880d4442210b60041c6c400d01429070907009a02641808211114100780c0d443c2c1300d84010711404482c2030426100903c0c402503070b4800c018102d5130300d4940301c00405c2e04550854803141c40c0c03520700710503d01500030100680703c1c100280072042c45070b07030219648240042072280c0c005501300303542c0b0a204101c51419051600a400c1c4c4030640c03a8070b4605441441d0540b105c442d43e2035020000034107020f081c4501340d41d100032665590007560403524122032540740240149d0741400f801814203900c0c2c031440c3d6400001c10003034010740c9080403010a040215083c04e64138506000c41080104000f48209900030701059100b84c003441d01381c406081c1100103201ca0b0404460382c0240f04404907a03150000080c5204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 473119082 1250 473117832 473117857
    0x51618050a0801060302090f04150504050a06060902120a0c1706120a03051809010609050105132301030e010b01051c09020a0b0d180201020c04020a02100501030602040f0f050901031e1205 82
    0x100d4407840d1102c0f03695441120f0141c500340100d41809403003102b5411864000340143c04540303102d021511207108451659100d03c0b4010384c0041d107142010300d55011185d0003e9114001c114910585070080e01f0403030000300202c2e41d0350000d00084c90f43e40d0780395490b115019610048580d02641898040c000364007602400e203c4d8044a80c0ca10007525089900e14183c4411399203c0d40c00f03518050066480750080c00001c20840190800400e084624422103c00000c962a00140c403d13001d00003d01244c00c11220b40020740d0411040d059079980080440e60400d4240c078000640c1c110855000004182407072000f513000202040006546034440080e0100001d03a403420020041c80703100007a0145100d40703009025070000942680c00385855405080400d8860040d149500641c3c80e0340380c11640241c000701c4400e5400324040c01491100c00c1c018010b07204000c00d803680503040100080f00c2c0007052200038044140c100c0301e601400c140204d01004e20b42d01104100310094002c0d00a4180d0300100c01200c031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 473120332 1250 473119082 473119099
    0x20409051b04140409060e1516030908030115050d02070302010209010e1c030e0607050f0304150503010602100c1b0f061b05070204180c0e0103030f03051618050a0801060302 76
    0x12400e10007411902152040501205244188402e21000c0c040100c01a1086561a0a800104c5c0300500000080d00395140a111306813510707035200c5220390500340003c1c041501d41004000029143c40460341510030700c904810036200080c204603a036204000c40c00402c9030011601408240c0c054010380021402603c07074400a03110181072004040790350764503084681100210750046401a5846000101d0181c101403400740240c9803e460403502200c0580b180c1e02c00581007103c0f0001e250081003050152400618651510394020b50702c1058a81c10030401d03903210b024030f540c68091042007041c1c00b500014000407023003501780a2404611a4010b890440c03d21b040d1003801c040a8032900c2c807402294580034180751f826000d01004042c001000c441680504c1615004100c01449203c02404a407400c5840c070b41c11071600411102480f0840c0742414108024420000441030141e8503280143c039203000b440718204a48080e045950f400707281c0180c002c800c080343c81d001c1074000b502a00c1c001e48102e40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 473121582 1250 473120332 473120371
    0xa0f0c15030b0f0d06020903010603030806030105060a23061c0c030f02130e04022103030a1a010504032004020f1e1e0307050903030a080906090a05030f0d0f02040905 73
    0x5003580c0074200c81540c0701a66650740a1a40360a0240c13641c0c09000e0038005061040c00c10210f400c66041ba003055010901010410003646024000d9680c00348003038a441104c1c0c2d10340b1a62040000402207545440d010240c0c401c403981e00c45e4001d403405461013500e41d00907800ad0081e074030010a041c0ba50140042d041c16117082e22a90b0a00842d03e031450402c0c50026000d2a04070401102c0602800882e07110082592091f03039290034408410052000341e010790303620f04050310424200c814400f0903c80b0b0a8800d55040c0d180d81c3c000040e5001c40343c1003c0e2101c030717401c0000521503650030b00c5070312a54014404240c01c1080700400000e008000300c0000e5840c00c103120895840002e02442c501610300300b00440c0b034144082c83d81c1c000b13141c0210141c2420740c24000c0d00c80000341541c0012100100003080c003401c0040b1500100702c215000b42040010b041c1e80070303035070b15003c0d01c03807091810800c811240000e2034464041c080d030042011800c422000c41d1503c0d10b4010000c007920096515002810002034082d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 473122832 1250 473121582 473121587
    0x30a0e0d0804110607020102100c020102031f050f04050a02091e0316050901120c0b0406080a140f0f13020a080f1c050405090a0603080309011506030e060103060b030a0f0c15 76
    0x750107250000031401e03980c070b10041001169403001c88128114040c41004050454090043d1805000b042d0005a10391614055120040c0c013951110140ba00314114104203603101e082014002040644001c5030558564500d4400391040c44040b68201c08000c0b404c10341c980c11a03954000300d40701281916171074002100031042c02f0310346010300e95100781e50000421812480c1c1c1092079034507121b00070082e20135648481c00381c0d039a0459400b000208150384c00b0002c09070002d10407040303e0710300302e600000c1354104a4003a144001d00205520741c000c00c1000458100e80034500c0340c09055030b00820422f0ba070754440d07201d16103642082c2c580c502544180000d40c10400504503500c81c0c2d220040c1e0354642454034100c00c000700f022001d04120b001a58074403020010a007088021440360007054000b00d032044e01011100701140265010800f0180740240e03039501154040307030040c11a40c0014012410010180003e8242040100e00620904411401e1006c0100309040d880440d6404a900d0403c2080320001703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 473124082 1250 473122832 473122847
    0x9041a06040b090f090a08031005010f0c05030307030905070513021210030201050a0f030b04092906060d0e073809060403061d0706090302090a11091212030a0e0d 71
    0x850344031031844000313040c40c0000e2928540c015086000c0f2000001191a1009542d105841510501200d40000d10040d6001110709014200900e8115100c0e01a6142c2e03d13240e000c082c0264081548a400b0386050210401603080a002d000b005401c42000000c5050002d50014510000032080000010075110b5400c1d4503100700c03901038448500c0c0080d0f0304011104440c0d54403c48090603078468000100340c80794401d1846036881800e519090b050b96500800e00240b051091410030a2810200b00140d00c50702c0684040000c26080800d0341d42e600b02c0f41a00300041030b003114001100090003035031040440e80d4042c200c00030400f44101d0314200b920300b4592905c1011403040c1c200c10100803c200040c0f00e5032204c00709008200c3c3c8504bc07480f49286582c10900641d00100018180600c2030041d49003007002145c02c000548801c0024104403204001035004002486100381c9803e4a1090427035011310042c1106462584403603900d241c11a0404000d01c07941c880d41c1440c0c031030107600840340d5004044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 473125332 1250 473124082 473124101
    0x90312060609130204141905220e01050f1f0f15090b030c130e0103020d030c02121606090801090f020f1c08070303050109090201170c0702060304060c030c140d09060b09041a0604 78
    0x1c1c0d10340380300640306000c003809e17124400c0850b003c1c0c0d00c0d0540c003c2c4110a105807409410180358910444c201075850103604e5085c42521050400e0b10102003110000c5100303000e0440364821100c030500502a0415076040050b0740c0548001840001040341418605004110303d900085400c40c000d5161495911070000901000790044500f40b6042c02082c002d0114210f010300c014684035186c601043c0d500d042440d6903208114552500d103050010035004098031024090780c0000708030601903600e03160200b0000b02e0010340209a032211000c2c540e1a0220440200c014010105841d07035683d282c8108035030700814083d8000391500002040004140c06081c0c94903030140d4400b2082102030b0302072883c0c0c546c05010340190000401812005072a403034082c501c81c90095078005545481058058195040c81110f601009140350501d140301c14058260b0b0122242c20000040c482c0309480e1800042c030b06040450752140501e0200402c100540414104c0203400b4007120030682c84080a0000341d4a2095 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 473126582 1250 473125332 473125339
    0x712051203160e060702130903030c022d0f070602030d05010501081302120f010c020c041b120c03060909050a0c0902040b040504090813060f08090312060609130204141905 75
    0x1c0d80401c0b89031148140842200e402040eaa01e40155540050700f0420f888051540d02511079031a07005068140c4150703040d070200d50001e01070720502c1d10140310601d1000c00a0f201d450050018040070418104031045619041074112020140c55083c040c0d5240c00c031411540e01c23075080500120362035200d074a0700c90050401d4551041040801d03405c00c990f01c3d08000000e6420301c6180841c0b03685ca03409020f0b40ca424140c40d009065421140010310041d982000d400c1000e1621900d280c18526510150809200c07945d00d20000d04251100e0b411400742c58140d1042c02e16034105402d81c1c4c140800480e101110b2446000f40c0c400c0b15035144680416030081e8460104403010601c8200541c0c28035400081c0e4480c400d407001840c0035515a40c01460304000c0d004440003605070b04d40120136540281d90143c0159140f8000c504208400d4121001d50700f0050085024202c0440c40d6070450300e5583d180c4c1c0481e0007211065440346d0710340c01402c40040c4215851881911141c10744a008040c2c19800c2050f00c0c0040c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 473127832 1250 473126582 473126611
    0x30c09020a080c0c121615090302030a08090a02031626190804033e09041106090907080a0605010c02060702010c08070803151002060f01031104020c0712051203 70
    0x2030241108a4000902c004c9090140801190b000b8401c80000c041201c114440c0d03c020015504040208420780c0c1042d1f00828034000070301d07020903000015140000c0441c504284941c0d03d8040702c03828100307230603002505031107005000d0f002c1207044102e00003500c44d030030040c0800d031403c41502c10020918603143d08840d0401c5441d084e244060126400f00070b03000380d005902c0c01e55070359034400c0650340302410b110441075041c580136202440c208854169604031004c80c840301c100c41001407101e0001034801007641080d00c141d05410345032203060f40c4035010014149003091034801406061000301f2a071201156203009004200e540c015a809442540c024080509198080d0300641e00124462010341c4c0d200424408507002a080d080250700c200d00c0c0442401002180000780043c1c4407030746158a05541005082140b610701e000c1c4580e0460f6004180d05502420300b1000c00c0081c480d404400c83c036800b13500760100781e0700500398018500c50700c81d0045850703200800382c40390b001c3c0c04140d4104030003020b403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 473129082 1250 473127832 473127841
    0x60705180d1511160c0504050c0a08340201050601110d0801031203150906030c0902030906060d0219030506010f1509060509040b0d03080402040b03070b041a120f01030c09020a08 78
    0x994000c000e10803002c61520f240c003c110400613550502c02c2402c40d00040c030341d00300344410b081c14001c40fa004401d40140c182800c1e280300024103010002000c036610390f1300300f004840c6216040211401c4004510b200701007410905d03400240070301801c0320710728046101000710881d03d03d80050300c90031404c1c05640e030440c0360f420b558444000c084100c6a030781c1090380b1079a8604141c10750706100401005001ca001076510b03d14980020700c0301c81a405203ca0500c140108003111a000c14280d6000d20202d0742d00d00c8a10341707440000c4e03000e031441100b62000c86510002204000d000241075046e5001010118055980c9166592111100881c0c4000141408030700b00000ca018a0280c081b82c0c400a1011450300c0800740031071400c01e00e10205a00041e0940248429414a80b061510010055014104060800030b41c40010702c550710403603200e482c03940342286142002606803502030b1000d940038040c0f410460044400d52000f80415514580c9a44000800c64124402c80e8000400c40e1640f81c2070341da5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 473130332 1250 473129082 473129123
    0x610050f070515010f030302120304021806010207271d070302190b0f2a210c06010b0405030f0a0b060907050c0d051309061d040212060705180d 63
    0x3800c1c2110144940d24403114070140203021540a01141048406154603604000703181c1040400814a268001c000b44009a160802440103414440c2800b80c6243ca582004034079010003980715659805070a0f2881d0410004194403074410700f0140c0051115003000500070010058000d0b814030300341c0c0050020001070800d1801c0c807400107410900c4810156603566900455809400d000394406400203041c0d034030301c2d1280340315861407402003000c03001c040000301c034169150320f150a41300340c00080c0090201182c20800c2296030040c024001d45200d565180d2001c4040c1d000707401181d01c28061113860807921040050b10380501c0e034026240c50314035110b1100f88000000040c220780c080000402c44d800429a0401c211500f02626560b0076544054140644140c0603094002140e0a4100201048403020b0b0340c03c3d20306e4200440041d0442c0340c0f41d510000c4c0ca401c41c0c0703480e800420300900c000c2000307461300301016007560b644103c040c1040c01c903440b0070880200c10081c8018a0441622080b106820 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 473131582 1250 473130332 473130337
    0x250e1002070e0a2d0207021e090a050901110705030403060b09040510090f020315040b091b06090316180b101b0c080f030c01140118020a05070b01120b0610050f 70
    0x3045609190400342c95204a0004813081c1c1250410a41c0014451003141480f001c1c401c11001e605030030f414014a40800141c0329039001d0415003503030b0344a00100348210340a5008038010113681407440c3d0b0340e861515040c0c7d147c0d0482d11058401500d0300c20040d40c98241040703940d11a80c0e0050140060f44038810200d402040d0b451010754217010210b042a005880070410f186030309050440034503841c640391503c10001d5900900d01400d9030007200046000a2443c00c0403468420b089659688807a800d0f400710749400d1b001c030998554402010380020b20500311060a21041000c060180a410421420302030700501400701c3c58001184200c400c07501d1304483c13501301075547c89548820021a51030610038984041800b00040603003000450b03070f5140d41c0034450a01c058148015a100f15072402650045495803c121125520380016441560600c40c004a43c20a0340c08000f04641f540c42e11140d40041007501c0f01218001c2071107010072101d00e0086030180d81c0040d1952407910b4a6155203c034140c5e034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 473132832 1250 473131582 473131601
    0x40c171c02161d1b12060d0206120f0114060f0d0e0106080c0f04150605070303020706060905040204150b04170c0406080102120f06060f03250e1002070e0a 68
    0x6002d2031010140300056103516100414000e4003040da07207002452038014001d00503249100000301a40d803400740d0200d1609a821034480c1e441c401c2074541c0c2d50b40c04141800c9840c00001c0d40a0400a143ca030480381000c1164040e134040c04254165a80b1114040000e0900001d0154005401c2c008290021041d01c0182084503440c4000b1411808599985081d90308507000044035401114500045081010700c0c040705c054119820f0007010400b0803801c00c0b06480d8001c40040100014040c400c0c14084d40459102940c0001c0c204003840d90f0b210713140d009000644080f4400e90a2000c44010003003508104000d6130813030710141740f4241c504207a0010001d6140240c4040d070048540c03054195540340718030360080600b07a001595a0f80c0c110300ca041800070003000009603400800030b01c403c68680714180e52104c0c48004089980380c44200c80d04102d96002812400b284102e44848082540d2212081101c81010741c1e000310560304140e002d90b206c1d03485008a801c207200700e6000660080594116040d00c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 473134082 1250 473132832 473132837
    0x2d06030a1205090f0a050a0e06030a05100b0f01050c070605030702010e0a1a060a030f02130e0a150501290d020c1b091003120e120d0206040c171c 64
    0x340388096807214a09004040c044001c18004030b0b1800c050300f0f06400d810003010b81200c007022041d040400045e01d40209010394540400c07080d0004010f074508020700300100390070808403074003041486004006402c84904650007808a400c2031907555000b501510420b841e4000a40b00740d50420b40f0841f40d41c0c0009210100310343d00c41c86261082c040521042c2201402062210790400700505035000c07006010b801c0e180250400c01080003c03520305606a64895070441e1140c41c40e15020145102404c80007403a008540606070200e0308020103a26140c03500076840c00c080c0100e03aa50b60310440003825003004c5440c411300380c4026130151000c04004014014100c00d005040801440c112450082a40c0581c0710f803401d45d00a02909241c850f02e6036a0201102e41040745081c156502c013040d0303076404e84544080c0802518040c1960340c50f000005c0c80404002c04403182200101002940c070207041d102900c2c044040c0d00c02152106c1c081d4a0b5840d04c0907010001d200e0307444000794141084141b114400b08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 473135332 1250 473134082 473134093
    0x90411130209030f030708030408030408040906080f0f0705010e09091c08010f08010507272705090703050309060c100c0903051c080a0e030d05130b2d0603 68
    0x200356201200268014002200140c40b501802c0a26161031410603400080794400d0000740000340c03900045030f03030103527001082300c2d02c4e034030740303240c081000e0040d074018940039801c02c4404124505c002480c0d10440b61580b00701e03030300c0382c0d103560685860b03003203500600c0d0005106c0703810b02005040031110503030080c849208483d0b09419a006076002c80040001d440300041140004014258540e00414080c05030803000700701310f04243e10701908006451101111140403403040f00440190204408000e004090310013a403a80140d4800003111900301d5a0440d107840e10b00401c6881800142000c1a030f1341c06001540740111030810001940c0000c40c0d4014a445980183c44283c00e2a02031384074801d03042c2d10780e10700c100e0440c502a410001d044042c64004500003005100d800d40c88800e26400c4030008600180703c0007440412800c600c5402c552100c428241400e10464920040300059550f0145030090042d80741c000e035100846100150000d040c4480100503c09020b001440b2904a08010304484 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 473136582 1250 473135332 473135363
    0x10507050114040302100c0203041208070b01080304170f19020d06061202040c051306030b010c0f0f0b0106081e0a0b09040615090c02100e0a08040312140c0a020904 72
    0x81c01d44290505030190880000d0a200070190100110001504c21085c2482001d40340e0030025500c0c003ca1040064800c40c4e100703003006001004007101d4955811610900301907031220040c036038a134814414044001100b035000c801074000494065500400040136003407200c007508062072414030600c826640090542130080c000780c403138402c10b0006c090440070118800f0250040008072402c11103480f00340303c001c200f440c01869000c04460700740d03100e038100003500c01c0d0001d0048034540d621510080000e01c0b5000c03408207020780c0071201c900091060348401030580c2c0b5848110750840080d00c4480343e120282c2040c03080b6414084199078420042e0100056240f070039000900e8401080c0d4068031020364441a41240c0080180341402402c1841d07014000301c2c000341e800941c4d96107659045031000e692500000d905040030f21800b100c040c1c0019206480c2ea45900384011428841411a40410440d954203402404048103440581112001800760414030360244843c0d48002802280c1e105e80599010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 473137832 1250 473136582 473136593
    0x60512100e0a060303020d081524040b040f08070612020c24070201050601020f10110d0207080c010608010506060712021c05041d0136060e06040506090c0f0702010507 73
    0x40c1d10030b031810000814914130790304020b42002036440c400382c00c020210b800c0107610702801501d03031138540c41a1100400044541c21070700d0a00c04000001480000c002400a280c40003100500b0588064111100c03501380d55552070759641d06244541030115003181009080d1030031030b030302a010400c42d5809484201000c81e00441d00100c0142495600d05186401c0c1b042d0240e09101d40741e400107081c0011b0031004480d8194541c0e400300c208001e08040d48640c1203442d18088042915842d850603031056407101c5803407403d9851504002c031100d200b0b600e40f000c0025a070405001e1203028090142100c0e241007200c1e11920340e0f4403203006081065208807040002c4400c002101c1140003c1659160b549950401800c030750f070154400403803412607901f0300040c07100c0082c0d080c1101401ca5926183e0044640319075100c081600d505900444081c50000000784c03980c2d1a4403124072810003200c04104556824003006a00030040d54485100740c4180701c8000c2da035401030002c041035801410003904241d5940d480 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 473139082 1250 473137832 473137859
    0xc0a030c0e090f0d03020a1808030f181f1e050f0706240906050603060f0103150f0303020a060e01020c1b01031103090d030c020d1b08071a0709090606051210 69
    0x401300203a40011002c1ea03055100058400c1d1050360703002441102d1a1400322992400f44060b240c29030000020042e45a0100f2100310200c00009416000d00c00e420f1581c814405030000c2c8020041090454041e00e41203819124503d01c0c0e95584406080c10b0000400304002d801c2803008548540e510401c1d0326a02ca038040d105507080980320b91510001f800c0c01701a00030349105a0140d80170f10018070030300c0300383d41c0c500c08106a0f1400c00e20300010310360f58000b141c4004440315401643c40d0712900b00c0101c01c3c9640070601100550242105000c0c81000e0305419080b441030101d00b0059401001c240d41d8005c09140e50f50410401c140b41c0803422007030190032000c49900c1503541d1403940c1e00804c403014106800d80100c00c00e030101c900180c14410411080506000300c120748003008850a0316020b410071036010142e8403116080030800502c42801113a00c1c13040c0009440500c04904080800140d03c034040c010070040d110190381c2d06080c4040c44143d541c030303824054690a280030950002140031120f400d007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 473140332 1250 473139082 473139103
    0xb0f0d020d1505240c010225030201051b030403140c16080615061c0906110d110903070306110c010908040e2d07020c0a0807080c0a030c0e090f 63
    0x40000d0350308000e80040b049214035403007240501e00c0482a03020550404124030744852030030956642d035501e0784040c6030082c03007a1081c140c45400441259901c69240c81c400c825030314400c0d00208901c0d220581c2c41055042800840860500d04000242c0020b1003813081000d66202444c040d42000c04400c00c807801d001e03541c022007446480f4034a0810914a040010a800c2031001c4614020580e2003004998588541080c090014082e02d1017070b982240681e03c07a50f040364029400700910341c40d0742e0a13810654096613841804e030781007079084000a4040c00444071901e80041c010800c407491036a400c400707011010050003022405001c880c0c1c0e250428000c1c80e5840c0c0c030036420031741d49908001140b0000540034060403400c3c4648500b07424101ca007404d085216130300c03100803205a647c5a080880c40c010366141442e40203461080002070b1070000003502006d681069055071581e401040a01c51201c9035844090070400031001d041200343c482c84402c0360000c050350240c540e00d4034103034440b03482e01e1502070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 473141582 1250 473140332 473140357
    0x4140c070b01090e030301030f050f01020f0927060f03070b070f03080703060b070b0603160e06210a0f0c090915050c07020a0501050d0b030604110111030a02070b0f0d02 74
    0x3449204020156a0040c05800b010780c0800c24111000041e40d600d001c14000200100340da80021001e000c4108a8845a4407811000755559000e00024103000e411089180d8003420880b1030045102c03541254161814241c40c0b03294000350307551410031002c021110380b03094041c003a0407400320b0b251540400606083d4010107903c4c0e1503075101c4c64010322000703004120600b0546805414080c0c086a070b4203d030003041d00000707261070310344030600003a042030500300404602c1c0c03035840303000a4405140c869080c400c0d80e08032010304072103841c000c0300301c030304a600c02c3c1d56104bc0d0461000d442c00140a03041d03035402140110350401029071070701020750407280400e03015200103010341d480300c0461134180101c1c0d50200303c040541d401d0400341d03408078141300780d64001d43d41880000b264103d40508181e0140600c8040201168814140b40c2400c2a00f076041120250000d000c04518180d0288000100c4151582d254000e0006514112410540f40c004401c1001d204000700700419166406001804038080c210 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 473142832 1250 473141582 473141587
    0x60d020c01020c0c0d05060c0d0b03010507030b100e010e120a0807060f0b0a05131a030d090801060b070b0703020d110703020f0c1f0e031908041a04030215070204140c 73
    0xf1810070b01d040da403c0b40c607520540a0855120020344007207038050300300c50076004103602c6030181c2c00804040e1054a10464066203031104100085034107400c0060366620640e0003280c04048000c0854408c07440d008aa0301094060218460504020306100b03000780c0540b0035503280d81280d42d1a0325083d445002d0035104603880300c0c020302c40c04070f40344a4084200d4085460024451900010405a04800e86450191640d600c40e10304020700425142a610f4070042c10303166445201d03400a084044075000c0c009240d840c26002040c0d41d00380303500b16018950086e10351020b560b903c24040b4041d52001041c4034105440f1420980540300b40f4001e0729690344250040c00b445c48003a04290318049900400e00e100c1d510303840616110b6030240105004910f15071070f01d41441d88410021924007003041130700c244400a5802d102c42844100700c042c00c00e6680c40c038114030420b40a0304d10305405000f1400040d50040508046250f1011181d00600d18544094400b142e80d2206403c80c040b10725040780c0e0918000c500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 473144082 1250 473142832 473142847
    0x501060306140d0516180e03070f03030b0d05120c070f03030516061503081206011d040b06090a030809150a020c06071a0702070626041101020304031707020112050f0411060d020c0102 80
    0x2806040307c1800104011810a50b00d80c49812115840c0000a010f050f41c0701d8001030640c403400040340c8200c1d04030b401c581e902132098104c421031798020040c4540a014404c008030702c0c0001400810100ca8140c0d0b0342906041c030700d00641c01e0550202004517002640c4076040103492100080c03440055001e9900700e5110a001090b2040c541d800810150411140c4403e0300c28112000841c0902040f05440000f100001c20740031884030b209501c20070f41d2100401c10004208801c1c6001486068400d40d001d040d501c10013036003416207004008103600036811015102c1110304152000d0116280030701c7c1d11400d03400d401c00c01258640300998800340140c010b06414404590054103001c0700350544440001441006544007112003000b034401030988500c00304c2000d00343e101704255805550808c0b4200e140d03401c1c1c81c1e1400c10303944c02910228042024070240424440e4039102d0548188200c0a0b90f0003180e68680d600c00c00422154001a8464001d209500c4182102d2014022060011000503980c010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 473145332 1250 473144082 473144129
    0x706050c130f0e060103051315020405090a1b020d09030b101d040204111303020f0102010b0603070e0f06030919031404030506190b0a06050903031204150501060306140d0516 76
    0x10042413141818282014005401e00d1b401a009142c0d4005040610f12000700c01800c2c0688030b650701003030740034180000340490720809512540c0e40403d1213581c51040845800240c0c0c440d500b8203002000314041990030404030307040004840d400342c0d0303410220010b6600c450360b1503072414075440e00070201030150081108504252240503510490720804504261003048002c0725113003103010081c0100c010380065041a4001d4000c40c01c0e00c10010b000941300c0ca0065001402d0700d52841031103104100398000711000707042100840740100c3c011406004050b1820450b4426504113101c114200b02c0c0009403201080c1c0080054005540300c2e40c081c103002d003440007001f08041514106542d001d45021400200341e99034880d804102e44040c2490f43d201c01003800000e06500800e41c0c4070080014900402040050091802031194403d1100f0841c41e40c8a807030442c00c80f0f00a0194043c0c0902d070901201d4103182c60001721a13074506c44d1003141d4400c1c00b101070701290044558454071005103408120844c000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 473146582 1250 473145332 473145359
    0x301141e07092d0306050f0a1b0903060504020f0406080304080f030c030703080a090c06203d15150309020604210501050f060307090b03030706050c130f 67
    0x40500d0302502443c100300252850280004048000b81082d0403458904032180618000540e0400c5040216142081c641155400c045aa855074246407040b609002c0100079201c00b803c03950750342e03000001c80c00d580c3ca8000804000c5c0013070743d0186001c100008190359030701824011b0305280000e103480d5480e004001e45030466441d2218259001846071100844000040c1e480b219090300d80102981c03901d124607001080c0b4004040c080580300900402c0341c0e5042502a500268041107075943c00f004010b2160316904c7c02c1c0c440016195019014417071481080948140b0b0f25502043c0c0090125500300950489e102000c0c1c44c0100700c4951800c21140448061000c1400154103003071000c0d0b0450350008409118a01407a80407031005081d40003401c80d0080c0703d07542176601000030401c9041c041810f00c20280c007190018071a10600a0101e0f01c01400d00614205038405402503081001d1030b42c40d00054580106040b003c180140070f060300280b016111032006080780c00c4990b8500f8203245c00400a80c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 473147832 1250 473146582 473146591
    0xe120901020708070305120f040b0d1a06090307050f0f06040e0f0609010608010509040623010e010b070f020d050c0a060509100e0f010c1506030602090301050604180b060301141e 78
    0x60b00f00d010b00700045400071600d203800703640c9400100d07908c40d2080603038080340c0a582c02c91400c0c41c02c04154014041c4495100340c050311000d044c017849100f0b0341001c10400384207481031680c06800010003080750b0b0410030035442030340d50b004040c2c00400c4a200003044550300154440110914070030203018100031141030030380d003007102515400701e00d41c1403500162148006100d0030740100c4900d80000c0030700005a101000181414500d95032503251710140c100884002e004041402000c0800055800030000460348800d901c02041d08401c580c035001c00030049019075007034910f80105400030b0301036500c07038080b080a803202d41c07525a22410030b007040c400000b28481d050420320004921a5005a80e4180d0100091009113031115100d14075151182018503141d5540e40d640307003090004020442140c0142a46c00c0e020b4000b0825551120204030641d0307441444a041c0350410b01d03031030020502c070350011030748039501400205035120044000c0300c05000c101e803000c103504069101c100044980c2900706802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 473149082 1250 473147832 473147849
    0xb070f110f0603040f0503120a05060906040e100b040e010617010c050a0804020d170c01020403061410061206051c05060a060e07051317010e0708010504030804080901030e1209010207 80
    0x10001807002150700303444098070140104000003501000c10804000f20b4030b4118000413020481d050048100300a80300070f40344144a082c81800103030b02170406109410805550500400300c05045007102c1008112550b01d86400a8031981aa43c070ba0809024242c020700880c28541421081143e0460071070f1001c6400e0003c1080405c00c0017940343d8445c2d103c50f040358045a080c90110001c0c07406449152403803441140c1000c000c03a0754204440198043c104032070050105200c00001c04a00d03171110030003100d01c0e862014848609011f2070344a6280710300b900341c03401c0d40040e591740c03180000b0365100c005e90701030282140d42814003000c0010a0100d990407901481040c403110b4203154200d6402d00b4002c001d041008001304041c4203010280403908010929041d1208503444490552800b821030403880c4011071207a2100003400c031030140310f900d10a541507901d02c055a1190b076241d440c50380c40240010b041507290f0040321700c045130a0090070705440c1c10300040c5585d0700c08180064148001035028800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 473150332 1250 473149082 473149099
    0x4150e0114070804180f060305011506080121021306092c0c060c010f090506060306070f02030405060706230a0b03030408031204020a1a0c0118050d030c090b070f11 72
    0x590660640b02924141c40170541c50002203203030880101404048030b40500c0c01c01d40000b0a020b81903101608080880f450745c48940c0d103801d01500c00000a01c42c58008594140007800903031112040343e0300040c40100a0703980e0b2511802000103a070096044082c0312a643d0b04811591031386131543e20400480d100a4190f03c1904030f0f82c10b9121080c07010424042c3c4400a040c1d0520701023036010039031a0540f10b80402c08151113040080e528101100c200740203118070004200d249001c1d4440340c10030b043c03e074000d41c83c15040005000090300209400c0756181d444400b041c4910b001c41c00b082c030f0140300d01c0000c1c2d24030703140c13646450081e03555000d04140240c00800040c084010044210b941802120a684900761200d00c00701306102240da000842c10310407012080003034648107004181c1852090700a005091a41d807122583c1050b1070301c001c0c40759200a078003000550181d003050140c16110f0408440f19075456402a240f44d04c82c0788215292405142408204a41102c1058190005461604 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 473151582 1250 473150332 473150347
    0x307030f02061e0f0711070605121f0b1e1b010b0f101407080c0d02011406090f0916170f07030b01030206070c05030a11030f0c06180604150e0114 64
    0x61443d4009801c042020700c580c0001032800340144481041d00081c00101c0d4a103654841d0020116002124007042c2c5051000100d000e2000072031112040f400c0f003075132a0202c903160141c5001554800a8942030702c170b003500c00726001002010041c1c041c00d90b2250004134400300e80382c0c21508481070045250b111310036005400d403158a4091180e00402c80908103140c5544041103c0c00f514007450400a207000d000180c0f6001e040004950303541b0340205500240711842e036001d603201d07180d030040391195045031045001820817803400b440207410002031000c0d118881810300d8042207c0003a9089002c5c0c02c24186801e66507030700108407541001f4121070141141500719514040c0721001031002910482010070114107002c01250244014000101112440300c100e1605440c95000082c03d284640100c10300b842c01d5a002160960895000402c040d2511590440c0808900c0c180344195820190601c00403a2003a0241c6901065242c1c41c0c8445d487d20820400040c140d403541c00140100c1181031159a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 473152832 1250 473151582 473151631
    0x30f070b030619080601080304170d2f070b130608130206090111060f0f34020f19062007060c12150326030a09140307030f0206 56
    0x40390011401c440652032000c1d18183ca106181c901d800000c0503015071400098100740c000001c2c82103400240c0112444403500d0310060310340403903c5030034021620b1a50346c1c0042202c10b030403442100191a0f680c103824000914000e01e01151a000220786100000d804441c0840c0c040c070880040100b0710b4290210f00d030094a90a03004010400240965008245000a40e014482ca1061150b0784002c1b00c00524010302258a0010199001e4078694000f00114580900d1940c0c1d6441b1004a4a2245848414419109800400103000008501030b800740070310308010512802a981104407a101042032403030510f1011a543c09946070502da440420a414408080d02a07442690f007041d4001010703540710307506641043c2c0c0b50760a025842d14015100c2030160310600e800301524040d90386100d0301103100c4041071918002c4d21074142280f10034000250324100325003004022a105107a011716092079503c10514541001a049011070074102640c44042d07410404541d002c0409105043d06c00f00c0020503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 473154082 1250 473152832 473152837
    0x311030c0a0e06061e04051003060b07240f02071104180b0a14040305070507060318060504060e030f04381305060a03020a021501030804270614030f070b 67
    0x2210078150ba080005912655450180c1e034000c42d40441c02101101144248072482c0d000b4001c40d44210011400c05005500c24030510050b2801c0c1c8004030718255503070b2104040100b01c245a2a0008441180008ad680a0340260304041030054000350f2144118075245a060468811140c0030b54501418254980e202086021030790707070020400d6245854010304000030b0140d10554084102c001c20901041682c850010b1550300e0050003138070701450715005c00703c05503031414048100f4010740c003242401240c410303031086030054465240016107400a20703815042d6044034448411144011404020301d034400ca441c091411110b0700d2020342c9104910905442c14400060000b22640200b5080c640021912600c0054040100b985880d550890300082c040d502c080c00c0400103000b4042e04408840044142e18113a96101741d103a81040d05020002c80f203981500018446c0000c000006060f00409200c1e0a0141801004010032280041c0905190041c406040310050b1300690b0708002403403a4200307 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 473155332 1250 473154082 473154089
    0x90a0509130308040501090b15011101050f0714070c0e010f06090602122104140c400f050612370804140103150602060127150311030c0a 60
    0x3c0c4072502c0d403141c0c10103600414441c60020250f5402c02c0600044080512001c500b0080c240da070203a44424810425082c0c80301550850803202d5290041500c05d40030780b81600030243d060300d0860612500d030721040141d000c980d104500c4102d112005100a500b11502d0340060444ca08290260b1440c0250095869901000b000b08034403012940e4a000d00c1900200e403403040003402c581d000ca040c20b06090300e2204c400b840b410703140d1140b0885895a030808072664891441486040f01c03c0c604840e20300c0c981c480401140c1c40031f01d41617192444a11500d40300b55034205114100c0010b0918040040c000c1d80340c122903d00005511144050b01c69401c0c040c90030880882c01c040d00081c0c0302c200b00114007401d840d110000d101e02804203020a04030559456017014400982e002c1c481025440388052802c007003405802d005810110050281d09404a406299264252000e440c02d076041141d140c02ca4904c1c0e01f214171000510a002c00038000d400c0f01d10000c002046000d81a0b44450300d0005100411612 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 473156582 1250 473155332 473155337
    0x7030807060b06030a0f150f05060d020903060114040f020f340f0b010e250504031e0308010618060e03030d02130312021b0d050f0102040902090a05091303 68
    0x240e924100412500100e40c0040d01900c925100e0603c3c0c01040b025080d03045c1d082000510f0070b980a4400c2540c42101002c64036022100f090072414101031058070b5024001400d100c81e000c200c0445c050300c04005040c000c2c0028644030503000b00e0f0100700000e40e54603140345603450303005102c03280740041e9040440e2200c41141d040c035000300240105009800c1031108081031020700e0003100500340140341022064140c41800b03100f000e82e80f6040560b0000c10290341091905080740c60706030f81e41c031840480c0130030800142042400d05960796903841e20303200c600700c0e4401c6c0060042200c1041640040e40b140c0500407900b401542c2c4420411064008406441001c08120b82c6a50a0f1101e84003841142c0b1560315041043d0341e40c942c1d8071641400704950340b10440d6650000c1b1008800c00d8804584034502c00b002000c00c000c0c40140070308101d007181004801b03039a140070381c100c0b038a100e8500348010301c0185154200561581c00e417030b0070001c084116a100c58091001c00d0104041544e491030107017501549070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 473157832 1250 473156582 473156587
    0x150c040605070f0203010f1a15071415010f080607020a032139080411010e03150f060a0f080706081902030a050a0e01021306051c02030c03040c050102030c070308 71
    0x60518081880f0501c1d40039401d54030b051210520740070301d0740000f044040c01c00c200b014540c404609020070340200000758407030502d060040310f0000340c0036031400c14003c0440007203d022005840307014010000a9100500c01640440d08103c2d60b6002e1100550100482c005002103038030f15140075006d41c003411448014060310342940c0381c41c100c1c554086a812150701c44031000c0e00d0038070025481444605106043c503070244803190002603115110551003260301641d45009610420300654040f80160805a07050081c0d07600c4550b950044a001441113004142d030340100d0800750700340300c00d01401703070000460b8001165081c0104403000882004850851401080d2a03850302e030100c6108038114010140c050000050009a42254101a010742089034042185004544503e400c030311070100415a43c0741c010004014030b5010b680540401110000c0314600901000e04c0c10080742c0c0100c420141004001c428041400f822000440103802c00303000440c9030074115090141c0d25050340c40000d1808800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 473159082 1250 473157832 473157847
    0x250c24030c09080304080c0f1c08091503270a0305180301093005040305100c02010b060c011a10140702030a150c11031e0708040512030c150c040605 65
    0x6a002c04010100740040c2c07600c80c0d4503070f940140c956512919240c031400c0040034070442e47c40e0039204185041c000041200c0c00e518155280c140039006142129400b00300f090203c0e41440651004510802030840820101c84407148a151003c0c9520000000b981c031627424100026001000c641d10215081c510f40f1596502200103409000202c4000f4903140040300b91070041110711101c1d03944a00b54041000c000300460350100d401d8010b5201c01341c1075500c06030208001910560041d03807036200d10320000c59600c1031080422503039441401c001ca96030303540781c8a107110010400b02d103414101044034003440c40396507410300070b0990ba014202d080c0b440300700240781c004656003000381348847c80d400300404000f14085000f44004044d02281400810318401c5d03a03614581001c0212507080c50b80e00a40203000c8003048140c0e0722078210b0181101c40000c208400710701582d507110013a5504000c1402181e68261000b0f6444c144480c00c8080310b484e5203080706000402900c541603c087e540ada141c1241c0750b0a4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 473160332 1250 473159082 473159087
    0xd0b0a0522140c0a0e0405010c0e0a0b160204290603160813051c080601030e0d03090212010e010c11010204050d02010c0224041a040e01050114250c24030c 68
    0x8903541c140744c1c0070b100307044001010440e10078901d1041c0e0282000700105107480d1026280c918031081c00300d522a000010510050007404043c14181c03c400c0e5400d00d86440740d40c0424100e60494080014840050050294180c1031195890210005032000c43c01c40c24008089000e0000001030320060191100c00281c5d14248420790007030864000e03040720508070071909261200505804520001a20440001c03281e50090240c3c151324542c00f401000301e4003170800214010003100390b0803a4440c0130310100c403d8440090094100030b0f013541c800043d0513400220050700f80c90039000d0040e250f0340140402c00890395514010600240c080c01d094000c421a840007a20050020071942c50f440107000030f41040c450024041d005486800e003084014003900d032044003441c0180d00c2a030516002c108010711555100e11000845001121012070034428250000b0340d200b48040c000e4092021040540020f000d08491801d001300000381d100c00b00442c610816a01aa840d110000b0904d6200d60b210303c581803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 473161582 1250 473160332 473160343
    0x53307020d120c0204060509070c080313050a0c260601090b04180c0305160b0f0a0c0b01120308130203060435070b0f0601021009020105090d0b0a052214 67
    0x503440050b048016040d060090a031681048050b0300031441d12502080b00c0c01c0c1000c0260180516484482c0d40c3c1246a03914101544000c20f03144940200140080008a04125400b40e03180705001c03d070685800c01c0240031a219402c019450300d050461014080440007040c1c060545880301d1003c1602c9031400081000b4081e0b0000d40300c0482c0300160508140002134408100780d2b440340d4152540e140890081009a0580b4080c5d5440108200040542000b11100800c1c100c059414080240e031080e403510882039100b6804001e2415010b02080c0415510600c66988090304c10b016140c100d0b69500031170394a0000501c020500003001340b0000d00c040c00308ec20040c1b140c0c8050320503008424080e81e078070341c6a04804022640558080c0220b01080405d00016200b040e060b80100f01c1c414001110b4030180100b40d60580c14407608000c440c0f80c6465205079051030500829104480381452040d1000310b4000038042a09507128038501c5d09114600901c01882a4118443e500300c0c8844005150912 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 473162832 1250 473161582 473161609
    0x100b07120207211104020f0a08040c050402030c0d0b0a06120b040902060408010c02060609040b04120504080601151e0e040b12100504020109080d0207060c050c1905330702 75
    0xd5040c008034080f101c048850020354400e031a46800f04c5400014002a40a1543c9070100124240b280c1801140f05504140e8818010350014844907500e6001c10100c0c1d209903106203500342d0016181c0441c4040d8024403c0c0031a06941001500f071034900b00034080d070301e03400780b1311071040d106c401403002941c55412030b49045030000e11040e43c42d075480348850b000b0404d400e43c00000d03008102c0054041d07e4130806c968402d42d004140c81e0303042e580d5561120358901041010303c050000070b000219803003104103d41406450510031560090306065030103000300340076103942d203040c4042124081009500140032541c000741620302050154000000441003004007000082611a0342c80400d000c10140e00201d00541c005c4c0c8800040300d8803070344000d45400165440314003590014204020180c41401400039503401031003aa1a10007521001544084c04107000b549812440001404a49072080e0200c000d4110300c85420359080d8583d202ca07404c00100a840141e06901040c45002d6403a03820a09100b03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 473164082 1250 473162832 473162849
    0xc030a0b120d02100501050f060a1701061d220b0d02120304050a08030a08072006090a0c060207060e060705010603151b050403230c0a1d100b07120207 66
    0x61040640c5082c0e0b1110051882001489041d02c48412000d05101d0b4a06985001c0c10304542503490740709010381540051400010000d00000c3c610714882030910f1640681415642c800107000044d1030720f60011002840d01e4803511400b45940310181215041c00251000140f001c0b0b40b031401100012049182c0ca0406504110201c2c0e0f101040ca001000420030354004450700350080e51100d5401c0c1c0d6902900d000b20022a03100d4000c108032501840d01740d010902c46000c09502c002c0c000d203086050490646500356594481c0441600b00041d42000030040c1c14188002c0c400d1524107080103104120468a241c0600b40c005602000e02c00d003904580d02031604022041201e08000e01c2610041044521040d4102e000341e805002d4107100d101100c1c11290032410320810310031000051344050b10710340000070f2684034207003a489070f83e184c150451005248082c180d80312030f80350080c180d031a2900140701d4140c4040c29141400202985400c0d00d111641189c46502021108441646041010307007081c0003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 473165332 1250 473164082 473164099
    0x304030305030f01120b0c1303020a030602030a1d0703080310030c0b04090b1815030c10020f0c0411030c0d020d0f0605010f02060f0c0903031608090316030203060c030a0b 75
    0x505802000443c0106452403054080c0d03a07031210070515183c020003004044076403190120302d4000c458409030a184840c81000d8240995076400614040050391084564640210070450b48e0407151051202c4150000140340c004041030142c26200e800300d00006007500c03400f00c04a1942c06860301c5075405168403200601c00561114400d003442c3e0071500c6030188213401d10705943c103c1c0c1807120700c0300301c2d080556019503040d803070b100c412010290741c40e903146406100b00c0e54051800d94070349000c94103401d1642c028041e12001103081c1030400058450030b071b014504100c003c032005007104d401c50b60310401000e200c1380c558000e0280400a4440d80515020241c28050b032000d140d0310a84c001c1040f02e038240c95500306041100d0742661228001c03102c007810740b04506e0002d070340080b0000c0140382c81840103041d2490800340351118550381049200c2603d5000000c0b607003d0281c01d00f008030b2286140034519010903242ba6500081e0303119402031207400380f201f000c00422800551030b0080080c00c0170003881001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 473166582 1250 473165332 473165339
    0x3120702060f16120b0409021918050402030706050a200304090501080f0d140f0301090905071a16020d0b041202070605040506040e0402190e010f0b18040b0f030304 72
    0x81d598007082d00c03044540c0e518440411215952100e407007020000c0c988510384641080d28600c4010803030310483c1900191035000101c016a40d4110f90810147d01d078001502060a00c03140058403480c1b0351507000040e203001700388000f50ba80001c0c000100c40061900d180d95002c40c80c002c039000c111460400707001c1e01006080c98241d91010014109441014900300070a0383c4c2c032070410343d5640c41008c0780d00b071b543c00c01d031840c611b070a100d100200c01c403494040d01580b9045d0041c0c181145903100360b1000b50445d0340d5003014010814141308500060046444003017040d550101641c00300d108419108007080084900301d0115110200c030050803035002180001d0f00c1c40d080c00c141d1101d01c40c0000f076034012b0007200030109809020350243c40c1030b51009031859003400c0c201243d10702c4a8001400c26030307111880c04041441c60121a00300300190804604021407035251a00d042e000c104c2c55044070b1000b410900c034018903506a101c0340d10b42648211030200d007055001c40840c481d200ca0591113501030000182c0403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 473167832 1250 473166582 473166587
    0x105030106061d0f0a03111c020d030c06021b03040518060319060b090705070b0702010c050f0f09060c0a0c091e0504060b03010203070507030207080d020d1107050d0b0f060108100611031207 83
    0xe0101c031020348000100f45180c810101c904510031000a42c07001c401c12b030702c0c000301e4403500306001c040d8880d250042ca00590040c0c00d80c03018038540e9110328103610008051240703040c40c070f8141118041141e07050409040000002c0e03110345042007811404403448800400380901500f00e6183d00c0805082c0e01504d050181c07004000303078800d060944009003c2000704000780d10500c9103a041440c59a2128284490f00b06600c1e2164007040011500d1134041c007000d8500d41d1240010b141000038540182840c84142c41e0403000c1d140a40d0081c5601c502d01850005055002c80b0b0286001560200c00540c554640c50a00d0062001c1071900340c1540c4048104900250000000d08085001e6001c48861540e111042651400d688a9030740040c0c0000c1540724001740a102c50102ca8060315055600308e94588000c2080c02c4565201591318100c0103080c0400b0082a000b4280c00c81c001b0310705400685004c000b089440d00e00391041c1c10400a004140300038481007482a1005609012684041c0c2c0c01d026000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 473169082 1250 473167832 473167853
    0x6030703180b071b210e0a170f0c0d0f03210509010608011b082505030103060c0c0201090605031914060a0605070b15120f0d080105030106061d0f0a03 66
    0x303080410303204c1414441c3c260314000c01c40c4070f40d03500c5451104043d50301d03a141000900102407070018040151074090603555500307101c40261446200b0041e49080e00c004203450400c00031100680c5802240d5000c01581f2101c50000c041c0390020401d0102100910f001c8408c8200c0d140003044202c0144080d005130042c0385c010b203026081c801e00071710910b80c071031026a00725220710034407104403028031018800140c000c4540f1980500e100b000c01105800f0303281000b080b9040c2e4a180f20000d00b00000500801180f4452001d581410f8582080502c0301030740088c240c1101c1e40101010300001000007072201c4808000c0043c0804407500c00d201003c03a200c642040020151001d510030000343c032011030745078894010344038400e422241c83c05550716900c81c00018007883c41820f5030488288010b0b4010403104004110030185018002c003c400e00c0c09e50300406600707041c2c204601c66410a0010800b0399409031801c2c1d00a81c0300071500e21070b1001000051002c901d144003154001001400004c24800708281 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 473170332 1250 473169082 473169091
    0xc070303110c09130503130e0f1005010c170418020915030c030c030604110a1101050105061e031003120c050d08040b040605090a151e06080c06030703180b 68
    0x881d800308820014400e40c4801c448245180c20800c80d90002d0b425000d40c50042c100c035030180054914251403840704060b00302c170541101c08401d4048040c844d23036920360031140e98010003179821503a01e2424400000d01408800002600d11080100c135207102c840389034100c42c0240321a00a01ca0b0320040205d6100c0650012a100d0707200b012500300c8210f103119102c00310380c49403419018103403540d03403030b0004507030300c0c0c6c1000d00700300d42155948001741ca408103020018458134240383c48440501030160742a13070030f481c4146c200500590b024421000c500d2000381403040100034030060780c1c0d280c0d581c0c00fa802d000c042203a80301510340642c509800e8800c0790010300c1340360601d004006035040c0d183c030360105507254101030b0707001860b10441c000060f02080c0b49601207504014080305840307200d0307000e8886451081c40074020300131017039031050545d855508820140c141e100806409001c828a092026511032607500c10450084d000080000c0001d4440d0b484110003d9400d18258508070403800c1c05c02c64880f0448 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 473171582 1250 473170332 473170337
    0x406360305060a0501081f2913060b03222307080f0304030807110a08010b01020c011b021009120302070906051e1e0406121209150f0c080c070303 64
    0x82c0424901c1c4214014541a62079200c01800100342c0c03070100309208030300051320030b081d203030b0700c038104000301c82010301c2c544101034031340210402015881c0c00c00400411400070f2034100780c03a0503010042410203005880c1c0c48880162010140a04000c106100c0080c4010007020140100594181220649004e40c6850400b004803071050380c403031030041d58420a84107042402d510038802000098840e000602d00c06100d60179642060403d44007144c0c1c21505030b008002d107039444014040c410750781001007464103102442d1606402c0700c40761112031101c0d40d880c8003a02a1602850080c4070074000c3e4100c0004040d4110420078418590070029102c040ba4003401c403409050240c001411b240048064841048048508040400320f004110b20920107029280130f00e00103c100000171340c1c4a00c601e0004201c0085290075140310703450002c88500c88100c40c80240300e0701a50a01c00d1983c08640300303406075054107012086014099041d030b0039032202040140b208100007482a00e0440210b50082103d102782c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 473172832 1250 473171582 473171593
    0x20415030e0a051c05040801150509060d020108010311040e06070201091707030807080a061e0521060f06061603030c122904020d050708010e09010207080406360305 72
    0x500c03600d50042c0180900143e01032003884040b1207400030801094443c40c2802480c15a4803c445400c0d1121440c10226072090305000b00700e18184a600320303a0100086512800700285035001a0000e41d041c003028203086d12401c81500c207038896130320165050645074200c030b00d41c0c5024078000303001c0c0148032401c030307020840502d810f1a02e25424080d40c515683c580c4a000e0599941e20045900d4040100b81a0703243e500d52100151900e2050084103c48480340030310103e2500b080284040544000b0202016a03414100f250074207401283d9030f42c00c140c0301d0300444a40c5d192000081c501e401010314201c1c0f06145407454038101a015072103240800340584401c100030814100c070303a08441074141e0603112050306c1540510309450105403001414002000141408852600b11045607422140c1d440403404c1d200c01803040b25106584180d000050388000d502d0b054459440c52414082d920414080c44500440c90038101400c400b41d00001d2440403100d6a05036200c4501804501d40e880b00362101e0195 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 473174082 1250 473172832 473172851
    0x30c0d3b120a0f0c050a02090c0409110c0d1115190c08072f241b18130e011a090f070516150906060b03061003020f0d02041503 56
    0x910301a100078819640340d4400e52010761101340c856006280701281d0320300801e0350101c0107903204802540900c0c0000006a255408e1007001001c0790b44620000c01981c10901c1360441020700040d2101030b5910a01c4d01c501c00d8940240d08628242600610f150400440c800304a007070409000d40b5107411f01c1d06107051001c0800d0050070b513848801030ba01400046c90700340c0f6502da421102c040c0b900c1e82c59080309840f6144050f0a0003c0d007401d15001070a598020700ca0000003801341072139040d913005200d20111074100d0000b07071501542c51082444074800343c0390030080503040b9a29032180701400c0c1d0103603030280215120858094024001d0705012290030108400e440081e0815118241c811182441e1144541d207420800b40c0c0c05030401030624031240c2c06007440b4000a00c55030800b480b0206000c0b80451003035a81d1070b10100b0b4034142d1f0403d000c911814801c00126980c1c0c1f60442a440384507003001071b40c4018440000300584502445030306882c0c000140015044088201c03110103d84540d802c0000908 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 473175332 1250 473174082 473174113
    0x14120301150e06070c0e1308030a051f0e01090507050403061d19020d0204020304022116090e2a031f0b030105060102030711012c010311030c0d3b 64
    0x60904c0103008a08040418401c11b82030503500f40d000f50428100020f06803495546100591003100d5154089855000b440a00400031a640d50382090300d204510703040e8104410b45683e80c41c144108141d85446602040489001c0e00c100c4018580200d41401000900142c00f0000d501203040405140309030070b400010a1500301910902503030003040300c80040915000c2101039040600140e82c405042011000365841103c100003500b850b5101030306a007030f002c01e06100c041d1400d60041c0070b0300d0b0a00038009864400850b40c61101c0c0003d42c1030421040f04215261094000202e046403d4880c1c0e031071fa03549081c0c0d05d0741a0380c118142e40b041070004214020a16098402c00d54100c0e001d68010b00c01c61001803001c01064004110600d0038480b89100c040b81c000c100c44140308041b01c1e42d03411202c00f00361541d250080403200c01c05070354010302d182080a060b11b1035102e16a01c10203496912a901c034005007103808a50301e1040781c102c014000005132011081c0b600b6084020803414403404082c004d0001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 473176582 1250 473175332 473175337
    0x1091506021b010c060b0603040c08060f040c091508160f0f080d05180306070c030e030c150c011d01021902060903120c0c0604060e0d02060103050a14120301150e06 72
    0x52080c0704034142c404080150f500c12000b9900f2103e2980b1202041101d880d4000031714031413809041c81c07450407407824842c1c0e03041c0b40d00030b048444690710510400c004070b62103181002c00c4030b058020004182e03c01000d056090802a04082064000ca2b10340c4052688014014015240c01000000131103955203078a0001420511581a440c0c00029170586142e010b10042c00507400608001c3d1305c000d04641c00030381804030031034182012501d050390f40c070b06055020f0606203100c00e06900920200c0380c081d00040100f0b41c1151030b03112002c030004050030244002e400c0290045041d001e4801c0c0c404003410310901075007005100b10320b540700742159aa951480010228010740540c40658540442c02c2c0c004208150010310220b650b09080000c3e40c440c000c108a0284101d0040c2000150310818425250500150028042c210b41c440b50061000c10070201d480610242d00108039a10340300c052107420300703100d120192040b4100d008000001c49945030408903290321851740d104110040010304001260 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 473177832 1250 473176582 473176603
    0xa0506120703020c0709090b07030c0e0f040b0102030f040e1e010f0b0a0e031501091802011709010e0a0b010306050f130f03020c0d0f060e030313060f0605090109150602 74
    0x140e440101160281c2c0c003075401040544000010365400301e480c0c0c444641a00c4150a040301c0301d401da84100318445078981302d22044440b8074606130454100d9100020b00111440500510843e6103944000b0141e008000b2102454201e01845440d980d8038a241c60b004001190b9540004901034440150385012034800b5040e1b4003035400e141c85a6052400c10051034105210b00018003200c40b4030300e1915601003002d0030300c25500b200b40340c02130741c1840c2e16107090318182d96085084c0d041803064480142c1e001190444038210090400d440b5036110a00385000d041c290a400349a400350422140c203010031058802c1c1641d0054809214507220711341c1c2c2d810240022a5031444c4002c6600c2d8280c00034060102d0170381d801d8082d00c101d42440817030400042120280d00c0003144c2e440c0085d062502040101c0c0900e0117100c07143c00185095217801001c01d280c007011018001c107015552200d507904021143d12920142c0400b400c12501981c450114000602e14011500101c5e030700000f0000302540b002682c2d5014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 473179082 1250 473177832 473177857
    0x120515090a05030a0e0a090614040c09050d0b0a0f05090304030b240904020a360207050703020913050303040b07020f06060f01050a030b040c030912020c0a14010c05010c0801050a0506 80
    0x10000c44071422145144007044007548880561000507054045002300400707803550241c4180110840c40401c0b003140c02d00e42c500b5062129051080205903a516a80c9100700d0300502070000a66800104a00811464046003403181c07810781440a054000409001644c2c40b07901d511030319894803084008014861246134440d181954550009424208203164205102812843c19a03442e82c035030340200d403424140410310250100801d0003d103103405c840ba40300149203404502e031900c81d03100c4a07150416400080d00803001500810811400b0b040c2c1c0406640c2c01ca000d5130b84074189881d04883d03108054a018005110741c410802c035295000c00c0441c05104010590040d10823200010343d07068004100100606940705628500f5449a0284c0c410030241c030750700040d8054140c50602070340600301e030390b450440d070207510b207044507071542c503407080945003003203e0303480d01d8004030004841d10040c1d59001070095081c0030003194496040b810b03440c140c0f4412509181103548841c1841507500a00b500401c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 473180332 1250 473179082 473179087
    0x90109060504050a1a0c061501020c041b05090303040f0311120105132312031e220809100c02130207081b190f03030c0309120f09120515090a0503 64
    0xc01d0030404664400f82181c40c4c4001c0c100038200303043c981080c7c0215444890701445400b0080d540da414040c150540108070b60405c03008818103400c2ea00c8a0301e0074420014082c0020b5810401e81d4100140d070001c007030080d5039091064592034114181d0000c0e64119000e0958400c8032500040b06010b80b900c910b401c00b1561030380000c10b844004061441901c14050100c0640600202c2d040500c04034031081c00e10703084655a0309220000281d2216400c50b40146002c54030140001c1e405c9020311810f501d002000207120600450800d24100c0c400c440305640e11441e20b0002210003900409041003030b900884940d0f4016862680ca0400d9200301c010051000c9000c0044482c0d410032541018080300880382202c105013410203208074640001c01c0241c54041c52207442e0010558507019040702c0500501d814420300240b0760b036a021178250702c600798042c4400c4401c0c10851620900b5058020300549200104485060410302c1d00c3e00c00c4043e00c00c4103144580d0000d8800003000500c2e04003264010021071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 473181582 1250 473180332 473180339
    0x90308030a2a0c050c0d0b0c070606090e101109180a020705070b180f0907211b0e030c0f0d03030f1d060f06031c090515090109060504050a 61
    0x180000c0b01e40b440010550035038103500041c102e5284446605a80303446000c01c030a41489440d10380e200301300c24481d100c44412600010382410000342c11a0040444c00e40743d985900d008806041c50f50007440c0030340c0c07900e031500200b60800240030841000d903100811445c007030451401c0680c460500c07c02c0d04408261203055144481c002d5540e0b0000d80c000340103040c4009940d400303040c00c3c0c0703d50002483c0040458030000c000220881074003010710888014004002d010b0214480cad0500404ca0b006003d48880719400f14121084040c05000d03004e5000c000340c4001000d1040d82c0c101f26150320001502032608801e160800145054800d8001864880804a00c90410800d80f5122004400309501c2e50303031948003c840760181c0b1400d80d020800c200d82c59902c404246151000041506058441c41005d00c0050384011600e214030310280101d80240030385a5109888400d4103921040d00489482d00040444e180394000e8009140d0990303030780464076504d40742150a03000b00d00034994403040c6da80d81007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 473182832 1250 473181582 473181601
    0x603110f03160b041a130b16020a170d0e030307060c0903060f06030b0f06010c02011803140609010501050a1a090109030213060501123303120f0f09030803 68
    0x14099001400c03507840ca018071088400b07070096540301c0340700303070b440803c0a025161003189401c2e42c402c19100241c1c20004044106009100217100c0c540281000092075090b00916500c44440144c016254486407543c44c8403211513032074510180c183c02d02031744010507107052191159519401d03001b001981040140c0d1100c10040594452603c14080041400400a80c031801080b94410924000042041c0340d41000810b50030300400030311303075643d03600708210340c070380e0041c1400e0302454081c0390010042107504100084a2090341000d40100c2c41c40c3c007010010500000c082e84184400d43c000e100c5640d880c8184060003119015030561505401c409000259080c1301038140d1a0052420341e01141d6290040362400409044010740705455400600445d40c21030100c40d645c0807103010800400000480160550843c403d210700304a0014403a00445081a03190700003441c1c122120400110030344401908100d080c80710030010130348004110082c42d0044000c0720480760080503481c03940da14106032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 473184082 1250 473182832 473182849
    0x1080115030507171c030e1005061e0604080a060b0319080f0717030c0903010b030c010903020904061113090c0507030f050c010e0706030b0906190302090405010219031a0103060311 79
    0x4122085c400e003601110038400c54940280d001041ea01e00090b6040c0c0364240c1810001060032403081c0300d0905050110540300d040d9040c44103460171056051061014001070b4491041c1c1d400b01d040c40c400d85900da800c0c08880d03071110703d46000403802c4031945400304451003910454010060008002400000400c0c1170f0b01c030040c841588940e42840d200c2280d0340703d400702500180c0300d10000400c04207152000b81024403c1c032030150800c45c001c0c02140411000240b50104601000b8000c0842c4000b160030054941c0188411500054442c3d40780c007549a030440c41d81d215072142c44101802c08502c029181d02800484a0068140e504c40b0782e000d082d401d0650b070310b6001c203907070b81391566079030034040c407045410b20010700a04410740d07000c120324030554100071400c4070280c41180314800c400d1a42c09805010300000007280e5068404d4038a5584505225009000305004904010404040c02c02134941c10741c0710b40746075020718030303c901c5048020380114201d4000d0b000c01082402e004403820075900d4800704 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 473185332 1250 473184082 473184119
    0x280801150905042a1106060411090a030303020702031002041503020c1504050d030f0b030c121608061e0402030703061d030c060a0c05070b0f0601090306090b01080115030507 76
    0xc056004a50720b00116048440c0307600c1420b45102c0c9401a40110783c1445032810a4904a140c00134192059030681e5440c1c010107044130384507544e9031049002c0902d61340140c5551100c01403d402c107140d0b590078058041d5000c160102d200b4000c2d8401c2c40d80e008a14800e8809403026910480c0344604004070940080d40200f600c06501e1141189142c061350440480610551085011f00015a945480a0152020790041c0c80702d480c01c0c8100504552400a000c3c44a42c0c0200c030407904040308600e80c24103100c0c0d00c03540f40d013030a0288100469250700c001031041c050101c031412031190300d84207424032000c110252002507258001e10070400200742e1750341201e6100c2054801c2d55402c0c1c0315403040b035403469000c41211580380d003010041040c1c51a851103003a003201803e081041c58414560b0f076040751504000e154083c3d012495001c242c00740d200d66aa00007441d800b4008102c00021402c0c034200002e001d118078040c560801018480010901200408595206004008250512865410450b844003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 473186582 1250 473185332 473185337
    0x708040804180906060501020d05070803100e0106021510050f13110a08011509060207030318030c03063303020105070204091e0b060a1809060f020c0328080115 70
    0x300114a1910020b0340600c21800418005510009444c150082d90303e598401410354000300800c002c595081070494a14951003075415540380d880c04a94491002d098001c070a02260003800414160380018114030f6802c134000d1000819070310005440d03000c0340780d806002d07000301c101c0c00c00130641e00300021008920071a40d200410b040b1102d4419038819000324400d0000a12202d00410000d5030001d50110288041c0c9041c1d10500d05045010f5a12905448010104040000c42c0213000c19401c000c003024690164040e0100c644e20b06000002c0c104000c04452074107419201c40b440030450712251901488205141140c9502c0d41d00151200d030012030381641c101d1b80392518080041d0300c0c902c20310028018400d0896483e08203060500400d00000d0100e4060f507815403080c40400380c510b0071040024060807010070303440b0b40c9107042805860782e10100000c4500100d940f00c01309a01001625458846c9003040542d400c3d810814004000f607803a0040114030b140c801031203a110524452030b526601070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 473187832 1250 473186582 473186587
    0xa021c0504170f1006030c0806010324090804030c0312030c1b021c05070e010801021204140309180106110a0c090b012001020a1d0f010f0314090f0f1507080408 70
    0x20b400f0b007420a80c00e070250f081c56582da15000c1c403c108000b40e03000060940700f0018580c541c1541d41d010002082c8100000103c07220311000001200a40c200c00c5a45a105e0502500c41c2d95a182407580255540403c1713030005441c00e20b003090603200e4403c2d8050711516507030381c080100c589030745e49040d01c040280a0340c200071140f002c1100d02910124440c0841d00c0b0300c00412941d8500781c6000c05440041e008081076074010401100e5100c0280b582e690415000b2032410f07005d206240c004d514501c1071811503a0412060007058120905840020b0704803841a02c58011400301030100ca03071941c10800e0003e040b5040c86406001c03091450307000e103040b82d106040048200c0d28412040403d0351610000070110f81d0006145a0441c2e8010422a03034030700c0c0310110b40d428084000000e40070720000c8a1060400c42e040300741140c02031003130704586d0f40e15021907070039441d600305182019144c40c0d15548900c1d0a00c180c61211f14103030000607060451091000c0c6404140c2c80c1d0350011640520050410794000209 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 473189082 1250 473187832 473187853
    0x2701060503070326070c0b1308101a0307030201050403061a0a0902070201090504090506160509040c200703080a0e0109030b150415060f0c0c090c050a021c050417 71
    0x30407525003d54040e82d21100e14031060001c80d92404d0948005000414040c02070030009030981204806031000f0701c1070301d501c034100529405e902c05a150310020380c6100d0440565003c1250350704c0306c011600402d203007680c0460101c00707040d5108010722000740060000c003c00c1000c1103c80d48038080024020200321840c1c0146800904001026004849120b40c00200d1004568012401e4002071009a805119800250b121140c43d110001d01441840a145c1030703400a0301d20032030440c2d0f10004014003c1040081080c401406484001c0800b400039000040050b5004000614102226840b00c81c0924140f1214001c69204040680041c18420342240c0032001a00c103031501d5220348815041c84c0080ca0385d410400040d50221142c40700d411007401c0c000d021155104c40d4404650410b8140b070250044189048504a0043d610120f01c0510741b030b00c0c820070716034004014110800c00307508451400300b0700142d5041003000580b9140200c0c82c1000200140109d02c4d41c00c0301c2910322402940c0c0784014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 473190332 1250 473189082 473189089
    0x3090f092512050901050105010c0308040c090f020711030a0b180703050703080d0f0c0206010b070c0e090a0b0a06120b09010219020c01090f05090604090f0611130e27010605 76
    0xd0005903003021584810b01d0300b030001c04070303c1442e030f01c10b94060091141d075140100113090301c4004c0c0800380401c25000c1c001418080320140910080141d4801004089850040e50001b500040011100104c003181841c1c81032034005011740b90b1070341007201e00300c10303860340700c0c0c464004007070750020030b0141c042e02c0310020100d1018000340d0019800340507020f580d0007900851400701c0322100c4620041a00e0621135180711940012082c1c191007610100c0c6540e40800d041a20400c003c5900238a20b0030404410400e0740840800d12219a84c86a2031042881e01d880707660105039000c9000d0400c0200d54030200401240c1503d620a4110790f10200061824010252003000041501c2d111005039104640c0c089003941e10500c1c00004080c402100c150705d6080800203100aa8081c00c07051044c0c1d16070902109000350500c1584080c0d80c0204104000007128030a05065080b096020328841c00c200c00024040c01c00201c1d907032050b0400903100c034901d5a0000300352255101041c54002a40d0b03152004100e945 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 473191582 1250 473190332 473190391
    0x1212030702030d110a09090b0102010b04150501030506120d03020f070b1e0106051e090103060506160c0e07081b0d0c08161803080a0509060f0705010b0303090f09 71
    0x255039601650b070b900d0b605102c1906441c12405184030401041140003421a4817200314001d461403034001080c00003000b00102d0141200da020254001c0c6410588450a01c510308504212402070303c00380419a114810040682c0310101c2100d43d030f401032040070031114461341c01041d04800125040b0b0801030203444540140b401102c0440b0100b00b250b0303507002c80800022117580189101e1920a160001d5010a40004080b40380d12644103903000c81e2074181c41e8001d40140c0082c00c0702501d419110320740000c48101489000380c069031141342d10000407035074a07160080e040c420120740c1c4540810340c450b142d0102007201e2041960640708414481194540100c0c0a1301c640c180040d502d250342c0c0d0810340c20203046407042d4458442400424103c40c1002c021100400c07040f42d8122070440d440710b03107181090740d540c818402c00c15030000d00001d51940011101c40500b0321180141c0c001c0080a101c0f0040c9581d0b0f100b041b039600c0e400141148540704614281802d60340c0021900740079050340d040d5202e00031020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 473192832 1250 473191582 473191591
    0xa03060f020d050604050c0a0e0a090519051308090d06060807060f1e02070e040c092c0c010212070c08010c05031f0e1603020903061005180103020a05121203 69
    0xd4000480c00c000400078000c013030f003040048a040000b07003031601a10010340b00c1d01c0c2444051044802e0003440a80d1a05914401489510418402e518200c4180b1080c108800b031203410f0300e440e16001c2820340c4410000040d9481d03100301482c0c9403118400410400c80d40312070044824548954000c40c0218040c0804402481146c07a404480b4030032240140c18a58000300b11010103d0700031643d40b0040c4d0014044086030003c201110450b2503a00b440d03980d102c000e4204034100c60501c5c00300401c01600c040b007644401142c420041581c1902c881450f21181200b04040c0161b100310420b20002c1215801400ca040c400d41070181c0003030b0703904242070a4403108004e45010500c0841005003d404940103a100d289111a0400a00d82031201440c0c100c0c0002d001190346540840c07001115600030b6044a0003544010f040b07900d60b03d0008040c081d5003105015240c082e25101d0040b05800780985120350580f54010100303c8080d060100780a9243ca41d001900101d02c41c0340441ca2070221030a0045008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 473194082 1250 473192832 473192861
    0x3060f0a0605030703140603060a0e030708030405070512031206010f0905040f0b090f100605071e0c0501110304050603061c080f0301090c0908060604050601020f03041d07090b070b060a0306 83
    0x3ca182c844005402c039006241c1d940d41220141081004590f404220f4590081c2d40380b00010303441c0521070007680741d03006120006003903400c000140b00034004002007040403100111440c1360f940101d0a01107489008000c558170201c4050008501158080c0c91480000105454405100396071400001e003030b11281280620701d5665600c05030014284813800d26840711242d103c01042d4280180c81c400201c102d0702c0b0380303400c0150200d2820204080345403440350425014400100300071090030401d070440b90a00c02c0f00c1c04280c03c6451071303c0e44a004410f49088070707802455281990b90300028804c0e6000380a0040c8040c40c010202d04002484942c003600051030719032807064596051892031411502c1110040091101101c02006000d00c0000c405038846c1007940c0114183c1c803a140180d181010070b803500030322800f002c500070490103841940000500000f04000000e6220f850003504e155400d070251071032110040005202084101d0a5030380c000c100030300109507550342e90300c83d0f03011120140518a007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 473195332 1250 473194082 473194087
    0x30c1506031505060a0e0106031a060a0503090606011803021201090b180106050406031509020d140c180112031413030c0e0a0b0a1503020f07030c1707031403060f0a0605 74
    0x282c540c081d1068503801941034540074820390a003807000001880512031031003010b0b220802c10954904821450001c4800604038035280c80e03a02c000a05030380c100701e49510720780c42045c00240142d807103401c501c0303d004d004030a0b115415045400340044010700800c0484299210300e0740900090010300700900c144541200c00d00701c039200984290950f1507a5000c030384214201403043c00450211816410030510380c0400040c044c40130300c08142090540b68015016080d1452528a5050042540017521000701c0c2c0403180611a606c0145040c0c00a02440550084984050300002d0080c690320b00c01001160100b0706120f07202450080381070b00c9800483d40c0c4850300004200501e45c00004035007040003407a061010018000100d002109a8450562500180d000210550303000f46d0440344694146c031403441e56140340d400c02428007500c1e404212051000c1509904180050703c05a41c45264990f4070b4242402011840f100b96400160440c1e81c40203204a10503030319a180b000b90760040041e07171100707074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 473196582 1250 473195332 473195363
    0xf070e090709090314071b0e0a0f09110f0307030f110a08150601050d090c0b070b0106080106210b030a06150b0f0904020d1104180b1804030c150603 65
    0x5040030341e9076010a00346410081030300000b80d081200c020b202c941080c032191310303440782d818040596180401c6141c00600110302c00301d8121a11782425120356407001c0b040c08100e510aa24408480310058060a00000c1d101800b109141c420740318101e000004044468464407030300e480c00c02c2000140d00300e665071102007078101a0304102d00f0303200040440744003a01c3c00701078038406243d070794000500311410408001030403021324045600200d00c01e5006081001c0150b2181800c80842e0b0104100703071010605c0307100014681d48644030355130503203c09a0300d00d4184984500d01c1100e081004055039034990f12621040340381d840c00c101c1504554001c250200d402a041643d41c4d00041407a04440541401002100190310707152040b035000c003009440050b6034100c03840380400180628400d200c00d0700d8001800151301c040b441c450b86032020120f1403c0040d4103c58041148001c0c0712520002915018400100804d010701c0034405079a0150b001c5640900c940a034031402c40d229034104403001b403004071011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 473197832 1250 473196582 473196601
    0x3110312060f01030b4203040507152003070b0c0702010806030c240405040219030501060807090308031003051e01050606070803041b0302040c0906030b040b090106110f070e 76
    0x1500e0781d4080c24100320101d003e00c0403585800c000300b501c4002c51b112081000a02020f1109550101403801c006039100075000080300c019401030f141917400d4400c03403c006ca0514281108010040143d85070003d26840d044c0a0a28512003d1078030340c4540003c0c081480801c002e824031a11a00003072844a80c0c03041ca0344000742401c940a4101d074000d5110003090102d035141c4440700040807500750140005d040f115840c0b05940c3c0704640044e0341042c00030400d0785403c50b00c14242410303943d079900c0130700c00e6a8a984007251f0440c0203c4440303000a406680c100f020032080002150001110a04000820740b43d8941920f8100103a0380c296031401d02c0103000c4c40002007846030a401210854405241c500940c448214030300010707101500a10241d01d0103407203401c80c1c040c039a00440c0d0150060041d48a0382e280034090000d184581c03008a82414280c1841e480d10744240d000c1083c000b4220f118a90a211040740e154002e000c0d09409882031085006a030300041005000824203142c01708050303d030143c100f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 473199082 1250 473197832 473197849
    0x50702180402120109080a03020c070305190c141003023001140604080a0b0601023405010503132901081b01020f15060a0510020f01180503160311031206 67
    0xd0f40d100d91400c940d4030009040b100455120001e2498050b846030a5060000d05016036a400245648030b40241411040e6a1603840c946681c01030090240107030f59100540030310002c494004e54464500794102203024069806002c0c412140004000f40424910b44e48902000200011003c00c0c01c10300108070f50641b00c4003e01b4900c0c02603481c24101032402251996400d0740d80001401c400340ea000095803030744200f040c0744014410078046200c80030001c080c2c0c1c181807021250105030a20408001c1415401141120302909104080361030898150300da00c8184610903a8003401aa0403405907134224010340103035800307000300d103010b00038100000151140b4085294001410f5412504899854440c0403400042d40031031003281e01c03d41da48800000e030408055400060388106202001d5034480d6000600c514100a228020072501448091100e0341190700f00b401082d03540104210030700340018040f04441c8610074108800144074409400b41180c0060f480303589241c1c1c1003010032010741b90109a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 473200332 1250 473199082 473199109
    0x14040e070903021c0b0c030603150f0709140609040c02012d18020a14010c0f03020610060e030307081309110d050601090f2718110402190f050702180402 67
    0x141e404030700c1c0c1e681d900c82e005681300130400c01b9400c1300800001d41d1528240200d83c1e0a282d01d4040e00800d02c0c10303041094200e4401d0ba61100003d09010011510f1745000018805002d0000c14440c100755025040002900250700c20340215503e86c028110609002c2d40703940130180c0800343d619141c200d200540001c0300c0f49520f0300c01c10070498428032800743e10303010804400d8510038031507440c0c407010660040c0c0320800c0e003400081681070500c64040c14194042000c40c0200700584d4414030031699080115008501118820ba00d604100260800100c0b084010320788910b146640b520020380d98840a01200c006051101445d6000070b12000107418505c1429444039003420109050760515a00300724050203809100806040e14600c001100d508000c0898101310f04d8006200c101800d501402403400d51140031145400003c00e1941c841c641030080c1d5491980d00700143c40e282c00b00010032030b51880707042e40c0a0207210082081034056140c0708000c1c005d0010300c50300f04905041c244140400e0810000c2d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 473201438 1106 473200332 473200369
    0x102c011428080103021011100f18030503011a03070915121e0621060506060c030c0d0915020a03030c11101406010503070c0314040e07090302 62
    0x42142d4162407003a602911a5524883d0585100700f0405a44805030828080142c0c03d095650004955034100c2e00d011441c20f001e441401d103a6110600198002000040144461080070003841907042d40040c965242d071406540040040300030f03006403070010000c0c0700d250080130710840c010307081d1203207603a0200000c82d1960445400c494480e04030068031400c10b14005180d0101c02c0c0c00c204a00088008445080b0342507a0302001000010b00155100310b0030700c8050700000e001c0000d0003000d140c400080080006100c0050400c0d1165800070070701010a040b40f1004030741c0401e80103415075140c18045942c0c40b031030105842d460b0310329541d02d10b01d104001280e0030b90400d41c1c00c00101260810703144190341d03e680c00111081c2c84222401e8000c10151240741c000a4800d524125041b800710000714202a15000350864100041e2003613000240300381028415031a0141504680355040c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 473021582 473201438 := by
  have h0 := BRFrame.cov_init 473021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 473021582 ≤ n) (h2 : n < 473201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
