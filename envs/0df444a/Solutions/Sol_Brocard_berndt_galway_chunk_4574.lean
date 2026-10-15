-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4574
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:03:22.283483+00:00
-- url     : https://prove2.me/submissions/0aa352f7-04d8-460d-9972-149d47a293e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 822482014 ≤ n < 822661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 822483264 1250 822482014 822482033
    0x5131a070f02161a07050105180607050a0c0201052a0a03080c07030219060902041107050609370507060216080d0c200d0602030702150402090403080402130c020703 72
    0x3400e03500c00b904450f80c4001509940c0078030b41c0a040350f11038402500301e040c4200303042110030003513001d0000d202034600b14008188003003804600740c03218016040020041ca21520440742661410b49506d02010b80c20340044400b9000341901d1200d64080ca199000900460300c00100c400c10b08800030f060034019032900070036110b400b80c10b24a6680d018014a00040d40100d0380030711003540d204507402c0c819841e0801d40003500c58008040c1d0440d143c13044003555045201d005003007690140040714200e4a0741e40c82c440c0c0d944510040d812818107045241d40303021031410485041c10040f4484443d03258101c5d06e829060452983c01000982c0c80268209000071003483d10f1802884894041c045184038503c0203030031a01c02c030000501c1d01800520301001c5a21102091700360250140141d0b12024852610300020350040d41c0c3c541c003506c42d40211580010142042905c1140d010702031001d03d0311144d400ba510900040c2080fa88140850517803040d102c96449030104e044600d070300810350207140d801d022a09 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 822484514 1250 822483264 822483287
    0x1f03080a020f1605040507021203091c0203030601080a150305010f02070201030506010819181b060801090b1804031403040f0309060c05030a080a0e070f0f0905010e070305131a07 78
    0x85802032152100b4419032503da80048920944000c83c05030340d401e0f401ca0500d2071408040403016400303c14400b0352240003c0b0b1030114500031465003140010301600307a94a00040f1415030004001800103089007800381c1158001400c0c092003d44050707100d541e118250344a10381101e801c20750101c1c0b48825580d0500641c0e821490a0a01c0d80d101c1c1000c1ca004525600540350400c40207444011031070030746c80f02c600c0e51480c05800003520b036050900b4521800b03010105124a0001076030000011542013100e104100c103402c001403071081a202d0469100998a800420a506101d0345840c036003c250041402144568802c0790b403026100001c1ca0080c05c1075000390002d0301003203251101c484c002400042220880003140c20003403095500c1100d601d014015a0090310414014181c00040403410102c0300e6060b1040d16001181c401e1721030750101d007101c0c024070520b42c4d2240f6040201e400240a81c0c00075411900e0f13000b400c4607a140700d4980c00801d16003181c060700448813500822002960180c0720514 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 822485764 1250 822484514 822484543
    0x9030809010c0e0306070309050c060a0804030210020f12061809070f1a04051915050d050c1602190b0403030522081c0306241d090f1f03080a02 63
    0x1c43c0604480401e54070b00d0010003500078550f55440c070006110042003d800800402018560380c0c85081500034070124065404502502c20441d52007508005402543e252109424000e414007401c400d1890b01504003400107a046401955001400c0114454052040344c10740004e105803071400201907203145a50380300005070503c03600160a601d8401044904440c0b00b21070015120004540c0c50419800c0780d448103826035034428002000b075801c5400347c00400b0070000300708105e0b03540054281d10b0340b0801c0a02000324124100c080018900350800e0300c541c140a00c0f034440312646809808456610503082a07000c580046124076180b0075001c5d003030820075503400751107044c2c500e8107030745580e00e030910001841c18007059100c00e403d07a0300c203030b2000004041018084050700d140c01e04d2a00c030b2000348981c450000361803110300900440322079000c640104001c3d018201d1607440d16540a00c1d075001500081c64191220079480205110300f0300c0c900034501440b03029503100040e420207850704003800403440303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 822487014 1250 822485764 822485777
    0x209060f0909010b030c0f031e0f15150a0f11121201051207050f181611061005010302030601030b091e10030201080f0709080d09090510230a080109030809010c 70
    0xc6e088200c00142d4072a980ca070440346031a81c4030b0742c0366000c504d881d040c201c0350039580c11310402c1510350034058090300407084a07210340c100ba80e48200340031000785450700301d00b0071038020048010468883c804400c0c0410480c41c1129002d001d22070024209070490710300c006002d002040465010140c02c10039401030400300c0c0c1603890184004141030703c506c00c0d40f140c1ca103c3d50740d07200c4070708803504d461882c00045c082c01c15041c00107280806110081100c80c1c104071000807034210400c59243c00c00617180740140d40302d030302e9202218036160044019510092440c0e04241c3c80d40c2883c41c060301c401c61004d028910340d080750b0003110201c511026021000800d01650b45901010810140c0d0f000000303140c000352001d840e00c04582c1d078820241d03408a202d6000c410644103000011260341e40c400702c0d01d801d03142c8141c0e0078412515188046000c200c040c1c0260100341d0004488110561071200d40c0d90f040210240c46035000d50341e00c040450840e0804082500410000720410884100c20f10a40142c3c0c10a07040030b6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 822488264 1250 822487014 822487021
    0x11030403081f060c021905040f1a220c1b11040509010b0f06030c04050603010b040614040f06050d0615110106051507021c060203070507120c0b190209060f0909010b03 73
    0x2061644c08070310181c02040c4021442e01c241c1008074500e4041d140c0a40280b020500300d5480c10020100c0c0079030360303442c0c0e02c80f004000324610b000032041ca000c490510324000c58007101600718004240c3e020b41c0d20f003442081180c0c0c10002083c9a0a4251640a060404121f0380c0f181c09000695000400018007a407512403011090340c0c440404580c804026520540c49588004007002036114036001598018408000020484a01001003041e200b16a6840720110040940c0a42f24000d0780510410b40d000781e90300340711962142004c0c01e40e0032006100851b80035501c045800300b69000241540001d440c0c01a182c00c4c00101340a420000d00064581142c0c800408440350410700820900038803400300107c4504160001412000140780c01650440d900c0c02c202101800c1a800f00e00100e410828038030b50440003a000b03001c05180550001c40c590710320740e90854840a144110210321305525800e1110030807a40b504000740481e0441001c0781503461002e1020005600c0051b409078601e10810001c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 822489514 1250 822488264 822488267
    0x906021e0d031d010e0f1e03070f0219030b101212030203130602040803092718010603060608070806010b040b0f09010e091504050709120b040611030403081f06 70
    0x11141c900d4151400081200c41541c01c0c40280f52401011a86982044000e10101d4808143c0350001c13510402101c030850420556501080708106040846030012710a00010400d04035004451500c018070705012400e40b00c8085a45806580013601ea1651100c01c014100c031420000c140500000c9030252180901651081d4008828a42800c101a008404500545100ca5031085155405241035403a59119060345540c0c5d0030240244e80704408510750820003941200340720300c1584006811b480f00b592540007400148404440900c0e6a40da40e00000001ca41d00e40304810145c052130003d0082c5501e0712503254604401030304010803101741000208030659420040343c3c04030528255058807140c1c40d10060790348039803550301c4503080990b69041218125840c9d100034007580040b5003c214640f201761007100e807030308203001d20585407940004060224058140081e07000d07200e81d03000320340204c0c07100c51414140c10903038044000c03a003000148160740e031490032004100009000580b12132880c0140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 822490764 1250 822489514 822489523
    0x30a020901030204200f0a030605100219020a0b0a0c050d1107060c020a15030227030703030509060415080a0c0806011b1b0b0a030b06030103170d020412030906021e 72
    0x70b106554410892151103001210607a01d20b64140c2103d44550b041e0b4090815680140000c000027440e040b0040f64078903000032030031050740d6581d0080c07140400c00d0299102c91000c0c3d000613640181c0070800001d051004078014200c50764280e4070f240d00a000c40c5840c514000340c180301c41c0280512220900440c4000203090412101d0925060b401d00d090343c00443e002200301d810400300300e102c4080c000e40c107030341540040007014039800300e1545c1210f80105180c9102441800a54160060381d42000401e1042d0007600107420002d0a907860b10743c1d50700460791ba1104e004185004a044102040f030b4503402c13441a05400c1c403590910550034507000307000800d5144191005d4400002250882d418400a10b202500115203080156800c0d074503510000c2c0341790401d80070440040e08011a50314103061800c1583d040703a500480e490725a1050255110b082c1d0040c8140d17031107840c0d09020024904a64280d8038140b94026144c2070155400c062009080040c6800b000840401603c808441c0084c0000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 822492014 1250 822490764 822490769
    0x40b091804021c1104020307030506130603080f2203030305010f0b09030c120102070212070519120609050a0605040609060501170615011107230109080307120309061a03010b030a020901 81
    0x60291004812454000e0030140d0134180150400d1011040010b615016484917001307900442d50304c4120000404002c05440440c04010000030301032146900c07003200c40004d00300f1411181000f070000013a0030440341e94290f40c1e82c0103400003906c40c0c00400118040c145030318047c01b41e48030118030303200101c00404d944028502c4050700400b1000d0325182901001c2d4151250b01c0d0340102604000e00c1d1380d8400603a54003680c011544a9080303040c0c0d10030b948000300d0b950800c5400e410110003081e2080d459800003031031002400d45090040c5102600000c40c240700c2d80d03224034032035440010b2580480c1401c5c3c1c100e40050308070389442d140c420030260900070000380c401e42c0081034800380b119280403000100d444d0300740c13071030300400c5c91141036008a01202c1da90038840340325070703001d0944c0700202c0c4420045441480c14818090150001c00210003c201080c51078035012900e0f080214001e1003da440c0c070101c6914842034a40322420512803501c1e03140030300070b0060310b00007100203000d511690340004140301411b2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 822493264 1250 822492014 822492049
    0x50a060906120b0d0308090c030a0302150c040e01180f0b0112270503091c0b0a0f060e070e1201050c0906031806041b0f0b120603010b06040b09180402 66
    0x1c0301e14064811098000044500300a13000002074880c0d490050981e40e001c1c3c500040303900070003800780381c14200052840e00361030f055801071180381d0b103000d00004540809000540c807050108004550701c0c05d60301c403c6008003404070a00750740c00d020b1010a41282e82c00c1030810307801410301d8200e240c07503a03102c50f6500c18005819400600c10381c1d03e40c15412682a19614040c1070340c41954100288074011015000c00c000550717002d4401483e82203c5082003210b1400100f1990030f1001244812006038400030079101ca034a400503170785442d40d2041103980c4045036003c0000300303491841000c504091031280d02ca002c10a00030f001c542024040094540503c0720711034001c403400300003d06651103405442211000d600c0c152a501c1c00c050030310403030790501028031813107520004200142d0301246511441c102d03006d84203e81d007000c191802c0500d10f5000600840e03419901c5001d01c420b00d50355540100018409500525a10480b400501105e6061090b2402c80401e0300c00400015859800104480c0c1806 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 822494514 1250 822493264 822493277
    0x605030f06010c050610140303030c040608130618050d0f090b0a0c0c0f0510050306091501021f1505040204030c09020702060f070807030e09041220010222050a060906 73
    0x81c030700100d407a03201064010f80540f0541083c800100c800e01054001d0300c0041004140403601c500c180369481c48103035410302180d00104005c10420344500042074000c3c907042d460b03581800307280c0c80e0340c400c2d1495000c0f01d282500301002123404010b410420302c0b9910100d424220340d820100c14010b040002d4510455080c2c8100040740120b051049401c1100d580d803042200c2407054580180903000805801194014180220b240164a0080c81074034820740008060f200306d5510303a25070401d42c0581882c0c1c21b055205083e4801e00001803000320101c0d0801402000a22100c84860842c0e40034a03540500d005a00c101700a001282c51038000c5020f075810a040540e0780e0b9a00d2011404903c151244927804010114189041100304001001c9081c080c1d0b40d1592140c1d480d01c1000b41c0c80e5410355000b0030515480004140050150706c5c041c040100c802201c00d030501c15100c0302c0c0d003684d1040807000f0140c1101c020010007804d0600024001d0300b41981d2581d84982490b0010784640103c1c0100003d04c501c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 822495764 1250 822494514 822494521
    0x315010f091e0803040e060a060215070e0a0801020a02060a06060e03030f071e110112062607080102070506100e040210050d0209060427050c07080c0a0503030906090d08010605030f 79
    0x24490031200060111504990340c86540386c20302c3e6000302069078940c1c0705150341d55000541c01c0c40001c84c00800440641641840d4440a006440301003da41c00315030411001e010004400e100ae01c06000700f620250041e00103442c1c01e64024040ba40b86811030002d001c1485110645c603107000060ba82c01030340840d5643d650721801c3c1018010f56100c005418604d410b016115810400310f01c100004080d030070388985603102440c1900b80b050320280d000d1200e21a0004903c100c100b961000030910800102e002e490349151a00102c40c26079000305002e0f103065001200780400c4103035450000c4000d00101d20404290b041940c002402e80c0840e944c504104072000c10600303004c0b002e40c0c0c1241c50007000107085580d16562800030029200404145003a2000740c90f5405c21803800500500f803142e00c049805030300c2c0950554400c4000d0b081040702c3d0b94030b0300c00c030642840045d5003000114003c0300e01c24014801c9180c07080c90706150614001000e01041005c5004000268000003500c1e0040c1c40c0780b081c030b9000c3d41c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 822497014 1250 822495764 822495809
    0xb061c09080702090106050403050708151f05190e06060703141b0a060c020d020c010906140702041401230d110612180d1103040e0402061e0315010f09 66
    0xb01500a07611440c03020001807055040b200900403248130300b044d1b40d4210368400d00c0c40d443daa450500300807513441010000e4042e0210480c01200c0030159540102c2d441e441d5030101d0109410542d40411038080303544180300c00304c4611040d50f4001011205c1c00e280c91120780d8010003140c08241502001000420300400001c0304030004100d0882c1c0108454411200b0f00301000500352000c050009401849203044050b80b003c51200e240d900f0607124500880c1ca40501101c10701e06c1c603440484100720501c400401685d540c092540b025003880c04010f0154100003007842000001c2600141305000b0000004154844151580c0c03040e80103146024044541004a91a44140c1b05c0203c0220964002c1007018240c4698602210303114101300d41100f03008050580e4000900600f0b502aa48240020040c405131104400d500c1480a00440c0c20041c00c2210030310b5042451059565003013010040000d40b02d034000e49034034130340300900c3c10200d4240542c3d0003501a0fa0103004008903c100405c281100c034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 822498264 1250 822497014 822497017
    0x4030311100e1f0c0206040b0a060e101a040f030602030402060903100f0b0307050a1403030f0d050105101b0b0903190801080c06031605070501060b070807060b061c0908 74
    0x1514968107205400000503082d84601d504024180f0442078501d100842d040c15100b5808034640a4000700600d071103985034480702d2a0002c0c5681d012a85404010404020a01c03505028803003440c0d110040c03d0034889103492043d440c218050128074144000c01c04502030700d0520003141e81000d00103030b072911203001040c4180b14540d00c0e0b070b4251140004072104c1e1240c95101d29015181c0c00303000c00c0080e0001040507200c0d1818491550701c20784611081c000a4101c2d040100840c10080c1240c3c40d02c1c03105001c110380c94005210088141d0359480040020307041000a00d00c1c154400e1800700110305008180d6003040c000400080e00fa000c040e4001504041c0400440b4865030000e0702901c450304c8440c500030003580d8240a103030300c0b80c003640c4d4000806090030003d90b4000c507001d81ca803c0101001003011074a940082c04280c40d29900d8940004100340200000c2c1f858a0180304000d03501d111500303011056540078001c0d036004a108100507600c0011424070b49501c284113220100315052070f410240c0340c6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 822499514 1250 822498264 822498283
    0x5090a05271606110d1d01030e1903020708010608070b0a0c020103140117190c05091f0f140d0809011202040807060c121b020d06090501050c13050f030304030311 71
    0x380b8008600810300700e030400c2190300008006401c442420445030004c961810008041c08100180c88a100c0203960203a0841031805807000100c8191000c61091460300341c05080c0d01f0307000343c1c121403000e1013900401c0c0202005400c030180103003a21440c0920021152090f0003a20b0304100202c60780c9011680300c0c0c0c005c01d0030710f411900c48102d00d586422030a0000404541d075400c483c495500c80301e40225080682030281500102e12040340c0b85440140000558000e006840c0781d1b0f48101c1d820801000800000064508550200d4001741080c10034412910000021841001c0c01c04110340090002e000f2184010401e20305440c018142c80400070107400b580d0002d800714000c0400220740194811002040343e401040d5240d204510000d060710008a0060300003d0010100c9402015081000b03c01055600c903400029645050392101c1342100d5081d01c520892100006052000d00d041c0c409600184c042110708100b82c4c0c6544000990f130b40f041d0b1000400b840300790480020700840c244000c540 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 822500764 1250 822499514 822499543
    0x3090316060c09060e151c0c0f0e220b03030d020f090a0f12082118060a06080304090b031608010203190908120903130602060105090a0527 61
    0x318a42035001d06081c020040014060348000503040c3c1c40340c0b00840e5070000103041c400c0c2c504040c160450b49580003204404007081c5150210401101502c01c400607400e25035900c81c03220101200091180088400c1503102d01e90030103590203080c040303003d000d64008010701d00013a40c007031000100c0e00390302032010702100307031131020179118403600c00c800003030801d4982200e101c41e81545841c04034050406500800540038612410344000414502c0102031b690115850350581e0115810194022102114001e0b0281c6190b200e950f8100410094107400000c0d0318010300010f820074051581e240258032407121000d8542910091a407000d010303101ca50004004801c0145840b540400d010354000e4130520b98401910101c803183c0599881140a00c0b58058410340c5095208070014044020160003116940000c01c00d003251001302c41c014000a00d05a009003070150302d000204041d801004001c6200103007040108100503610003116a00d441580241c04140f4006aa000c3d2401209115614 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 822502014 1250 822500764 822500797
    0x6130e07080619020408071701021b030a030509030a0f0318060207030503100503120d0c090b031303020114010e04030c03030204080d080412030b06030105010c02060c03070308040c09060b0f030903 86
    0x9044601240652203800042810f00d002101c95201d4412885a03114000780c2e5044100140400038881c400003c4d5403a02400250800c0c83c00c640c2002c14403965901c00e1850b0740001860000a0b03054050154042c070780c01c014504144448901400043d2240402001c0594502c00d21500c840d0065956070307901c2c0c110900319112406c500d0040c10310f91050310101003021400707200185500d000a0100d00700e441c46c985e007604210407000c0b5100600901c820390307010b00645a901007804400440035600c10a20401603000410042c14060b0071202d80f15204520000100d00501c0701d800302c0d003422074225078140780011426a0a01b001c030028000c0c1d4000c24003901070b0010548503298000d01080c010341c0074088030501c0d013103c80002c3e41198650303824540c0012091004008543c000c44a00401d01e00282800785000e080f0f501c05415540504012000f11322504140402d00c4982c0c100c40000c0d101c007140c01c0240c1814118003401030b019242c402c2d2400e42001001a42d00041801030700d02d003402d000c00e41d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 822503264 1250 822502014 822502019
    0xa021e0d0b0a1a040b0d02071502041505090f10020f0a030f112a13050408070b0f011206050c04030605090a1202120d024e0105030606130e07 62
    0x901401c441c00e041c52198511400105035450150303146040104001501c0d8030780340c54034101040c00d030044000070344480e50030f10813203000c100d100b00f03812004040c0b9000142c0d540d04010120411100144400e01040170a04c5640d90345d0b101d04492640030b03881200c1c0043c3c004d07454801207280c10068540b00420380246920381d820150408031210031030303d8544481da140001c0440003030307907076a01e6038074001c084800d55048803241d4903c80c1481050701010349120b90310104880614140e0750161021180c4040c0050010140a50201901d0b008240d034800d801c0507525001c0c1c804c4581e0002407018024a0707940b03011031451500748044800456201500b0301482c50300615241c1ca40c0d1284100382d821940340403034a00300b9803011401c0144c4a5030720303000ba800d1501f4081480d000750091104107401e55007246448032600c802c0003550b150131040e0038001d540b141c040b5440b682410040400200e10651540060084d0b94010414640c89a82a03400309012694212002c001c0c0c920007615180c82e01961001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 822504514 1250 822503264 822503287
    0x4061e0507090504020a0f0c020111011a15070201090e06041d0d030b0406060f1209080c0607090f0b0703111e0f06091c30062c0a021e 59
    0x91403007030005442d580806940e60043c03105074803d0030803850001d088603080c2c440f418006e1169082007801850041c084420901c0c0e21030031a1640080400c040c0c0d5480795104443c41c060700c058a40f03a010080381c1e1308001c11540060940c4805009095400c1e09090004103103807201d074028800800541401c0d802000c081503582e480340091a11a40000c3c181001d2510350300301030060070201d0f0702a5454103155050654105c0f007005040b80700c41d01c41da80340d103403000100702038002900c400003201002d0070841c00d00c1d00c0058900b0101c5e41c0000305201400e0b004001e00d4491505075482c160b0141407c50840000710625414410262008002d143d600a0000104c5500094602488440d48100c0726180c441d40009a9a40059440282c0015640c01b4100c0e000c0e00c104440184c145a500c48100350380d1071007200d82031010b070034a116481c50740c0d6034004210640100c1c6102c0b50703059430540e0701003401d00105198012168010301e081440e6400040c1c0a00e444410011002507412104140740c949610410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 822505764 1250 822504514 822504521
    0xc070e180a0b070810031113240e0112080a05070f060e100608060103081e190c02011709070303050a0e0301110712080c270904050706090801020a021504061e 69
    0x8000c00060800c1c0001050b907030078411700d08141c0f80c100d070030f100d010f80000c41081400309164501c0b00103252210a1032916903d407441c052201c64641c10f8010b010384c00d01e0015205000140d01015145c0540c04a45011035011000c9407403104040ca0580d9641005d801c140c0b414620010000303008a00c0d02000c0700d6840004500500510310100301804001d68a000300d035908c43c1d0a000c0541060420007014103e040c4005021912580070704440b030a141c4203030310303c0e11703401d10344d0629101081031052080f04540e4081070b0740301c1101100c480c410950170210381c00d603030b01c01c03403400700406000000418a00711030281504010b4002c0050092040484001010744540c00500080302d0100300c41c89110600d50003801e030b007881080b9030009181007120f9250303207903d600800d091030280b840009100580c5a20340724640d0340301d140558010301e0705502c0c0c040e0090402445a11100459105000c017107510b990114070600600100c0c01020080c2c2c449050450050240382c0d403080300750745602d00c0e607403a04800d0380 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 822507014 1250 822505764 822505771
    0x40f08030703140c0a12020904060e0702010e060709080c090402040e031b0c060f1c06090608030c0d03050105062b24060c030806091008061305070503030c070e180a0b 73
    0x140c60f914552a0030500d44030074041c0030b00307140100d02d0f10305640007448041c2d800352503101001080402e403e50b90b218090b84038482940d441c1c00603512252900c0500d041000500e402000c10f10304442e045260582080c0c6800004d0400c82c452075510011809669480e08404240d10304041035aa03502c8200d030300302c80104096408840c07107004031805031f50b107890f00b40305440280c061048014580550340c40040703600c000c0705680c801001d60350000490b001c0140e01c01c14000d424068000d541d41c007001c04c0918541814114407004040c10000144041c0d100d81c010303200d0300e542c01000b0600c0c80c540c40200701c00114501042201240c035007404000104003041751f2500c4100703607401c48203055440d40d00880301d9040d0300300040c0c007092204020842c1070410400c456403000009011003031003525013030030508002040e06c003018401c907400a0315040c800c1c00c0c08030b4001400110000d5280c01440e58101d6220907091103501028010701001a03078404492013151800305000055602190051600d444c1d8100300341e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 822508264 1250 822507014 822507041
    0x307030e1b0f1504120c0806040f031818321e0708061011060a0204050301060b190c020d0c06031406030613120c0209010b0712050a17040f08030703 65
    0x400384841e9814100900c04108420500f594545820810ba08008010301003007210400002400001c0440e014011a40a14480d06408103c1d0000c1d050042c4a441c200303850595841100100300104c6114030008540000b1102c404103c903a11502d1111b05015080c001c000003005001045042007c41c20b43c8074401c0c049100c1a1a040729a01ca00c441c091400320703403010219800700c0110714989410801100034152038546107031080c1c4803a440904010058400241039a00460b041c4903a14083c0540c40161071001e91060074401c8441040001c1c000030741d10340050050705441d48003552a003c080031006a041094006201c4e0f583c44010300403c1d807610118100034512012540c546400300c0e20790700611082418107032000542e04c8105201480700c8402003407040d09109900181c694504641c028684001c04a89802e21410b161100e04241c0078032004004041021808640d04000429400c036004150020141e0b034902d08040390305810900580a0302c800301c100310310150701d40c2003184030f40000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 822509514 1250 822508264 822508279
    0x50d020d050121171303082a0109050a0f020402160f060501141f090f0603060f09020f1903020f0304050f0115080d050c07170d030522080307030e1b 65
    0x2c0740b006500c0b4400350500105181480f1030750f13041c0b480e9070303c0181822401142c4e88000c1030795244d5602c0815480061040c1100e40d19410b0791301583c54541c0c90040c800e8a610080c04010080c0c0c1d641c940350030403110002d0030302c070f50300071244123545450381a61000c09090200c81c02504850038144c994030039070641203c8076030130540040f4840d01c46044089041c04042d07c0c0000031078051401c07170240c0520b0000c2d034cc100700c005400081c010b81c00b2020000200903030741f00010014105180c0c11b5100845801c006819401003081c1d4020185c50400c41d80c03a00141d480419084501d42070840282c4543d036a04000b03200c01005200502c80003107166240105460000c0001e1580b000128032045010300c02c94070745130405051002100d010320010701300b548022040e0755040e40c451a240745429030b07041100030701d640040310034024141c0511401d50000403150028075008803500312a4460309503582c005201c2d103004801700e441c850094001c014200d00600584084502684080782c21800141105104264 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 822510764 1250 822509514 822509549
    0xa0f15020702090406020304020d1e0528030f0306030804090b030c01031e022a0a1509020a0b0919080c0301141027020409020a0f020c0d12050d020d0501 67
    0x90910071540c0c010b81c064021002ca40c0c2da40c649000a400040c8242c1c1c03c07129030307170311729001895101c0308488486494444404000007030030f0661401100c4550152200260340c420380305541710501e183e404507418035008880c04d10707440c0128003402d0558402001c04030085000724400030980c02220380100d00390111130542201000440540c3e80001c0020400f08115070300362280c1300d4903001400300d9258110192001032048040d0282c220a410360244241c12410f40b1604210020201d03440c2000b0308981070203184819000141840e90724801c1c5003020000007040245a250a013866100100611209000c659a0b0481ea910341c00e200c88035920035480c0200403912201b41c1c14440d4000c10a005054000a04048040b80c910b10700100026016281890031142601c0310700080001d032140800150715042e808902500e1944800009025502b004540744810b03100d00c0c8440015a4011560130704200b0102c00c141c55500ca80d092081520780001114000001e664002c941200d6004a04154004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 822512014 1250 822510764 822510803
    0x4060201060302150a0f0e0409140c010e15090d030905030303040c030506280921030b0a0f1212030b12030304020306131a07050d0f091704060203091c02030a0f 70
    0xb20709828103000c101506e40701406548500641c8401140140c030004000e091500d4025010707014022907001c59104005402c00c5503031101e103482c2340c0300301a500c000900c106c4400b03c2c2c13041d014000215000d4502c554048041c584104401001440e02409a030f2340c80c2010b0910616615150000781c6481c071418010403001c00301c5001546c00002e91080d100d05604074808158043c0209600a8031104a010110404006120011600c0d00c10f29100040c140e23074004d050000c0b0003c0c5902160a03104504d20422820654207100c0d224194058203112903416100c0082c0e004006282529400510101ca0004526000002540902e000b10101c03080d43d9074140c4058044500104c004210142210300b00e2101d052000d0900d400c50114140242801c00c440381c5801203810529089034940e4403180c24000384003814142119046890300154602030410390040e580c0c0c441d080140d030003070b1120111000000600c1c03c00351900c40d8000c00346c13081c09000341401c00f1884500300040d00c0d54100d4210107807062 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 822513264 1250 822512014 822512017
    0xf0e040914072102041d25150503070320041701060905040210050d0b0904060204180b10110a0c090c0815090114180405011e0608210408030406020106030215 69
    0x3c851001c03a102c820050f076800d00018028500340f5070009055901220048042030102d03100b20703038890301e03c1480394200c2d883d00b20404107103134040300b455060200d2442035070343d004040300e50002641c20040392801003d4008030301600d80c4007510034507034004200420200b240e40404607175904902e009001003a1070380464800c9907070075100258000e503a405040c104500510107886c1c4424036030000110980608003007184002c08079070031502180e0000c0e0a01c42428082d000315104070980c038080000e8481c001c0030505545516080d28180055503805420f01e03042086600070f0182e1100d0178421507a40d8101c0300001d007040440500214030001c000400c81d028004000060f41c03c014895903481e4071b000140c0c0d0804003c00b00088e04980d1030414280c603009080c40644c0503600c5000001011440c1c00c0c5440c040024904e040300c1d02500342541007020f1540014900280b10032034121030003a0002040c0c0600d50320036036008951501020400141c16078040d800134080380c2c026901041d560740c051000c20311a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 822514514 1250 822513264 822513299
    0xd0e0306090a0b09070e01240e0f04180f050c01140a050703030b04020d09030e0a050f03150c090d0515010603090b1302040f15090e010b010f0f0e04091407 68
    0x25500074200da42c04180d01c001c1c40c58101808900380c2d901e0a44800b420781c3c40d500241c000e0911400b50201034210300010140010460443e482e11070700c0300c5228070000b00c00c016255040d9200e6030b120b408c4a50444c038046ea0b0300031a00d900c4140707205a580245000e035240c0b840842028040f80c03605040003450b005a50445140c0001076580ca85006140e9409800070300074081459081982400b80c00e49120340ba1203804220380c0280c41d804402090f0b0010000507038803e40100380220000c9104000903100025402c0350040600d640001c4d41d55a40d41740c0b25a4080c0c444240d501c19841465503050140200d52014840f02800501d2080d83c2c0f1000140c05440e180300d0010800039461000800403c0b85089841c900d0380300420100c0d1000302040310a090320903c0c8179200e20485511010002e40e00c0d60b00c0383d410b0046207030009001e981e1412300044c06462051428005102c103500211030b00c54031920b844000444000e004002c9801c0f141080d614030081541320b0380441c03049800100d00280b4040c5103105 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 822515764 1250 822514514 822514531
    0x1c030209040f1d032505120403030c120e100e0301021312061a09070e010207030b19060f030314070812010e0115020f071502030f030f1b160303020309031603020d0e0306 74
    0x105d41c000901c420404a407070b0070f86141c040d01d0344c00500740500c0002800194003a030f40d40750301c088803410115452004261007005002c12480790710204d45401c1c8901184100c2414074488c3d55608201103801b92050402c400c0b01400800b81c0403c1106a0380310010015001c0d210170403040e0f0354001c0c01800c1d8496003003071543c054040c0b0005101c0354410311604007480707810b10503129200d98075078030a407511105940174451a501d4400c3e4918001c0c5622980c001400b1042010040e02e1440e02c0141614141400c44c6811042c00100d817002d11212a0031600c45116100e12a8020343c0d4450710440d080e0320a00030075502c1c2c43c00c00c80da03401c11031000481545555004000d401c95031b281a00c60312407890030340190400d500052041e01b04d6191082c001d54410054115a41924600b030042e1080314120300e5240c041c1d019040c070105003c035070480224000c2070340c0f50030700507982d032185070481b0300d103000380b40406c03001c260419008010140c2c0810150450002034450a40304980e07801015150002113a0034038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 822517014 1250 822515764 822515797
    0x26060d081c0e0c041a0a1a04030c030f020a05182d01030b1005031c080c070203030310030311011e0207140d2705031c030209040f1d03 59
    0x8022403000c10007400380224406000d20315000801c0c40c20160b849182c00d05102d50061000020076043c1400307003180c002408801c03a8103e0304514000340508403a40520701d640d0030804440ea0714400c200d001c907000b540e0130540f41c48946581e460506805911540c040380a014007803800100c6061504041d0315102e0a055182082d50303072401c001d00300100c00d50103e40b1680003124600051800401d540740618010300420307181e442c0c100802c01d04040c81c3c2d4030060199000b2040402c2480c0c1c1d4040399501d0500c1842d2130005512180b520035104d002e0b1190181d0305001c000180b050f0000342c0a156411680700b904c6040324180402c804a00f03c40c182090701c814407000f2107581c0d14060311640100a040c0c81000d040799480c46104141d403804103d484018003080611144464214010368001008030805460044060501e00860f4458915012107007520300070041030400d0718003035010b0304c000d180c010300104182060351000720b000d001c5030001d000510040c0801c070b020140c13010048400c050769812101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 822518264 1250 822517014 822517039
    0x2100203150d0201030605040f0605041103040c060f020a0c0b030f09030a0203040b0d090f0b0f13021e0310020d021b01062108091017060409030f110c0a062606 70
    0x21241282d15041241003681e02c19000c41d0658642c410540a404102c0e0000b4666061070140f02c02c50f041103c088400350003c0c002c020025000d00e10b800309440403450400705000c01490203a01e002e00d0440c006100e51045000400c40300070900145115100403c429a00e43c4c49a044a40d100c1c452505902c0040e00204814820504454020214079401da03200290030310700ca8903010504100c0303c10440c2d0303a800c000c0501c40e8111076503a800d074001e581400c105d4001c110680c0050302285989944e901400200142581c082d03805001400103008145810340d0b03921041030404009501c80118841c81c20f0070b00c6560740d0203020503c0340c007080d0707a40c3c13403450711007100004140d50300303040368500444002804110101c9503480d03204a601c103104d4107880303039200700c041540e841c800d80d0002804a4003540c41d00c11a9804298001c1e1000d1645c031450409244c2c440206800d141480d42d0483d50682103608041c0c0080d1446e03202c0d2011080880a0803c5402c88584240e603801405003910f01540c0002c081c4903e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 822519514 1250 822518264 822518269
    0x12090806071817060f07031a0909160f1d010e1816030f060e0f0c0103020903030919051002070b0d0c030e0604140c0d17070f020d0b04030210020315 65
    0x2e82104076072040c054601503501e0070303295601941c1c250040356a400c507000740000400071402c09504440c0504003405200c41548041703000740320610100c0c2c464011500801c0b03c03500300707002c1580300c412901d008a012a80303034601d4007050b01d01403180ea0b1400c9201c1c1d500c00d08280326114520f0694205c4503280c007864a40c0701c20010940d041014030703003a5020b58008520b0070b1a480c140003000318894080e14200a2150800500b22401030300d8a907010f0700800110450b0b0b40d404158000c2c246004d080c0140c40340d94031000702c0d03d140212001140c101e48015120821701080031a86412a0b50489005a41c060a03e20403a00c600d0b1900c2600e228030410b000b100c40c92002600011587e03001303858005940112155000d02e0010305440660b44800c5d00c010b440054441405101e00c44c01d01a103800780407105903510991101814001c041c11b01c580401d980303040040c0b8106090640360006c1c194104560345042c00b9600290996046025114410742d01400416600945c0c4c49180841c0301e10a00c0c1c02000c05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 822520764 1250 822519514 822519527
    0xb12062407060624020c0907090503010c030f0f0b1c0f120503070e0915190b0a0f0e0108060f3007050108011a0403080706020c06131209080607 63
    0x40c1098500300810240040000c0c400c09005201e01511001c81c500c1d00d0f01804843c400486900c40420300400000454940d070002942140d02e48141c9504045a50f40b000c11104041603801085d0326500f4000b041d104588d164011400008601c1000c1004c0c00b84070080404482c0b60300900742c0c0040c9100c64010400b078101000041030360007034642c0c0c1070401c1c95075076000c09507003006150340c0854008000c0c010025803009400c0c4179a4001c3e05c00320302034200020340007880c51410440610440300e00035101c0d81030705800c50500007482d0481030b09803a640d60701d001900031011060740b003001a81841c82042c0710340c0b045d0001d5000e100040c0c88074941d0b904030018480201c6650310a8440340301c541c098100301032803001c54544c5800c220fa003d012480d0078400014030303484040c1d00401c100b0703807513011500b80c4e61601c00c11101100c0c0d104603c2d5548a01c0c0c2e00e011006401040c3e0b50300c1040c02003500f008101d40075411f013403001030312404000c19030410410042c6c1c0e401c8014000c40416078000b00000d4005d80c083d0310b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 822522014 1250 822520764 822520789
    0xa031101030f0218030129091f23150d0903120f0506190f0e07170c091201020c0303150307090504061406041a1207080a06090c06021209040207080f030f100b1206 71
    0x2c15800040c01352140010700c1200d90112102e003d50380309c22b50500d25018100d00c00304c0e804440d84500c00ca191402005540a600e03c1c041e9000c5d034480e1854105806081280e01c0c10f040c0c0d07041400212b505004400061008480c07207406107014159000220f1022030400007554188820340d6009400e0040481e801d80700240391005008c1100c182884c18009800c3c02d80c405c1509201c11686c5002200c01d002903500304280f491420f078010310000d81c0384880401640e0303110025a902451098400001a05c0d01a85030f00c203001c0c8600c0c0600b03010500003141c2004c0381d400e201441e80e03c6503803180740078041140d0f01c8400c800d81900c000c21000001d481c1000440040380c801004540006403505019814068850300c2182d10551b1446110100560010008001d00917400a071070651102d06c00310549200344c06480780f085500080000c02c0041200c01c0d10810381c02c1421460302c6c1e1511002ca0f0000038001e50b0307104007003481000c00190064050041f0b85945000f5121000c203a220001170020202048 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 822523264 1250 822522014 822522031
    0x2030706020f1b0721030912021f02060105042726041d0a0e0d050304051507110708060601090e0604020d05100603060b04050a031101030f021803012909 67
    0x4210032000e50409005614008210344041c0911920b442017045c0c0a2403031440e6444103140364041000800d4004480604441002603c50504880c52000505900b03135600084ca110a403005900d40e8103500140c401c0c143d40d0240c80403c10860b580704e80041840f4208685411421101c95060006510402c2c00480460310750318407000b005800c1d407420b0305400c96000107038619601d00300d4044800c01c80107110380280108004000d0a408c4840303041e00e4840540804040c02000008141044001c001c88020000e400101d2105400c0400c0010b1808554000c9641d80340305100380400c0314040070038074902440050b160813403554604000440044402004190302581c02d000c1004601e0302400342d41d2080b10f00a02c42982d2608001001d800c540c116000302d0700d00c0100740024805500c84181d070a0940750480200301d42e184110004802800c00200d0381c0b0078841c00452201603c00a1030510800928214002c0c4001c1524200d082078030445034442140c604a040002c500038104101d2040e00550034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 822524514 1250 822523264 822523267
    0x1320030a0209090a020415061e05040801050c0c0f0601050109121110031e020304020102150421021605030c0f121905030415051c150302090f010f060207030302030706020f 75
    0x654002039201802103a003501c490300445040d130114070b803034403640203803082040c450007005040940c014024002c0c00881141c2c03128841c2c035003510b540100306413001081c00318020f0089142c8803180c0025500100e0000a080c859083e078150400c5001c20600d06a45c01a9120303078a503842c10f000b41c11958914101500d1407141e082000316217882d6010210103502c40b54402040142401c1d0304a0382680d811680c03185010b01c107105020050313a0100e03200c040310317603101c42c003070101d46442c00e02d003080c070360304a100149148030842e100c012a07401045c042030480480e18030400c60303a6540180754541804034401580301e10201440d604d0303842c05082164008510004550350964040204400340c141e2480554046d0300c0410708001d141a0124502c0032200d00b03241c807500b0551040d14645011030038881c5000c515032241014802c42c81c001c03141000940e001000030519042000201d40d001200303010742c02041e400218042415800003481c0d0f4101c960584c001c3d032030400340f0b45600c0002c0d0410b05070086203100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 822525764 1250 822524514 822524533
    0xc060a03150801020a0e0a18020702041b0e030106050f0109151b0f050c06070b0a2d0207060b100203070318090e060f0a0605030c0108060622030b132003 67
    0x10044075240500910400181da40003e41c40103005004445001441100da0580900600340401081d0507000403c40001d82c559000d403001402a266032581c0301c181039000d040807400301d584440b038041129401d038005c05c0300700c0e01d92040c00b43d04604079240301e010901480342044100e40020301d400c00d640725460000c841000c05000f000584407404815595104118503003424000306000d41d44014404681003491704260350b03205103450034010701100500e5682e00b08050030010b0b15203000c000820081c013a48010400d131040c3d10081d04a0281503074540d140c901031004c0ea0403d44030080b84501e41e50011402c040540e64119440002d441d482c4c4400c1c0368101e8001142c80030760040c0a1707a0544000a0469860102da1202c0480300091140c06410b00780740342002243c80108414410701c6e02840c003242c181c2c0c0c901d80483c2440c412100c032141d850250741d1100d841004110454025248555101c3c0e203180c40d515902c41c1d1405d0721500282c4040079101403141280b0700d24081c00050b100240c141c5030000d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 822527014 1250 822525764 822525791
    0x190b040218040c0e090313060e0f100320030103020f19051008010611070b090f01210920011d030f06070216090207151509050c0901080c030601020c060a03 68
    0x30301607400703e5544400c03001c04d00124004000a40c1d000c042d9900031803c0c0003c15400c0040b06286128040901a088284105540340c5440c43c40030440003410303821a991008400400a05011000c2021306500040b0103c3c231018100489040346c0d00284074200890200d401c101c80d00408068000b00c0000d0003c000400740c503200045492180e00d0348a100f065890101c025102110440381d071032031504074003014002941f443c01501c03103400741622401a00d01451005843c00700e10659004441c10512070b1529135084030313810807909588100d0200524902402c552544030303002803640ca020401c12459443c143c0988401e83d103403010018101c81040340e20f900700700c1c01e142c8144d83e2980103800c0500d00c0d21600b013141644000902d0441c201710f2030070000e42c40c0c8a443d112455584010f03a520344201a010110300c02c03508014184401080145007031a000c02055540503100c2c1034007089042e800900c0014030042628071921060700a807031a50401002c0060b190300c60400740d424566141030200c051f6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 822528264 1250 822527014 822527059
    0x41112060124020c101d0429010504030f06050a140702010b0103060b0a080c18100309030801090603050c0904020415060201060807050904260f1812190b0402 69
    0x2040c0190b90000c141494060b01418502040781e01800c0d90b2000f0315504085d00c3d0008040c3c1c0120b10340ca4900401d01c20200c619080303160790303880700d40d100c0d041c0312458200041d140c01c03140080d24004407000600e410700f001912603005a10018240e40e4085e0b032107001054154101541c440c11103140042e4040d01008030108907a0195107800050303550300148421560944116406020501102030070035602410040c510800107001080d1054042120203181800c44121582080020710100f24605034080040090034440f4007a00012a1900006184a068494442903a030000d0262010058004c103100c800d42020784220703001640d0351030214400344101905005080360358008140c442c138240c8042c0c9000040d400031f61168144205001c00544003032a0040700f0740c000303901040300c0e29446a8210150040361081140071034001140d07101c50301344e02080c880041e0304440050004100010041c1e036002d0b00940d5041e41207909445801288221030701030b6004d44010101d00d19002d003036034580c0c100c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 822529514 1250 822528264 822528269
    0x206030c0306030d0504080a03110c0312070b16090306021c05130c05040212071b050a0b190e07060c0206040302150c0f16060c050102071a07120b090411120601 70
    0x10050110501003685001d00c04070482513114076003541441c2c02c0c1b14029460780e482c203c00030140040c1680018030b018090107912040d26008060398040c011501941000740d105081c1140c40d20400e00010b020300e052400b192001425680d5410082c03070441d6505802503002046c2c400080101e0101c004640741d050180c00e200d002d0705502d00c00071955528080703100400716001148500d006101226200810505880d801001c1c1c0c500500100424140300e030a02000c0320b0064540d00030a0031a006012846a00600402c00c10501e0b12080c0400740d51307041110703081c0701d9040f9590000e401c1003080d0f030b03c03804030921010700040409242541c0e0f0b60014070400340d45101d0042500c404940c1c18844030f030134000059100b040001820b505114000000c403100b88600031403051000d68840d0a042c86025810383d18815880f28400007500002c4035841d405120440384400041e1110f05009400001030142041640c0090a04503036610345959079504d0007001201190420003074280c3d50005402088081d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 822530764 1250 822529514 822529531
    0x110d050702030d090309150201021c021b0109050307031b050d1101060b13080d0503010e070f14070c05030c0409150902150a050a080f0c0d050403020708070f170f07090f020403020603 80
    0x11b098030340007200c614803000c0101c080540e4414040300402120042d002d402c4070031760200050381c99180c40c03c4503aa244120040046540ca0061004100074001000701031450180e2200016030f07441c0c02d0801c0002c403003008010621f0300104075403107245008525142c1400702440001c1411500c80e07113a0003840c1c111110074040040b105404022401c0240700e030352116003952801610b07640c10101000064a03018004008000945481c00c0540388581d590309140d89504840762f58909281c05c02c00380d50840b90150500c20b010b42c0d011030010340b80c10f2041c0700126602030041c814044268005d4002042005000d9030400c414809021000444800401c40700c1e0040d1506901c8282c103003c02400b0100040107c44003064020a10081c1842e07441962250611480013282c50703515803a040341000b08a501c40b1101740300380100410184071100300c86c010740d0740c110141a069210248425074404c184d201041180d0000316003801460103c0d00312090020454502518140e030f26404666558001c448460 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 822532014 1250 822530764 822530777
    0x6180501020426030414010507140303071e0215040807050d09080c011706090402010e12030408010e0d0f081e01060e031e03180d020901080a0213110d050702030d0903 73
    0x40c00c8900045440001410400c83d10b450400da160940d130344038038050750000f920803010345240340e8800c40072103265552210a1410701044000480c2d0340e504246c070f0313500100b20001c03201d92100768000c08101070003010740c0c0203000a403180d005201e03c112010b0400c0c2c41d0a035081009101081c010400d81041c0740341c541c4c503601101d2525501d1410025006442d40c1000400705641004509645006801c001c00716903481440e140c41c03005a94002d42548800e80190f010300d6505295840400548126190b000c001d20440ca030024805440703820002001d4003041700540f1140700343e44604d0445a100d4010307100e485d541d044000101101c00002d920000c0003610b942c011a52038102482000d1212020115901071440503040280d00c07401032040f0f8900202a0707480401c003650b2209100c9403132640241500079296120380001e82c6950a105050b40502403540c8032401451252190040303002d6000102c6040002d81e1012101909000d400342c42188018040c0030f1a4007108e108044005101e5210503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 822533264 1250 822532014 822532019
    0x1080601080a02010816030e07031202070b03060303041215150510180e0601050912010507090f0b03071404170d09150801050d080c060709080c0405160804061805010204 74
    0x11850020140c102450503003003480181c0040c1d03003081040b07420017526000d02c05850007009080700200304414400d406071086400020a1200e800e644101910241d4291080039803114681c15141c031041e039145816030f0040108104103001c10008944c080d108400c2c1d000d0800100509d0426a500c05da0040c4008000c1c42040150789440c04501d8030b0900582012503e00502280c400400003031485255000d0030101c001460680c0f00744100c076403821004004c402001c00790550540282001c680080c0800e858071008240c1c84450349024007100e19a10f1f605296070384d121002c841c1d40c030306444a2000c0580c10b000114000c0421f00d4040c0d0302c17050081c003c0810303400480b8010015101c680c4182012801070b110035000c80d5105651906403076054038012860342c100e00d050180c1d0b00c68121031440500508081c003840d168401c2108080f50b181c001161a04d150940030041200c00a6800340c1c81c5c5a803c0050440c16070254000c2c0e50b105000744800100f4407001e49042c0c050701c101820484160350300040c107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 822534514 1250 822533264 822533279
    0x6050a0b060d0213050f0102150c0405030a030e0330091503090606013e07031a191e090204200d0e15010b0c0f0d05070204230c0711061201 61
    0x1104c001c0c0360886d1850199125800040e4070b1307003201403000c0880303404840042c2d41402004100c07401441c2c06030881e0012013141c00d0040c10303640e14010640c441d01802d140c10384000342d40380054028100d04030781a4803070194500290071950040310711a42000c1c1070803000e00d00780001c5010350300c0b13080880c000d055140f8207000010800e80d039440d400344441b15000c002000ca101c0000500c0a810165450350108108546003189403403100e500c02440070f0528004501004000700200d4065044000444e0141d11080240003d0f90600302401c0c41d00e8401c40074400d001c40103900194815800903100154541c102034822540200c1c0c80000b240806002546111100e8540b0400746010311941c00b030192443c00c480a251070200c10720540c00702d9140824405029102405443c1260054400320358144001e00030141650300403000c141d201d0761604039000d056840700c01e0419618042d030006d1040d260703a1060b40c880c1c1c51300a04c00030784520b0101d1503042c806446503c010300d4205482c65411001e0740c5007100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 822535764 1250 822534514 822534547
    0x605040b070903241104090e0f0f0d050d1523030c0333041b06050a020c010518180109150602150a090f061a150706050a0b060d02 57
    0x100320104000181d0410100f035a1301129400c29a108082e5180d08220b502968050212419002007039030000400003190328090b848029a0158001695071000d003000f1015110300a00029450036001420311045403132140e0010448075901a0002900440302481c2d850800701c950030107114240c0740140000e14180c166002003484400300c0041503a8401480485d44a585805400c50a018048640c94480350303030440140070142221a03411483c602400c28004039849020340b00303907850040790003007085441707141202c2d07031b9011036001080784401c488011140769104d692203401080441d01d40c1c445941da030164407031192508200518542d410001240102c2c0c40799112004071217015101040015004590b04007401802c000580c40e030b90703444c08010061324084500600150904030600d080003000d42c0018244240d007400d003031007189401d0600c074221820b00c0001007114410300c9280700044640d00081c4d48080041008196450510040381a07600142c0f40090300c203401040c2580d4002c6403a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 822537014 1250 822535764 822535771
    0x10c020c0a0b0a02100902040e0a03230702010f08370c0201020406091406040f0306020a09140a0902031f120b0a02090a03020402070c0b1801080c0304210c0c030605040b 74
    0x42c901850306840304006580c45420020030080365840f01341d00c400395680c650040c0312140c4a0341c140c411081d418540141003041d0b0102000741c0351420400c00340d00c2102d0905484480382e0603100c403113078081c01c0b4109542c030901c01008004651000007410403c40090803a60840340d6a000705600c0c1d0341d20358901002501c8948802404684c818030041100d103903c8191402158180701d1903a4204180d1004211b240c492608000b01207510a00000704000c103035802010450016a1740124040e10350380300520000e900c0025a03807004525074280030050f855401160007001180305000d28280300d041d050358003030065210244440c82920f21030180720510242d40d0b40101c000d841103162001d110300107500900c0500019001d10313030210301141002204101900500952850703251220191408542401c810910060010300d60f240450240724040054a0213558429103401701442d011b06c4281c04483d14070190010007041d495200d0110746500c0541003d54014440451149030a0411120014024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 822538264 1250 822537014 822537029
    0xa0507052a2d0904060e01021303210207180e06090a020a090b0d0609030c020414060406090504120e0d170d0e030309070e07210e061b0304020409080c010c020c0a 71
    0x2080c246000b5a40d4005001007030780840b1402d100e0303121410200018141c61b2240c02441d880000d0a1030003651b201c06040c22240704059110186081c0c80a552288055441302c0d4050392200307809000000320b022000d130040d03888020000d8406084544545000380c00e0f030380303180305822656a541c00d5091060b68000a0100307042d050000b0035a060110750004c0c008d6802824040d50743c012002003600c1a03410110b0391390001c1c001e0121307880d514124400c29170143c524034410307440c1c500d0000c0c0c00191170207000d100d25003001d040104004000419610040c42907007503036000110004280006d520000c11a4601c514904010f858208201f0410b04880340c0d4a0703590070f640d20074401c2082400c2c000908001783c401010791a08180c42d92070094503c0800c0411800c4680b1000c01d48805001589e8030032044080e0507011a0f100c2d0329400c4006100001c6480314980280d410400140941840e030054100c04d8400c80055281140749210740303085540c400101401a00480c0b015401490100d4000b405070012 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 822539514 1250 822538264 822538309
    0x150917040302010e090121021215090d03060b0d020c120712031508061f080307080712090501140f040e0a2a020307030e1c2904080a0507052a 62
    0x100880ca0300344100038a8807c1d00d500e0b80ea40b1003401c545498400140c0b0095a4003107400d010f4407080001a0038400325550341440c46481101c205061103030089208590206c0c5503145401c40c48961000a50301c1080141c4091203110911000e52000e00c004000d400c3c0100b0302e2313040414101c00c0c02020b442c030505155403103200e400e00903c996030f030108103035400a0310989080c3c0b01d48210626154807200796070000c101400089455400c2c80801002001307414414031041010650100c4256040c081030b010b218001030010800c2905c42201c000280310a20808640a0030319544100400850804641407420541c1350441040f20807880c9080d40e020190700030b070480002c00c003e50000d680c0d0090040c09800c004a81c1203c090035284e5502481780007040c900b4070710742c81896060610305010301b032b4800c8c10f490b0b040d24018080348a001c815240a15070140c003a0345070207040c43c411903c6400401090f00c09005400d421078203510720100f0004140495041c00402c40420410000002030000180403203180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 822540764 1250 822539514 822539519
    0x3030c0418020306060a03050907031707140d140a030b030712211b11091816050a0b070602090a03120311030609130f06050903030f0108010c0c150917040302010e0901 73
    0x142c038402c6c2c82d0034030400d26001482c0e944004c2624a4942d4991000c0c00c4941c100802550880b080c0c00101012800703116800c074407481000c030031b541d200c00c003080d02000218885030b00301881071400d00420801c0900d14010462044550020341452956803000300c2d4403103641e0031101003203481d04480c819040040070020b400c01c45141c0c0a000005101e40b142c180b4002c9003500340400c03442c004440603510000e04803804915101c00042c8000d014101e505019110300c1f102541c0407056907081000780e60001d072503401924a0300c0c2010140d0342000108980b5250244611341080c0c9500203150f006501500c03426418007001c820103411141006104019010304008011583e01d134140c1040d0030425050b4090000505800d0800b140004600000e04130784c100001d01c41d000d42e0000c081e5004890740d13903031841c5a03680d0308249401c854188072030f080403c5058460b0804118003c42840c08040007030340104412030310b903561022054015000c449016008281071080d5640011800d40b03c502c181d800b04034550 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 822542014 1250 822540764 822540769
    0x180903092d060309161e0e041e0c0915051005040e16020109170406080f0402030a1419080706060e01050904081818071101023903030c0418020306 64
    0x8042881060182d207000000c184445401c200030300c080300c0d41e01c0044800c241c45401050304488440009010000c10365408200c110080b0101c40c05203a000e45003036041d000201000402d81490b20040d14421310a2000194284a600881c2c4003440d0500940fa440e508110800086210380c1200300c00300401400107022000a0b501d0b2030390012480102c0c03168044080004a01400c3e00d0700d0f00600400455609a1060901d04050030a03244983c560204580d1107800f40058641d08480281d030680c01403000c138000c60380514030380c0c04602112068902016407a42d100c13888007a01241181c0140380040c46105103d118407a2201501d0201c94001e0194074000000c1c12500c0041d20181c00030340f0000308042c80c88203107551034401860103494800320581c1040c0e20384101c40c080300d500e0042180c420344514502418421a50244520030388150004c141058124941c014006a08441189500032054869040003d50722424030302289960310390030545240682c0e800141d1230003480b8010701c00d02140346e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 822543264 1250 822542014 822542089
    0x5060a0507020406090c05071e031d01090512030c190201050f0c010204030b1801050a2c070b070605010602070f032607120e100512040201050918090309 67
    0x55268603115486800318000035005085941c09002c11078138204122005a4128024211a9003d00d0244184140f599092100c03e05281401000510f5400c03000003c414080c0900e100310710185001c80c021500d03480803400d0901001800c40890780003042d40b2440d1007081244031401600014401081d08140d40041c186001c0d10800ba10f400c0b43c0425540c01e403403c25030646001310f030071240c014210309200c08444400c071000220600b045d400c01c0001004580d80d40902c42c03c041b0000d0003c54444d03114002203003020355802401145000741080004c036020007a025082490160000069a504d0000040e143c09a03070f40c8800d40f40c240d810020400309d44541c040003005220303405044242e0301224030f0050075204146008181c00003040c28404040d9010048003040a4103072050034004540000954503030107041ca040801140f107000040055201d100a4207005401420102150340d44071981c040261040700c0c03111181d800400c180242c0e1403d244042da07407903101040a5051a181000500807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 822544514 1250 822543264 822543277
    0x31422180e150105150c0607170a05062b020910060f0f020a080f2701020712020916020a02100e0a09020403150504050c030a0302060f18100c051207020606030709060506 74
    0x4170020035092034038216101c22600d4909040043d611645080d41010b4841c0d800c2501580007136146200240704050503226a0340030b284001d2101c9071051b0050a03400013500d5028000c0d41c1c0e4148001c444006803114880035020b4071200031848206400c28500070140640b5990410800000007040f14040390049503074401c0307039001310b83e40b6910b01104c07409041074030424840b0061011000c1820580140d0040c054020000076425110899911850203100f07891a000180d80200c1d520003080c0d103004014030600f00d04880740107941c0d00900d560002041d08103000341d20408070780c0aa80200d1103280000a8101401c15900114209400c58607100040381940c0d030040a190f0382c030801706048c4207041048403101c910060480c0c000500318034000391111030540d5542101162100840d0205046240b10410070a4010051200310341c04c03d8164090001e03100c0034400c1c44010004842d50703084000c07841c1d00c0380c641500105000e0405005061400b2415401888041e00c0c021080c4119030321201202c05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 822545764 1250 822544514 822544519
    0x706020a140403120215090c0f0a0b040e0406060617041e05070f091a280807060c111f0c0c0807080c0a12031422180e150105 55
    0x31500c030118029601c04100c0c50000c0c0080801240020411042c4c00210000728001d41c20f50f407515415850034428244182d8455640c2e812000d0140345600388107107410400c0c0001000d000341160b80da0300031a016409034000d101d48007611400c00003841300318000e013401007038a8a0190112010410409036800001d0001441c50450110b8850902c0006a0320202c82d60031005136001240c1d01c0b411550005403520400c51100c0c01d0100f403103901744122108211690016080001040000d4900ca10b800c0e031012203001d000440030404a103404082011402510450700e5160b9080100e040689400c20b250744080d2154108040815910b006104804529052802c14800b06403140c9401d07016007030f09812802491060200c00666800002541e82103a40103803800d5100700d0702d80840710b0081d40b59050213804540080c5075490042e0201c401440000003824480d0085810504603050800303880e4810750324400b05040035200960380740b04480e9880740200c000c028084260550b800e0001b4144038003072 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 822547014 1250 822545764 822545767
    0x3030c14150112021f05030604182310020c0a021810030605070c0209040528030212030424050711016608070e10020102040b070305071205040b070602 66
    0x1001c44d00d0350b03005e52121000e02d0050032401091410018540d410843d085031180c2d04060b0948000c941c240500c00d01c1c2504440e60038180044088900e24480302c1445040491007445445408214a032015143e84d0021101900c85441e030340c0104204a010812521000b04000050102d03039074421540700d04480c1e0041c03000c0350655444d00156055018510003942109843d010002045400b25101600d5010780400204c2c03408103c1510710342d0074038070380000d01681c00704211410100b40b000103190b0251203421101200d98407445c422112061280c04880007075129801d000d4481d40150942c1404840034008006456005c4007101c4805140400300004100c2022001c121203125403412140c8040c03490404000d984590000b00103462074504903041103810f4401018240c440c103003441c0a01e0169039100c480c050400104082140c83d01003200c2550740c2040001402c41c044809070424a000b86c5405490322842c0c1040e90155224031031480030040104420f01000d074040058603203041e00103c006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 822548264 1250 822547014 822547049
    0x8030703050a05161d04063c12050a061e06081603030c080903030a0210050c0a0c290702010b01030b04050606030106260a050402011707050f180a03030c141501 70
    0x8940c0303810384c0c45c42c9500517080040c0465910050808030042001000d40d4810f1920000b000c004913110003500307031020160310300301081040448024a08100c4c0214240c030071075a895a1200b0485d51621080b902400e008498440f6889040c450740e401040039a019141d58642c035103404091030514000181030007480ca150009101d003103420b40f0311010300030302100d41d144032100340a940c0e20010220502d24609090006010f1440c0109030b5800709a01d81707881801c6560395803209507056000c1d40c1440c1504480c002d000c0142045800b190040c08941c0001402a281034001005d941c090f002c003600581c10031050094540700c0500326811182039103010000441e43c0c1d9003000481a01a001030b440c0c5072600244038503195250310003401030340b00740c98100220b4034590b031804038044111013075400718070705108480380008004010081860b1648c0a001510346202c001408585107800c04e500003000c80314480100400d05030100341c00099040207140d84c001062920140344814012103c4000320100b49 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 822549514 1250 822548264 822548297
    0x1090611010b030d0e1306031502070f1b05190803090118080304030813080a0c03060b04090501051015051306050d0e060f063f160308030703050a0516 66
    0x200d2403001410703039049880f1283c0041c145144804414072902844071b159040e20300c82e2041c0c1c0e040f40d174801e03102101301c21543d0000c0b000b50480e0506880032110661a130380001c02c00703902c507000342c01010f1407580f419050030705001495804200c1d0800c0424407200034400d0b000000103035200030070240780400380b14500e0200140d0440140d44071000c980720119010080220301005130a03c04049145d64450319a40c07d241e550b1036810200141c100b108219042c404600c10b60080da11424014001050552407035440a0848074200d4101c16585481482800421041c80d00000c01900c0da2408a04044c00d491203680c0503d40385c807505051040010300c03030600340310640101e2031401c180000e0341c0007494198805c000f40070003240c0e10b51203942c1e94210085144503181c0f040384100c40114055200c0c1c41000029194849090304e0b4040d68030943c01080c00a032000803030403000d5407282405035120300b01401c020702510b0028005803c00d9042008100d0b400c040d20b1030300a1503810501d000e04220490204 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 822550764 1250 822549514 822549521
    0x10503010c270b120708160c0f02040e0a030924141c1802010201060b0f09041a10050a0806010903030e0d1a0907050f10210e0a030f0f0c020109061101 66
    0x100c07942c0f85802141c0c6082041004010910613400c03a110b421003543c400610f00e0543c440002c00101003800d0140e28004680f0011088218500c041c0c400241120986002c0d890b20b04000e00840000300b940b0710500c001003111340140011240d500151038403d41401700038040031500340d030300724900c14040340f83c0c107000d0021100c1d8600354220080400c1000c10120895010081c43c4006038050b41c00c20301c0014171070070410304440314040305600c0c00e4203180d07650341004094160980711805040740c4c002880d07481c0d56803400c03d0440c0c5a46446d5030340e481c91070071405805030100410060501c1000607082000c42e0700580303200301a12007261006c0039250a8940112f500c180c000ea248440c94000b010404119000a0380b0020741d40102d41c0103054402890410901c0e01c0f43c0c6a10500140300304500014100c40c01c103010031100e076848000704034007240402d4286800182c0c41c0540004010002c48000980c020703855058400d990310302041c61580640010700f61288522801e02081031990040240e54429070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 822552014 1250 822550764 822550769
    0x40908030c0c1002030412081303021c1101060b1c020c030a08180610050102010608010e0a020609030304030501020a0306140405091e0718050103060c0f020c06030a09061d06010503010c27 82
    0x1046480c0d003841d0401004085031f090040e404542c1001c08129405000103a01820590550040210309034151040c14181202c2403203100348a0550f2261803c031800303015000c05080c1c803c00054960000e41e031044810043e20b10202c1400b40304000241034158003000b00c0740741032405e00b000e102e10b884161540500c2180c40a2503100343c0650301c14481501c1061502c1012910241c0c02400525201c80899007203e24202d082d488aa0080c000080141883d40c09010304150040541c0c1c10190b4980b159400d903440114a5000070b983c8500602000710440c020044060003034030300700068a03013008501d540f2040c08512581c084900210038151207000c03c03410300a42200500100c8281d90a00b03104054402804102d602904003105022080d1090302c044654421035030080140000d0b004c18000c0c0c6500240420b06465140c0381041c011130b20328040c0c0002c4440346100c60000840e0f0007030240c03c0041c184c0145200342d04101040c070a96a00401508a00104407042c0041d0205020214240c0f10941d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 822553264 1250 822552014 822552043
    0x506150a03140601030b06040e060103110402040f080c040f02090303070b0a0605040c020313091b1d041d0d020c281208270603070302030a0b1207080705040908030c0c 73
    0x107001002d85003a001c12007904880c492100d17046c95861b07410411068809880ea40903055104000401c04150010300e440280700010700014605501c2c1c543c08404e1409a8120544540c003444200c50030f820300e4481c0e85400e038240f580071420017402c1000070307403a40300310b00700a083e452030ba0000c580f80440a6000d04010705000f80100700d4401d4115003c0c1d2250003190f0b43d0000708130001030000707a070489805222030800a04940301c1902942d0074007a2061200022070540488400d42480119140c51184440e5004d00c0112040001000c258592800d200310741d150003150061540111180c462482403d80200007109a824404108903000d14044043d80704c1c40b2201c4000c0010303030510011301e000f85040d0b01455603244209120f02410700060114078150741d0021340400c001010341e44280d02650300110050b4010038140e65410015480051005141c401600500410000c900003000000b0044c070044d1070030311071075106c2d4403003031400e0000400c620042d4500264580e0a640706120703185004a01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 822554514 1250 822553264 822553283
    0x510080706030c08150105072901030b0402030d0905010e21030a0503040b0121060b120d020717011503080304020613090b09070315060e03072616030506150a03 70
    0x240c1c80c0c000c002e40b01e400082404540150045013840142c0b9410f0000e1000c103841d518a4006241d07103540720609940f1007501103002400d0600e03448819600280d000398001d07001c41c481400c0900400d41860141c403420002c1c4040d01700100043d981064200041c24022586001440b15049891a10222000d0811b0450100017070745844690071201541c0158003c52400d8101d0b0303214907404010403016a0941619039400d013050001440d1600001e1300c00ca030140c11540010461007001349084151150400980c001d2003040c49020781441003078010f4081003000380024503070300c0340d41c94246456000107808800008001020342d00e80f00c08480501106450b4515190359440c183c000509510038518842c50400300424101d9229000341d0700c103000c8512415200519240081d284140c1c1e480140f40c040c002c5110004003109000460301d10711040740740c2c00c146500c14005071428030351006861803041c00301c82002e10104000180c99a44600380501020091118200080d250312f50350380006c2c4603801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 822555764 1250 822554514 822554519
    0xf2a1202040f0f050a030503090415030f060507080702011406061e0301080a0308150f041a0d050604020a0807150e061303060f11030c0f030a020f030f0403081f060305100807 76
    0x6441c00b090120f404002882460a0b03e036000c02c050461144009800b550003800180710601d03040e40101d00300541030000807499592540c40d240d00c0c03032242000b0f070b86059556042012040d0062040f5500100c0c1c0c0c03008010010201c4c103840c81d0100d01510b5180101c00101c0c0c10401007803000c081103600300f400c0e404603890303603560b883c41e9944911a860480001e58201c010520f1407104040c3c68042043c01010b42010400500030300c0000c00c00042c84a42d140b907021940b0380180c0b01e420090210314005c1004d030200d454540148650003180b6400284654002c6608200e02401d0024459104803185001c0d00d00009950024045009100030113007040032032000002041030651098800d00d005607000c3c4915401c6100b039081d1400119069500303103004022452684c0c6a56004540c8079241440041c01c00002a030004c0194100702c540c140c210030740b801440145500410720315800301c0c03030041c5540011030f0b00d812090011404d100c1c00c01415241d2010400303e40b29104824050031391407044072131030765 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 822557014 1250 822555764 822555779
    0x51005010b04171f230a1416080c0315150315150405010f030f06080c0a1e302301020c0615060f0403150f2a120204 51
    0xc0c00b51050600000d80d5180805000c440850300741103c825982401e4a2442d20f4000c040c00703440010701d5000000c052807100d4680791500084940640c3c90b10000160300090101c91106040c0082c0c0300000c000068400e0345400d55002c015543d1244846102c1c64582c3c540880c91010130001c461000e500061811a84001720303111405140700c1d5401529a1780d004030520103001e2000015010180c054000300720500065000380b254241000182c0340025050754614400403c0390403c1c0c20460054000310003029075071070165203002c0603110004c0c0220410398034610201807101c20340f08100c0da00050140b00204101030014035801030b45243c120000c909014a08410041724a903000042000303940750401c283c01051099440c901e003030200501140c0c540c81c0301401803081c0003924940c40300703040003000c0018683e00081d200551084064480c8008604044000d03145c2ca51010440302c0e18280c1c1d4481d071810304071201c440001200520b6551581650b900722405485400800660b60001074001000d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 822558264 1250 822557014 822557017
    0x403050f011a010f0906031505040f0e010605011d130f1404050115030203060103060b03190602180402030402180406241406130e191406041103010b0d09051005010b 72
    0x155142940d010b00d41000300c015155042458503400004007164020301145000303030700150b2130b500c02c107107581c003102c1d030300c1c0001015940003d40e01407840391102d0312400c406c1c20900a0402401c42400c0a40e8058080300110658520341c02e4054410502c0d081d002c1307045142988000840011000e0500150f000300c2407542180500b0f4504a40380c0d86000c207400e01c0c5c800c2c000800420b896004000d022030b640307192107020103013503004055981801750111414031101c2c030f0421800d12501c610800750b2185464180c19030341600d40005a03000314010010040160340b03102c0491000307603600300f818090ba00c43d070420500500e20361003000c0c3c0c10489411601c451780c140150381340c1103468044500c0900390004003804013a00540b82105c842000c40001401819644008140d103c8805130348003203c5240445a24181c81011079001040e807200c1082c400b1504060283c48940252043c6240c40c40d403600500c14018071490041c1541d07181d880450404000d402c2c070400d48112250501070143d540c580c41f240c030b40c0d13 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 822559514 1250 822558264 822558281
    0x330a0308030613051513110313050601050307050d0f0614191b020705010f020c06030c0301170a0309090c050408010207120807080f010b0f1201060302040614041203050f0403050f01 79
    0x14a4918a489001c80402c2c050305100d01441010030856170b0485080c06030401610107518503040d1a01d00c0344070900c034154081e500c10046911001842100c3d401c0140c140311040c1c100718041d400c50742040c4200d03107544c00300318209540511102191002420400010075840d500c40c22842c900c48240041c0801c0c900c030f01c0d20000944a01000344000c0340c1d031a10f03c07941c0100b44800258021039420809036006031200020082180190b801c0c031030710360000481035030080321100014440032005010100d0b5214910b0445081507005040c078030000e450140101d003683c4540c1c501c0a881c1d2074150121403042044e100205000e400942d100c03c41881c1c08445040000c3c444000606444000780c0d80510a80055002c0c2043e5043d0200d41d0b42003003c0c50032503600105203040903010802070640c5081c0b504081038000c02407650010703215030034150000c00700ca0050b0022030380000c0c1400140007105064000030341c0c6036414185640d5070983c05080303c00c43e000710f40c8090042d00590076274074074040301900803d04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 822560764 1250 822559514 822559519
    0x2c0411010f0206040b1b040306020c0d14091e0118030f0519120806060705030d1a0d0b010e0901060f151202030f06130b0d0f02090f330a03080306 64
    0x10004010101d075124003c42e80603103000e8081c1c0100320202d000320840c06c0f82641030117043c2d10701303500e0703846050680c0d101c606c4d1400d550340104211080f01c2c1d40301d43c02030008040103101600e408580b00014088071418440c84034103900c06040508168090044035080441690140100503600c3c1041400c11303c1c840c5007920340e80561142c161041010205480300c2c01c1d0b01c8191a880c0b1151500c0413980481c000717081e00e800003401c21a1502003034007000a031060b618948408140e11a880340150002030b02001081d00694103041c111000808140c1030030f040d01c44a94140c0996920302c16454003516103a030026401609007000401c0c0b4120308601140c00b805507844641442030a1940c4038205c0c80b040303501d070068042d4080400c2603403a14551140322181011000b0490208690000e00c41e468080000caa1050f810840c8000b14103103000344591015444c07080500c1443d280141000045e0300044c1c0b42070a08500f07d5080500c50044140b04c0705d4940503003810176042d00d0745030014250b40140c1c6e4061 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 822562014 1250 822560764 822560777
    0x1905030705060a0e070e22050a060c02010209130b03031908010f0f1503051e01060903060e03070203060f0403050d020a0504032a12020324060901060305040308012c041101 75
    0x25100315890290316000920200240141441c00105006e8058094660f0f07030181022071280d40011b0101e54400a1980140f0182c81100e11520300041214903803491a415a4018818401503a96003071070780b00440b41a81d40400d10041d402c00003030461281d00204c0d2000500c0001e840c2d00558840350355410383e8521084090341030b8440c44503151820203403080400210040d074a02500d40e119400050700702307041c20126000664500420f030782001090300608009041d0403c100705005190180b01c401820f454080c6141281c0c54000c281c07241d40040001310040c49060106040612540840381e540404020464407803466a400500d154000c1c03000f42c65200c00051078006800b510100f050541d100740000e501c1441c50010041d0000b502d4030070136a0706009004181c4080d03058a001d620100380d101601d00d040d4a460401c1180d45141a000081003500d4841000000703500700103414152040046803004150349507950354070013103540400609543c40f060600c020003e00c00d05219845109032180e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 822563264 1250 822562014 822562021
    0x1003050610022a0103150321080915090a0b010e010f05011d130b0a18110315040207080405100801092301030f030c02090c07060606030501150f02190503070506 70
    0x883e919560078000180f0700d049070758511a40411140204000c0006040c040707102a107881e000303c001e21166105030b03515111300b09014080c0840300460444d4581034200074142d4105007880f160381d0790748510210401d80440340441e407050000c1250080740e0b5408915480b483d0386801c3d850002074428400da2054000d4040302040642c0030384100072500003485160f0780c1c1c0e42c2d05001085051500c0848000c1d0031035851440b0800388e00e0754141c110140a40b54080e01030803121408000c01c03a4072014a042400000384203101c81c41c00741031902900c00c1000c0364050f0b121060750610744554425039000340d62208110311a040f519030041407050498484500030000c401c080e2404090452420344101410710011005100003072039422586c180754002d00d000104042603a01041d19840103a403100300c08640400c00d0000c00c003050090002406162400303101c00d500d006031403480301501e02c00c0a0140414210211a000d00c2006449116800e01141d50780201041c04c0140d101d5101420640380c600551002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 822564514 1250 822563264 822563267
    0xe0c040e0303062206080303160e0108010902070602040909030309050f30040905071125050f12030a05070209100b040b0a140d020a020d080c090f010e1003050610 71
    0x8000190a04401451460740c03030728108203161521102c024402130700744690070903285992140c680540100e0004507547d0510b81c00c240e190f08942d1019608115007070391b1008080c0d070f000d580b0a04492902001580365682071070031202a01607504001c840c10310300354199061680c0740d08000c00b554020400d6030404805100000e80f0f03221b0070104446001c6c03041c22244501001103442070000d0507500b08407418607442c0c4400c45c0c180c030b40030b5402000207a407101c017000c044007003400800b1200b0440ca2a543d0321489001910243c80c0780752045502c1524884014411900ca008410103c40c160b00252540c4004014018040b43c001c1c00c8181e00842e103440019010b0389540004d0320584000303203205424245004c003000c3ea294082c10142c2c0820100920102c22000309a02921100090300740c0542c46000a403030003031a06c4c03030176403250040082d21010301009408a1089404200003641c00d040825071050050342d4036800051003e4002c0c0108030801c1000c3c1d80359008074002e2004440004103c0a100d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 822565764 1250 822564514 822564521
    0xc0e060a0308090d020319060b09010b1207051b0d0906090b030405060f180a030504090f1a040b040204051507051207030e0f22060303020f0d0504030b07020a020a03060e0c04 76
    0x100800b00341e000c000300100c9103400c0d41c0301001a0303c01030484200d9010141550001c11030484103c5000c1d498080d54260f610b4495815405041c150003114104804140c80740042c01020304440c0522800140c00d6440d644c56402040344280c80b6011a1041102004003c104295070f200391070000b0a410408585510510b0450b8003543e0448010852500d80b0007a00b5501c48010301251000c5010954580340000c0502804c03070325134002e44990713490b03074540b00c6004180c921004040142030314008109445019141060a05e0041502e0000b110006c00011400901c80c0e034204540c00102e500810300003810b00c10060020b14420000d6400203a05002c50b9691030041480040c046450400000310a003069042d2030151000281002030b09601001d40d0f40d0003401c9109034074401c40d2160402d01c18190100712489a00e08048014480070b034842c14028060b018034040240119002c10210300411300c2000120900d5400424900d0407503600e240c40300050a14100e50b0070749000340481030420745828403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 822567014 1250 822565764 822565769
    0x40506131506090f03051506210a060513201201021201050f040608060a02030901090605090327030a02060342100921170d050115050703140d02070c0e060a 68
    0xe00400000c0b6500c48811007a2400818050700120980c0852100900703445210284014000190464030700c1400c10a00740c33400205201800c041c0c006001d8000389a82241d030380100a40c0490401c12001c082c001807594055141c045003d41c000b003230303101300d07a100081c0c4281202c000705c851903491402142400140c91541c40741d03050b01d4100100040e101d01090f0003d40e44a5103500000800385255a10b0b0000c440703081e01d200b2425440400e2088030061001c0007039520040c6000101d840455000000c1e039902c0d00880d000340034403004404100114110340d088510700e0070001d2040d03084012a8809640c261090000d2030151090492142040c02c000440c20600450ad0341d86030381a0341801400c106c00d000038500007d50710380301004e010214115100c8030180c009051041591100702c000c070082504d070182c006403542090110b03126403181d04071040b07a24560b07160030301904801d0b41d115550020300911410b00806400000e480040025100002099502600d00c2c449291201804c3c0310f6030108a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 822568264 1250 822567014 822567023
    0x31006030b06090702010b06070b040b0604051501031806050106170c0f030103030e0d0b0f010f050307140103360b0f13021c02060409150510050306040506131506090f03 74
    0x40110b0803c1c2805040558070a216000124401c481790f00400c8a640c0401c005440c0b80610805000c104040c0c0080542c00c000b080703900340140c5c04c04800780400000305c10280c505041c2d43d054100d08200d41c000d040300d0741517000341081145681d140005481880d0100f46000b034001000001814040341100780ca00c8450340d40103090a50f03003159411386e80b03200320b16441c40e4051000400c65000410300d0f0b00e400d01c603c1061500c1107007945001c9200022010980000e03100e600040c4007480542c4c03484040c950070000910300803030026200d0192002c11480320031008000700320100868400a40b108010024070b1141c40509116034400002c8080480260f8a200a9076910406400545041d11041010711010032400042c000141d00107005a800b1303900c0004103941b60101c005040a80e91100c2c0c0041130103a82000c000074030320600500e24030004081600c030b20350f168003084031910340900e5054400500b0004020300c1150040c48007101901e0310904000440418001c9040308404582c402142e900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 822569514 1250 822568264 822568283
    0x70e06090f161101050a09110a1206020f0408070b091305010503031b01020405030f0106170d0909050a0204030818030f070503070b030c1e0301061d1c1407090b03100603 74
    0x2802c00c2d404105081c41841c8080040801d51503071500001e12420340602c1c00c813000081c140c9079500c1e01e18070351a00130740854031850005200304800703040400c001803040d90000c00143c1d10a4042c00c01d01c414001c1d5040203100748510340380406e2070f81c01c850052150280440700d0001c415403210001c07042d2402401070300e0301600180801e6201c8403207180403d100c0e90007603002504158698020916104101018a28070782d16140304024802944007803091001510002d0100880358200c0501000307400d06c00c69000542d90030002e000116140d060320041c5510000c8180d5601d694441d00080b803030203000322031103400340b00c0d401034025000041c0340742160300c0a07014251092418442e030711103400040401042010030004018400081c00207025408810b81c0d4064172541442402440c01c822046c4803442500c90030100740103a07840441e0074901054000b02019003d0003440c101412218000031808144903c2001040c07084158101141215080c0d04807903000d44554420029100c252101400d2800c2c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 822570764 1250 822569514 822569521
    0x31a0105010c080a02100c0e1915260103140f0a03021c0c02060c0604050d030608120703030b0415080d031406241306080a090528060e070e06090f 64
    0x410805000b41c04005e00540e0b81038481d070780004040d0340d48586020009000c03840124014503203c0000d048a4900c880220496030810303908100560500400c0307018010170b03003001c4424000d51840d668011040841c0404556524503018139600000d00c501d0049000326242c410303d05400180842e402a05540104a0960007119000c03a160182000000b084181229030025072690001060300600d244014111494242809801c0501409101d0109030910200304810341c400a10240310840e43d00201c3cfd59480c0704d1406400400200c00d9054202c1d090804000600314110403040c100d0b52140e00341d42c0382d59a0148210101c45d08001000300440351080441e00c5810564080c030f10942c060040b00d1421001030f00b8020964011070810600300a07400c005009180e44094042d400c00c03050002400070205580c0c2e0f66844404110080d0b4003800798044002110701e0820203184010b8005004003d0038000329402600c1e020503015150f103c0c0c030070f02e01148040c02c04410030383c07144008100303014440c0ca = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 822572014 1250 822570764 822570773
    0x120601090503030711060f0d05040f031b030903031d220b190e0c0937030b18010209100201020306030705010903080304080a0c06020d2324030114090601031a0105010c 73
    0xc01c081800212400d0601c00004844000c1c0702780c074003c40c02000b03903202611035480d00610000c1d015001441c0c141c958401640020740000c01d08003920741c9410000b241c1da46410030998061924100380d40d1014407007244958081c21a8800c4c02c802200810900c1130b40c4940003802490001c480d000a4054500c890400c003051447c500150040c6008800510b0710101030001013400450740758986002409240006018141c648226000e00e0204040d03d0010b1444e2590584240c0c01040b150000e0070305507a070080c0341001e50446100c5a0020200c80441c908070000034000e401c2124064002d1091481c041860341c060520740080b00d40c048883d078030b195141e03901c80000303401c546c0c00e41d0103101400c000800081d4190000d00b01d003481500001901e101110340c1481e2070b41403030345d40b40307810401d9106010130804010500d84640d12000644180e100444001c0b900401c2e4040c1c0a40030350341c890040c1b001d40c05000c1a19030480303014502806c807480d1041070950081c2c1c0c00380300b158089035000e6000380009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 822573264 1250 822572014 822572017
    0xa15080c03060d23071d010e0c1801030b090a09030320190909110a08180d0e0a030209090d090b0901121109090403050306031204031709031212060109050303071106 72
    0x2400312081012940d000300010f460300700709410482012469244c6c1c0d664104c0740c802c0442c01072004100c0da4080c3d0034003000d444414401d1403803055018901c00c14412050b4060f411043e00c03981e02401003101e41c40c0c4603003070000038012054200d0001b42410185041c407035001c902d030b000d0654008192850608000040902c80c480f1002d9a4140a100c0f840003c00500790b00c103250741444140c40242e9a0425642d005040310401003000b9000c6131600c1c55542e00a42c006040384e0645c2d4281400080001900700061128152380d000030b42c41103800382080001d41c004034100c44074007815103e0554442e00d840040307580703000f210001030015203030703218194400c0050741142105c03030b0079410480d00c0e100b512004151988000c940580c00715100105121680c03e04100c81c441100200c5a42400c0a066541300028115103402900d0380700070103e6100035680d4207100202140504441440d0340d001140c0d43c0d1180c032601110018042a8070038000150340c100801140c068a610005110090714008100502c9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 822574514 1250 822573264 822573293
    0x1090c09080d0c12080f28111e0408060c030601110a050f1207110f1f0c020f0402040602150c040803040803040e010b070f060c020c0a15080c03060d 65
    0x208200c291000586000c00e0001c003015451554415800e015541000000c80c0807200450303040051070750030170548080c1c2c81c0c41c003900141c2c42402100108000f5900075451203400518152041c41d014813203040d000307440010109402250641154042e5000c8080602c2c0291303c54000c080c4c124400003002d49858100071540034805052049142540703c054600d4104c05600c112014ae00c504c401d90403800c0200100d00d4005041c0c82c01e10314020f00c81d07444041044900d5000740c01030300c01e0100e0000360b5a07203c022861303c51405030740240c10b0000b454000c00742800c3c21400d82c01080c0c1c4500f4103450341098021501a0b03000307500280301031821920f41c0031001000510740321100c642031001103550041030000f04021704009004680301d5003000140c000caa001070340700c10203103941000700200003113081c10340d405800d4000200060350480c0060a90502c22a680f400c0d91044a04501013003810300c00312a06100c6200340e0702e0b114240d46841040500784001d8520b01d60003103540c031408000845184034000d6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 822575764 1250 822574514 822574517
    0x706050403031820030601060f0c06090b040c090b06031302010804030909060b090109120302060f1329160801050d080d060b0742090f0302011b03110301090c 69
    0x104800024105600b00e000382c2021100755010003130703010038100d03014070350b028050080740a0402549410405096046c80700c0d065810301004030116018011360358425900b894011064024a207060700e40407540c040f40d03005000c2c00f0785c030740755511104e420620140d0740b007482c0c020b02c124101d07829038005603200d000c020b00840401041c1400491840c4850007a403004140e0a40700c182c0b51607400002500d40390450f0000912075400151100102c1c0c1d0010b4141e0b08403594440d0070080d43c44600003502a030400c10406004031707003900244d56410040412821403011850328025003a211452601d8524508003201000903000000602c400d00d00002c1e0030380201d1241d04242e182007612a201c0c815550542e2203e8040580801c04000780901038441d1100b00b5010180310901314203040410b00e5060700140b81041c40700c040359014070002c4955001d48107940d0811030100c401c0205107002030180c6003100315407200324650303d80b544103075002e8010245040d82c0d082c112811a82050708000080c09441507100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 822577014 1250 822575764 822575771
    0x3040501051c0e1f0b090c030714070611070317100e0901091407050f220b0a1710061508040b150d3008060d051c03090605010501030204050303070605040303 69
    0x40555400c00c0800d03d5840c52124044c40c40340c1c140784100c1200e28540c2d09034003442c3c1a070104404134100c9412281c4c81641030600340083d04034030718502e20038080c50300d008250390b03d4140b21100414001e000350041d0ad20954444c2d4480340071265409402a007034076084100215140306201100b010702d0201e90180910000180203051600d491541d00800f0515180580024500303101c079040001103040070300c0302590b00c00340801400c42d607504015005860004c0311030352607020030300d02d50b500c544130002030803429144d8500300400c0c41c5158480c601c500084140919140d800105400c05060000502c1c0690701d848640ea565515180c00b5164000c0100c8440745140c00b40302c10580e641002c26100a004440032824100340c102020070702c2035864806004800610804420250301129440e8007480a80e50241040c0203450002e00d0843d4041c3c40025480d94404030a4900e075241e070080304075500401d001d1023981da8600064080340b01301c4c002c02d41c05400800401021501c90341006410610918000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 822578264 1250 822577014 822577031
    0xc040c02160b03010512120301031410050703020d062103180f06050a030c020712081c02180f0d020a0b03041401020d0c0f0810090c050f0a0203071403040501051c 71
    0x41c0c01c81608065940341d0040f005009030309000c0c9903180c080c140390b802800414a140d501c2c240c14001484000c24046104039100c031012001c1c080e118820b00d040b4418071590030b00c2580a40039401003440082881d03d0038070001080c480d041010005800c1c40f010b43c0b2404203043c2c40403210202e00381116014043c4005001641d503101c2d202540040840f640e40c191603104001d401002c0e01c081c0103030031046600c000f9050004501103111246055403000b031a640d22240c500054020084c025180030b011440803d0b000b020300c08001e1180b008500880750420240010310811104244d001b80107904693707007103c10300c510001c0100941d0000d0181250b4080c40b8010107616099074014408195190749030b111000e500c1383c102141e94150402030400c020b092515160428180300c00340b0803003044603100d0360066241ea000383d04a4600502c03803204140d0707400301c18001941c3d0341d00c41401213400071004075203d48911808410798060303a1050759000d162095034400301460860019200b4070003581c0300f440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 822579514 1250 822578264 822578293
    0xa090e03162105030105060a080402040e100e2a06030403140423030d1d060706330f06031505040504060f050c0a1b110603070c0b0106050c0c040c02 65
    0x88800d284030314001d42d01d02c1e45090700c11141c4075001c0807110030f1290500040c00250f890b101524140c844519105645503200c2c00082c0c090640c8414045a07409403626801a400d01a0002c002060141d01214000400300c06200e0642c189503009500316009d0700801c1a40f45410340007035030400d0107807609041100014000a50b6a030081d8880065041507041c0c65520a801d11145915403c00718060001801c08210160410b0750740c1c213492610000500d05132442d50340b0340c01030700c9110783c20240c10801024000d500000b8000104000c0700c80c8a1550031a40070a010003070020251004444150380040c40c2103020b0b8064400c1180148054918040128450700c40b4480c0520460250802160a07420000c5400490790701500c0c84408002c100b0128243d0307500010300c00840b028034001030f40d9a080c1d80c240b0101140081c980da0b50700030350000521554035407040300509270074080e0301007140d02d0341d0703d560035500d9109900c402403694029001008140c54580e01103d2040c05500503984e5a4480519 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 822580764 1250 822579514 822579547
    0x5090c0c060f060a0605070305090f010302160b15030c0a1403071a1c0b060901180e0c0c100b0a1707051005130f0605030f04030203091003090b060904020a090e03 71
    0x115040035082c082d042290900c3d12210107401001142411481c2401c15140105075102d001581e90050525200c4000030740d00c654110f44e41031968040d805041c0d1510311f4200380c140000e4031401071302045000d24190354603008c0340c401c0384140c1c02024030518900d000c07a01d070880103003414415410301480c0400149000242c80d1001403800d100456940e648081400c0311891824a000c1c580b40303460408002c005440d448211000c2c41c000b400c2c8114244000c40665600361015003007840308910b50000d02030807400100260144607507a405480d61062140c2c480011286041019030740000800701c200880102c0d1a00c91a11440304000d81e04607070b44410110f00030b098001d0010000802c0080c1c041410110700c042c03500a8414042244802440e00700c00404502000e8908694180c0c0003003c00c04050003001100c03403011019007a01c080810701d480190090401c030005a0748640c610002448914000c0f00d064800d0b03500600384a001c0c0c1c28200400001e02203c85259660702c010007490400440032403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 822582014 1250 822580764 822580771
    0x2070612022104170a0806031006030305040b0d020403050703050309090a050c16140d08090d03020405030c1c0606030c15033b070806040606080d020709020928090c020a080405090c0c06 81
    0xf12403211b9403c00606061903c1501e444000700c241c540482030001942c8502210b0880312442c0f000740d02c0d4200c4070581c20091003541c0c0000e00c60f1103414400001c2003030100c05013070031010480340880540d0b42c07103003e40f066079000c1710130300700c4070000b00258003401400130111405180030343c2c0313a6152604d104e11441e00c0c0c041030355020b0b004244c07034508001402c03004001c0800401200c1c90154201442c200109940c2c000d0300b92060300c10b141c010b05190b02c024855200030000d51300304034140302050b6682086254030f400d5010f0001d8400300e80300d4407000c240c040d014145030798072030400c107500480d0025103030103000003240710940800210074280c010303c0e001045020040c02441000c0e000c64181303498074400311041170b800502160011072000101a030042031000c102d403404078025075110005000503803840702c00200840c003e0515440c40c4441d6451072640320540308022000c1100f150040002e9a80e042d042900a000850800c02400395040003c01143c000030000045070030a100004140e04000085 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 822583264 1250 822582014 822582017
    0x80d02060414010b15030601170109090203010605011b1407050d080910020604020307090e01020d0603050a171602040e0a05010c021b0a060807030c02070801060602070612022104170a 80
    0x10062005020030000c00711091803462008101c2e1682400105c0d00a440180500c80703000008400508140d01500000f01c40c0840440c00c11305540c1c50b040e03031000504020805034041d618148000c41c203540161885980850243e21325121000c41c2e50340d61035800d0090782c1c1d001d01c0d030140000010341900c664140d86c0c0150b11940302c1c00d80391703000b150030700000109000d0400e0855014405000140c0c8001c50140c1c280d41510301d001c81c5000210030183d01a100b5120507031185840e2003000014010003183c4150700c94130400c40250b801101d801914000e00031701015425407490051a40c3c01450150300040004061605654600310103884007400c40361055915805a044104625040002c0c00351414040000711840848a41045401400c512000b0001c0051560304c564500d585802000400001e15240c8000e1042070780340c1030000e440b080a441003401081e1000162540c80f0200c1c000d90354800d402c036400301c000365211070184020381d0740500141c0f00b2280d85c80740407a004462200070103914019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 822584514 1250 822583264 822583273
    0x51b031005150a050a08090c090112050d210b040e0102031e0f15130e060c0d0b01050301050609090415090b060f030102210c130f1518091104080d02 65
    0xd001c144a100c40800b81c8401c4400e000300301d803580080c0c1010559025940524116000f581c40f2000103141c22030001400342d001d500079000040e544503082d03954040c0c62140080d01d80350300605c042519902400e20108081201d1461070410001c4a40d205442c110001000460b4102da6002402c1c2241d2050b6040075140714800f00d0b085a1180881a15400403091808480d061a1480ca0006050307051030794240704e9030032090920109266a040032001c91400020b507a810300b0004540b80c03040d40008507956029080c2980c0c5101c1e50300400a9904950010389203a2030002c0100400020410080086802c1c450501200c400c80005100b503084841c440c030740340b03581418107000f005071155078400c0c510301c207078010000e40c2a400f10035855994500d210342c402c10200d880d44281d8046a00a800303005003402580c003000203c0680c14440541107401d032007910b06600076808021141e18082c080014400f605549041250801581c06172001c2588000c0560505890b41429403c04004058000045c0c6c070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 822585764 1250 822584514 822584519
    0x9071a0304030320090d020f2d03070621110313150b060d200a0206150d080406050924030f01090203060d0803042d0c0602070e0a051b0310 61
    0xc03d8850b44546503c21140d9075400ca9420b00320350003501c80c1400d0140035046c0c90042d141151100d8069080c0d8a200030400108144410071450480342007510000c00600d0211b0400750301c0c02d0210b0224160740b2969155104120f10a010440e8010741e81d48450103d55500e0300b825858001101070350082803203103c240044100345c00c281742c0c0380d04511203010700e051131304514004603a035460840c0d03a02c52001030003140c0c2c441c51440d0761041011108200080c3d01c2c0c0040c061100c0d03580030824a00c00c1c07202c3c06040c00702007459000d12104120f2520000d0645408100074020304d4090000342204e800c0040c444840740c0c5030104064008a55650622506400401032090b2111a0341c486400340000c1031007107003145400710001d1280511810060542a400000b140501040c8000041195026000241021000c041c102d003400301096068610110459001c29202e1010801c3d60031521f43c1039412802d5191008510024800948401d0b80c4d54541d030b010035400c01c4103402862050003001051042c507171 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 822587014 1250 822585764 822585767
    0x5030405040e0f060a05010b0415140a030914011a01050d0b031603060506091027051f150c02011d0909010204060306211101230403120302070f0b09071a030403 70
    0x640c0034045440c02c46c141401840f0740c21080e02520201c41d02403144102c03035500e040040d54100c8a100c000d184221300001d01a03e0190560044242d02c0d1060941c0308803009040c04003402c0307442460010703a95852100441405611942c003500f921b05140c04002000041e20001070b16042d10a0800350b00c02a400301c00300180480e40c070441d40c1c007101c151020702213881c00924400c1e0f00da50340d000b40d003840b400c01c18080c0e803032428058000280d00002c0504000d1414440001108500c0d42a400100d440594401080d00c1101a2032140d1500325904c4103141e080c42075005640600c100c9a0300907940601da420b940d015510546101d0003204117800059560b420020024191004d03508a200039440c01c58480c002031040b6440f1405e150b030045030000344e05c1c2c1074100484a8a9107800e40d05010700c43e43c103aa6501c8600c1c58001c0c03040b648030701c40d80940100508020b505034002c030340001c2d00d40c80044203004085540c199500307034012722030001d440081d03480d049410300409505ca05403c038520040100410107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 822588264 1250 822587014 822587023
    0x40b0c24040c0806100302060a140315190f09020d020d02070f0210020f060a0c0c05070f061d061b0f030408060411041401090f06030209070806330705030405040e0f 72
    0x90803c000948140d04e41000c181d01c1140441c0b10086c040c50000902016183c0300b5500501003440071000503036281000c0246040241109006a01c104c202100210710380326500a0b0604550341c8041c0b90742c0091509014000075004030a103400748907000c003c040e509a03850b100400d4003e21a03514604030240d1801802011400710f0300c004203642c0500c1340180702000001e201c0394460100741010680846a143c00c48204000050040691080740c1c00810b02c003010008203c103070368041d0785e915a103040c00e01c60450008400e2400c80c0e0400700c100005222903480e03403644007440810f5001c45110001c5801d40c1447e503030155005100582046052008101405100e0440f280c8100c905006180c952003441c04034400601ca0700301010b0383c882d207001e8116160f400400042d40c0041002080b0b19004a000d0a0001d04682143c440c0ea900d0700d000560b661001d0390f80d0503541001c8102c3c1030b0b00b20301c20b012403540c0e07111030001d13a40f920041c03000043c00d0341d40307015101c07240315010007400820866004103441c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 822589514 1250 822588264 822588269
    0x3080a1b0b0912340506070f020d0c0c09050603070506040f0e06100504150915030e0607110606040914033001060e060a1107080c010212090303040b0c24040c 69
    0x1035510030010555500100003813603550303000d69507100c40719035540203903906010708400e00104640200420820b10075000810050010900d07020390301c0b41c002c1c0c81d000b110003402d05440100507c10403403091041c50f18076880a640041c01408454900d51502c0024629402c1a4041640b14140400c01c0c0110b01000d006180c0207082684d00d0010b100001c0720140c0710303011302e01401f12540034118070395140511900040c401098440803800c900c0c1c3d80f07803d00030050b0024800300f9500380725207801308040f41c0c4502031202c0c9815498000d003449403541420000130307201e5050181c9104840b48a007c0b00400b05000801c5040d086000d003d00030242d0416018800c0100100600700d107024100400c206504108022100e0f0300858259540e02c804000980c0c0240b0b08551541c4a44070385400400d0f0342c0f500241603d44036509800b218401d403404a06803070144503003528140c141d00f00380002c00440102d0005400d09280080c2500c50150140041c4e9001004a00900c21080885000e020500610803d076102 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 822590764 1250 822589514 822589543
    0x307080901200d0e0a0c05150f0d2a0206040b060a17070e0c1804050711010222090e0c040203151206060108060a050f090402040f0606080a141003080a1b0b09 69
    0x40346060f40c43d0007241c0d01c11b43c82114000c0e1441004100c45a6400342103510028008482e5a10b135201050064010300410a90142c483c041410a400865840d0b902d4000c62032a0390080c0010b650b141d0311010741070340180801da0000c40e52171021030003186100b04e000f10a80c40400405caa14541a1079003c40000603012503140c1c00c0400c66124001c180302c030128004038081c0c03400700740e5031107946003114611445404e000e0954070201d40c4506521a521126208881c41100c00105580b18440032085990000d5000c0059100741155402e9007040d802030b40d8402c58101081c41d5038108800440d0780d0700011041000c0c1600702c2c008105080d80c100d00480d4000c1001d459140800c1c0c24480800c0c00e640e001d40315244150050400201107650b59002201e04805030981800b2007503a0780406410b449058542e103042d542415100344481c180240d24522803504001202d040f0b928603196403144d036001c1c69000c070821208042020f02c075240040707240e4400c1e1283c1004591460040402400c1a60780001c099 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 822592014 1250 822590764 822590773
    0x9041a0a09020c071a1b070b2a06090c1e0901080d0f0c080a052a0c040f05040f02241303060f06030b0a02090619050309071a0307080901200d0e 63
    0x38101004035058880c141040c2d074040b800024a06c08461070b00c45a64403008030300c1300000700d500c1004000825045858034400509821086221482e91100f000721010102a44200c141f16007903d401c0d80218502407103d500c81c0303441d00e05000400e01c7c20308240c211107030315800000b036802c48a80c0400c8042190410b4070380508a031009940d6040303684101044d110420130042440d041e201d89414000305811212607150f029507405450094036203154500c2c0c1485540303848007a01d4401c55034004c25109a40c404440700110705a1341c20041110542025484800003001146c41c0c400c0c0c400c8001c02c040f080320b92451910720300d0740c580181658008040b000381c0a041040c00c0000802d0081c00c6500800201030260b1103042c9a80854424010401104c0041d01c14242104195030890019401764042005941046c0e0300d41c010100603041d040d440f0018460700b00001003941e4441c84005400c040f91100100c1c1c1104c00109928819010024001510200250390710300010319200350711488002d41c0c080e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 822593264 1250 822592014 822592049
    0x20d02071e1b0e010e090f0708010f060504050f0106111609051602012906070f1209120f06020901091706070f0e06031303020304050d14010b04060b09041a0a09020c07 73
    0x1c0ea03e00006126045600b400e110114640c40010b02100c81c03441084803c0310034990b540e01a042c0601500420a06400d14010300410b00d824580901c0d442010401d583c0d4802da4a482001c591421101c03144943d6070003030407070107030140d07018220001c0103000c01e400100300c03400d02c4ca041c4103a0b0b01074000e942c000c2da0314119147c901072410010300c6007210001c4112082030100c0b0004129144a1010001d080030403201d004410000d04c100d450120f00402d9940226140e1640d2a00000c2c1403501070292484c0c0c00e0787c1080000440c1070b0000c11180c41d041c03601d0824580d41c0d00c0c00c9040040860b00001640d0031000c2000340880d440b00114840010340c1c0707050071600055401080441c4070141c109080000402c0c040c1040c540204101e030300800c0042c00c0c0a901c030070a42480d00940c14071242c45102c65080040e09080703032034a80200b10179070700080c00300d0b031519403031008110082500744640c80d40c02c00d02c0ca80020031592481c40c11070003444905d1025990344003911102c1e040c01e03440e42168a5282c15800c0d03d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 822594514 1250 822593264 822593279
    0x21120c060609040309080f0714010e0603011406090604030807050f032523060a0b0411090409050723030c030a05190516060e03010e1f020d02071e1b 65
    0xc81d41001d01510380102c41e498900301111824115046201a80f103011400001684c0c00120704045400d00c20300c1e5090007401c1e000464800302c8040c081e65020f0400d00060050b4080c544800d5015280206040d250013404e00206980d50001d6005031100e01c0d003c10000d0034060b092020041c0503112202452809e804c040141c4080d0403689030318480e40d000042c510301045000408001d405030001c24207034502500b10926a0740b180f084404240044c1030550a903498106405803c0c0901c010742403550501032080d0901004084101e07096500744500d000c0080c509194848206034130305a00154179181d207014040c1850540c4092090780030b43d20140f0a800444c00200d5a200600000e001010001d500c81c01c000740350041014254052003c54500002c07429008400c10f0000d0000360f00901c0010048040680c6a44040c040c140403100d452440b00010642a03009012100400500500300780c002e44495018800c0b44042507030000d203460820041c0f100701d43c0d400108843c070f410201c25241c00d1800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 822595764 1250 822594514 822594523
    0x150b130626010b030601030b061003140f070e090f150319020630071d1f02120f0408011103040f2d0c170a08072021120c 53
    0x4090801c0496000c880300d40c0c02900501e00030b01c0028211001541c407821309001c0503005646051051002c103288111860017030140307081040c0301d82000812644c4840c031100c0800d03070081504003080701840b04410709603554100075024031200d0004034103d18001b055284c10485202295100340d005c003280262030000711070541c85682d81940d41507111090013207600480303180b603002c18402c42c0c0210403c04015000485040c820241c070b6441520840b01000e00d034010f15040096590070002183e0010381407209901d10a841c05c0ca5441200d00400c0901000440ca07048201110090b400000301000990000d006010024004c10302082c035500f403a40c1d072a00b04641115008115100d5411801010040c0501540300e0300054095480d441d5000c3c581400c035551140146c2d04d501484035074003030350202c0009044001075442a4a0703813a00342207450795201050b03c61103401101078a924860a640c4410418500d0000b02c414400c59082c00e00306401d0030840b2514204034800d07414010201040000103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 822597014 1250 822595764 822595799
    0x5060903060406270f1a0411090415020c030304060c1e081f08150a06080c013c0201050108030f07060c270503070f030203070303050d09150b1306 64
    0x2000a112400440000b10302c0401c4c202440c0c0c800c00310f20f031900071311031445400301d5018494843c80d19607402900712818001d0b001c0c1c80161498049113096a014141091400e810a00506400c000b800848403540c0690307103d000c0b44001a00003100b44410803e0740d00584004805a007000040342400d0100311040b440000245400c111112002ca61008880d1000400d4101080500010b15440d01801966551141140b65a00840c1e50010344540c9051290805440d00c90001e80034034414a17004442d4903807000c07100402850710210354401d8203012451020048803120411041c0300074040e000c0c0c21200141c2c01000c0e41e420801006c3d4955088204071001d03a648030b031002510600460040701c254000103074442e10341050420f42081d821102c41c0c1c45003141d80840464000a84a0b0031691240702c461100030f4140c3e110741810300000b4003071405041240107232a2700140c81501500c4820008a080c1c8101c031030701d666041c40c59224104241d00072400c0c1ca0080c410300c1601d14000ba04080541d542 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 822598264 1250 822597014 822597023
    0x30e060f1c090b10170c0f1e0d050703030206010b0f0a0f020316110f01030618480806011e0201061e05010e12030d0c05040b07030f0801050609030604 66
    0x1546445003805a03400244443c1d0420554551440e00f80914202e14815005800e002985010044495400040c1c0e41a0215000c1d21000301005060140640e103241084002d40c210044000782180c2d0f01e0b2103502e00141405907005205c1c541c61414060704180701a00118030703510003004281e42d11340701031045507050380306454045c045500f0241d0403400c0d8019030001d6440404046000390030f00c60240300c214a0722800b200ca050402d9200c0c401541107401038820b07160344210b00b404a124501e020b030300c5600e14500b03500051b10301984200e561142010403000c8984e264403542881000e005650fa0b840054441c14208421039061010000c1c003988402192942c0c1148004070303e84c2e100e0f100707400200050540e03a4400e51103101d44944100781d10707075074040c49001402c150026003140c036102890081700104e41000d98604020814460048c208401000041c40000c00c80000c05c154148020102d881c00396507465088419264010003072034060b030040b445050107000c0c3c02ca142e64041411604903601c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 822599514 1250 822598264 822598297
    0xc030f050f040e0906100605121b091002060f0106030b010503130c12030201021c050f420f0109080d2001020403030c0302060c0708030402060d0b0a0909030e060f 71
    0x801000704840c421508a0b51201601c0c01c14880e040000040990180c000c003010006a1901d8803012101070007444d1034002d06e14001c101041c030350281150180003a6405180c107519010751603002c295a1001c1101880040e84250100b21f4195600400c4602400061800740884541c0c080020001c1c04043c040c1d58203c0b1046804108001e03d010741d6000411814260120018250030041d000b9008110220581010119114555800b510035248070b00001000200c19407241840d04c051541c100d4100383e446007659490380030030101d004101c0b40d0f00390712800c1104090791081c1071002c026510001c0d2414844502c00a004860700402c0700a906078083c03404440c820780156100e000b00c00001e0b1032500c19440081c0110605920031250021710b13000e43c0884205031600210059244a400380c050030044081c80810010b1410030000c04080016060104100c100c070000100c0380d01c4184e00104231286c0c0e800380081050703002000341e42414012a001400c12040b6502060140300c0d04010300041a103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 822600764 1250 822599514 822599527
    0x40e0c090d030e0f120a0203071d0106120e01020304060f0f090206090d02010c0c120b09430807080f010e060403030b060d0f0b010e0415030b0601270608070c030f05 72
    0x1600c0004d0015203a00401160561030010381d00c58848482d403030264064041c0b05400b0a0a14a80441e6003d040c05510307400a140c2c0303492012a4640721214003a94501e8492419812414007400a1401503000d000d00040b140242841c00c0c0c02c031030b41c0c00d2005201d641030840580159590b8420303121064810758403aa070300841440121010345500307900501061401c00080351011a1a5034030800b140f00344a04403054680c20140e95903408603070306004110125545480ca40c0b50852545079400d00b204101d2000c1d520755140f02c5a000c4450303041001c6583c41440d0811401c5010841403841c241014020042900c0140d0b40075212940188040c042c16140c4d844e5503030a0300c035201107174012800705a0401c85c3c82208540800904400d002d250b00003154660841214a00f512a46109120002d02d0110503850b42d0f0300c3c01c003031903001807000f41413118401c001700321075215203034403218841040000340200d070405001030100080500810304004480c0050000a6040102080340c2e96950501548640f13 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 822602014 1250 822600764 822600769
    0x90b0904020103050a06080a0b06010305100b0a051b0d0f030c030c080a0b030c1207090b0f031f020d02161a060a0b09030309060d0504050f010e3f040e0c090d030e 71
    0x41d80301345001d114603012001480f9270440300b1401150260382c10721060321524501c408007070b154010b501c0207a030304000b450000742c0503100074840345002c82c0d8001503000100c09240d0501c0c1e01d0705040c90100d82241000003242d039240c8106104203000741030400c1541c03485c1400410001004103100c0310166036840340042541d0421060302c2c0c2180c01042c42c000072401c078481a4440d540c2d03100c1c0c0e10055007800d13010f21061a224410b00300e404000b400400448961041c603043c0c00e19844c080300b15032942000407080f01c03c2540024602c0112103040a03d2403141494000c0c8110b409041c0c451940e82940103000965440e00e0359030084485008485880702070300d000082c1503102c3c145001c5e03403011f0000b40c0214000c159802c03c40c03046004005694049403d8214035090799031b900010b0007150000c080080c11203450180f818105400d603005480100d04000300d604c410315a00000034214080401c040103490000007800f68400e515a40c1b031814002d000002c11402032100c80018107002c1d51503680340311b070f4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 822603264 1250 822602014 822602021
    0x210111603050c072c01080a11010305040221070f150c0201120f0603060b131104060f0c1a06150c03040e06041e0606020d090302150c0a05010e0610090b0904020103050a 74
    0x1080914050003200180304288254840d20100b0344510700703191170000864000114104da82d850300400d20f603680005040045006003001082203a10140c029020040d1121609c9020341440740302d001030110500381441d041c2c524100d0b40c01034030b40070500011052043c0d8401c0d09112050b6081c09c00009096048c90030202400d05510b010200610386500041840f885801c1500c8800051f20642c0c440c1604403644420b8500c0c100280e082d4081c10001080001d2094a107080029164a0b22059600c1560369101702081982d145002207940c90007840020700e050440341030700d41150800140380c0900c0c036031101c0d224007640c030600702e9814035040010500c0d101c035003083c000410030a52803540d03030004034003180003040c1500552005100c3e244800380d00138001c8038a501030701d80081014404143ea0002c07003003954441428081c6038090141d484000603003d005102c000706a0320050840d610b40060802c10f001c02681c401002e5606000e001502d81e04c40b41c190030340054081c41e01041d07e40e100542507019 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 822604514 1250 822603264 822603269
    0x1e1b0f0c030f0403200a0b0c0f060a020304020301050601050a0804030813080703020601180204211e06060501080a0c0e04110903070803120c0702220b09070210111603050c07 76
    0x5030000042c0301032074654000003801030300c0c403c401d14405291800804a0414082c88149810840010042c004a036250000d001c171101d80e801111640769100c0d1200f0708007103081d0356003038605030048144000c601d02030003219486482841c110381020310420000301400d0010300090305100c40c050110700c01840540161501d00e404c40e0003199505034500d0b0080d602c500074410181031400945428038500c07d2402102c040786c0004000031403414449510801e07000d0501c0d8111468989041660074a00c112030980c0585805050005100c614003c000740c05400001c091002040c07601d4040e01000d50820341c54203e00c40207a074001000707003204c20b00203228030503a0360407907051043e440b00140c2c03420000024010301d8168290005152076a0702d840d261406201c030020751204e13a05141085a400c00100151203c0c03100341c010070080c5a220100344104025508000181c0001d190305620402d54010200040403032031f0706500e803103607001042a240340c030028010100903000802e60180001007064401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 822605764 1250 822604514 822604537
    0x2f0309120a210c02030f0906072103060504091e0c030507090e010b040b0105030721092d05070b07020123040303140a020d1214010602061e1b0f 63
    0x640e04008200640348285000448010303501e980c000c02c4580c08103006081503145a60015810021140645046a0401808181c01c002d007401524081114005d0074103841c141519440300440303926000800352606a0481170080c2d0401c2c5602001a544070700c0c06008a0f82c014a413017010841c0d141c040f4061215a0000d0f02c0c41c071070020f010403061034503030107510070714102c50081100100140c144019202c0c0245140c0c0894402e00c0014007041c00342240720a0302c1c9055511220503610000540d0480c0c0d00300d9415207400700402c40d8070992007941924247c01032250890100169016030321f440d602d0407140201300f003118000c1024011640649200341a0300300d1441c007a40c01c0c0d10312856206064020788010782c0041e410f40321094507408020100d03250300c241c45d4042e20782800700450680c2d02d4046150600382700756030f4801c1000c9100134054094040c041e640d000c3d207001d04001e511140541c12413070301542e40404d040d050048402140e961101008101e07551a038880480c14050388a41c002c2450812 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 822607014 1250 822605764 822605767
    0x50c1b010509010b03120f09010c08070602120112020a0303030c1106131205031006081005040507120e070806060d0201230309070611032205041503062f030912 70
    0x420248064000a10603507860008100c2d41c480e500c00c059982000c00d41c6001c6a4408022070082856410000c04e01d2680605010648844941d03a003181c640c820305040c0c502582c04980038028101800c90640100000c601240c4d06510f240c000501c041c859120003000d140d6117406058486000d030303040030ba05010440c1512001d24004611a00e002441c25040310304070301202c0381486c1640580700390f90049140c107109140203401c1c0601541c08590203004014640c04404000481d42e031b0f1030040d50300c200d840e51780740005070207114602300544140f10381060050704110024407039140c0028211754450000c40d91824185054001a0360911100d4039008003182c60b070001100c0380b401c00c17000394003420420b0200c40e00c1943d5294220342d1404403409000b01a04108040241100e010242d403001800c0311030a0700c0c0040e5100700050403140740c0d0200709000c0080c04800c0042c41014400c0342d1081c03000c03001c2030300704101d66604c81c80c01726010301c14cd014920022011503581c000800c10041211030007180d40c3d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 822608264 1250 822607014 822607057
    0x110a0c02010201151404140408071709060406050c0c0312120c040506190806010f08010e071715120a0b04020d050109020303120405010b19150527180118050c 69
    0x1502c01182e0070201d203000368100010307e03001c420318040442c452a040042981002c102e81d80391200d201001c032140f600500240082d10445d03551500400081c019038540329030355610341e002182042071800b8074600c6500003400c0407e82d480010f0450f01621614042101c056070f5452140420b4091a089160800c40120704e0300611346a2940790340341e181943e10b842015a60780d6004450b61244403004c0c1c4001280500100480c4000084298112456041c0900c0808950030300505030b003c03c0fa40b0358104c1002c031040001c5800c0c400b400038900c0c03005c4000b41004510700c0c1c851014041000d00024010f0352521032101c1400003c2d0305c02003103141d00600740c2c0e6403032085294038400150140c0c0c0c1990503520f0110400400d00e01841c01749240143c0180703040ca01480c0c00c1c3c0c2c204200036200c41c0350050101c10049001c0100040c0c10380f405030340c4000c608030100304800040c40002100c5e803958128280d00c41d4014030003101000a4099001c8505802183c0c03552003058101c41406048000c048611001c80f04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 822609514 1250 822608264 822608279
    0x40b04030803071b113601060f0201270311060108030306040501150e010e060928080d020a060c05070b070305013204230a060306050a110a0c0201020115 67
    0xe601400316655134080d0400c42103080c0b003c0381c5511100070320120051001e00d01504051a40c2c40004510380c106e11400240020002e9404004545040a40c40e031a00140300590f08001c2c4003400c81d14520003040040046c582500000006400101020051580d4842014403542d500c910408096050b1440c95035240c0c0595030b66041602c000380f18508040011030741b8109460a04000f0207590384c1c0b04440900031006480340280d0b1020035400c00d5003000502c00f81d45402045140c8496024003400003580d4408522004912030340084209401000440c854aa80010003038003003900810009101c4d0325022099440d07205058006190b4040401004546030f01988100c0c120b410008280c0340032004240c65500d21080005c204d6110052014100050304042c1d002e0506030703881103a0f03004003a0940d0303d0b400d001c00d01140c0c08031465071600c1051042214074003644c2c1c0c021391003404c1407050f03038003992405915010310b1170110100106d1040349401d5a100f500000e0311100c8054080050701d0f2140350 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 822610764 1250 822609514 822609517
    0x712020a051512061e040b0a170a0b060d0b1803040f080607020708060601050d02070204061208131e0504090309090509160e010e0c0d2702040e0c0123040b040308 71
    0x1101c030003070048000040c41410303c3c415446601840b001e507081c5d003103102810003005044900c01c0c690803043c0400e020a4204500560b0301c031011a04005021704001e40ca00030801c1403000f4500c0e80a0049030a4110000e181c84000076040f8048480940b2461a12219140740d401568040072041c8110b92002403c407101081003401620180c0c25a100f403034540d103000780e4030301c010b850050018008214040600c00749501409283e40700030000725242d40e0b52003004442e2a0012002c1e140c262001485194110041080034024107a80701c100b000001c24802c020341c00c03002d134414140030300e460b0804001014801c00390a0090b01c2205410055800c08000710380c3c1c2c1e070451603003146003581000e501050012001344480e0490b032984400000caa5100058520345030420390b0801c00e190748030451480b40d8906241c1140c2501030b0305030340110b0010240100026a69008009542504214420074650342e00c111403200b100482a01417240c05080d0110782c1c85403140e030f03010151076540445c0210030020300c00c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 822612014 1250 822610764 822610777
    0x30310061106010b0a0507020406030b070201060e01150206040f080c0a081c051017070f0b090a051206071b080309030406020106080d050712030902060d0609051303020712020a0515 79
    0x1628000600d901200c07090781e401c028010562103060901c84031048521070340007064080c0c400b510200e40640c0c0c07035440f540a07460a0382c502016035119034040c001d03070030900d107031a006181d4004aa1001007100034081e45650380508050080c81d00a0204401e01c0464422107032406044021170342d0f201d00c80d00b414100c0345c002c180d0b646090090445982c9808145000311401201c110002070321b05441c0400c0c0700700c9603c1000c508c0580d03005041c2c3c0040c00301601d500ea00010b20030460440d036603030002d000704002001c1d1a00050310403103108502e808250000500b880d4044401d04161607030441d0161541503045903a940100380d00f00002c1001440107012003d0710441d54250024412140c0380c501040c4c03a0784c41741150800103002840081d02080004600040d00507039420006104505900803643d5503014040003112240c645408010380c81d03081c032442c0e0b070110820381ca07041c0e014040d6030001d480b14240e1185c400e00e0440e0b40c00c0d00c001d42d0f840301081780080800034441401d401901c040d0321030300c3e000103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 822613264 1250 822612014 822612017
    0xc03030e010c0210030509060c0c06011e1e0f050904030206061909020c1006090902060708130f080c10090605040b1819080105060d0c0e092a03060619121403031006 72
    0x1040403e03507090205c4180d1f4068440d030002f419444c0c0c240407500c07a2580c0391189000b501c44425100003002c000d9038445c400011109410060b610b406d10310304041c0012154410f5019401c01010000404e50210b642900200f046a800703000d039039201a00110105a60020303030850313200003040c070fa001c0c030001405450200121003c0c0121a5100700d600100c9400847c0650001c40402c50440040c00f581c5c02000b5668a10303c02c2c154070760310b44440e0480d900d01600092445d82c07040c801c1c1185454410b900134101481c0d41380034030042d814244000d110b402a807003104036405011511074603000c10420341d190401c1c0d002d0b090441a083c02c1c14a2130442c082c91050b090700354a0640800d4007420301005c00803070f1503003040b0000c0c842480c01c0d407504001440100300d589140a22084259044015000e41654060424038810002510020503090080240c21240320f404808121082e41110103004000c46001c000aa050210142041400c00e2220210410389000000401c4505c00c3d070720b1801025180c09 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 822614514 1250 822613264 822613273
    0x90c060306170a0302120c0f0a1505151014070b040b0117030c0604080a110d0f120b03070303080405071a070c0501050705061f0503070315180c03030e010c0210030509 73
    0x3022407071900c44524020141c0103810029401400b050440011f100000c11181119500680050300303900340070002c00700301c41c529004a88800c008030301b40141504a100413003082d03420300794100040c80d010880c0f1114424002c03003901c1d11203c07a80810650b000503070070003151280d5181500c0c041c81417034000d00a0001d190300d0101104404400002030740d0080c1c403080020222038a4035103072120300e07402c060303500c10804c512120f801041301d078144202c581d8a0131545075840b07124414040034100414040b40303140083c3c98441e200711180d400260b4a42141e405085c0021030362501d09085042400581080040d910f00410010340b00026000800c11a4018005d204000f0f489000441d8903106880011f000ca44c005004141d50031710080c0c59030f0211480904656032030350742e40d01084c180b010303036071059131113040d58001e8851004550207100303080c40b080e090f407150b03100060351040850852400040c0800480c1008000541d028024107034006800801084006915001c0140178080031501d83c0c859024 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 822615764 1250 822614514 822614549
    0xf0e01020a110604050a031d0301020a0c020f030c01050714030f13051c0807020405060111160e0106020d0f0f0306090212090c06031608040609080a09171605040c0201090c060306 78
    0x100e409409164171401400b00721425843c00c540342c440da042180007003090303002e260409680134401001c1c58540c1d0340780c803600740c603080c0100b10480104080c0540a0382001c0d4002e54183c0c1d200c0f040b00c503841d500c11f100c90b03c1d01641e200c405103507000381d0030350001c008800180b5000902c0440c0c074002c1100d1003100e101c02031421148809012000d01070000308940424414480146043c0c2c04c003d9001c881850201504c6498a40b0a0714248002071038901d854500e14051060400030b07840704d4058000f40c0004c2c840c201007540000c0891340860081c0702040480102c24201901c80c0c0c0150340100750301036040d51108100301c00601c030b980c8140c8000f1010712500c030b0400020301340789003902e00c01c0c281c2a03200e90000200101c1940c82030030040040360541e90b54007902002900c84009400004065912a54141e0500b8162440c0e480041e11184403036119030f441c07000380c0e84007807050800d0f900b003900d0104280c01000f10a0f80941329007c001842c1d03050344e5402003041545603000804441d0060a410300c0c481 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 822617014 1250 822615764 822615797
    0x150f0c07030f0c081c0915021519050c031b031005090103032f030a1409060301030c050909011b030902010c150b0f150313301103190e040f0e01020a 65
    0x40b03121708841c0c080b515060080000041c0306c442c000000300305005480d410004900c1e03004410b4000c0f00c9006190ba0198401841c400f268801c150380700130b040001e075295007400c4000101c0300190002104290100000095003124000d0f032040060030080d202d1b0645507100e2401401d4211102c03c01a110401d040000d024482c0307891000c1d202c5d40c10180610300e800940403044410610782c204010f001e800070003190b00541c450710000c6008500540e04a01d0880c108400c00c10203010242c18820a40c1c144a019040406640003860909245042c0001d60044a10040e40c1020032028083c082101040003003a100c0103a81101c082d4400860700c070000400a4030400001d045100c414405441c8244006403018000040c09070a03640500003100308001030f20000e620020299004d41d032000c0000040c0f010072038000584107500e401d11005903040000780181c0e40d100d10003c5410300c1c01c00201011418040d02ea6620140703418000600501082e0100e51000c0d020f9030043c621407001489a808480540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 822618264 1250 822617014 822617053
    0x1050a141e15060708090411280918090b070f05070b09010908040305100c050408031c0e0d02010e06161202030a060909060515150f0c07030f0c08 64
    0x40144030700800020340c008801c045404001003515400030010074226810342c0e6440050464140700d10303200c690300c0303141100780019941c0550702c7d4500e1160030f00038050030103001c000707284a9550412822034103078102c00080365950906c3c3c5c44445283e41410f9540c80101031078028050107070003015500215156400210f504005603194070000600c24891100010542101180c11041c0c04d0300121700091151110415a4003552044a4540c89511a603810501902510f45801c4160034000e0500b480c0481881e00c034410344516003464015070b20403541c20003255020442480042d011a54034400d078200203802044401802400341c411000042c6605060824200035a0300743d641d440d40301030440c803656001e500040c0a80c1001da40301d40d00440c5005103485080ba580d030194101281e2070804650803120200c0041704540541103c5c0e0140058503105402c50b5201080c00504640d12006070001608111040e0002020002c101045400380143e52034210103540212090700d000809014145541 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 822619514 1250 822618264 822618271
    0x5040c0f0b070308040501060302060a050705011107020604090c090306060b04030b06121e0a020904150b041406060a0e04050a0b13180209180601090e0c030606130905100c0201050a14 80
    0x1c002044441c0020384612000b5410501c902e001280603522a07001445030340084100070000360000c0ba00c0c81c1440424080d402c4480c2001c0c9403540b80ca00b1031f401117500340c0b00e24083e40000544030f030001c9030500d214980d607000031500051304000042c0c843c0305074140e42d80f182c407080c0c030038200701c070042a024a032100345441b50840307a40040c10071005c84200110b801c9010712032400c481c018460b4860240e251011941c1c840d62140341060210402030400c403046964050425004900c5c040810350f85081c200b1483e50041d20031104252660140181110700828134031849821500f4882485800329580c2c0000c01448002c445202001181c00001c0c0c003140c2080741d2000010072400c424a0141c10010402e0303070031404641c5403414284100364654507140e82039002a0146680f40040409080140603c801a81c1d046010340340e42d082c2200010030181904011000d00c0d07a460001700c040080c10800b8180c031900c450000e0040f6450340070064020300d0219a0080030605101890414424400d600c510 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 822620764 1250 822619514 822619529
    0x501170c04020906070f031704060c090b0306010801030305090f0406120201031d03030109050c0c061317041d0a020405090f010e010b0306240c2b0e0616051f05040c0f 73
    0x1304203942d110300001403070342e0101fa824400482e11403140080d40c00c40d128402da0242802191002910740018681d4000d80d10065041e0424414003100c0e82c0d01c031581074112905490302588494070b400004141200e6448031951080c50104001a0034003146e26006400d8001d80b010010240303a02c2075010414040c098440c3e00d40c100f0401408624680c0d0b0146410590000030203041141c200102443c0c08004d071044c2c5661070441d40e4060801494041407a8010032500c1010304140ca0030641c4410300c104154030f810242321031000500c0801641d81920001c0000510310306490600c8045494000d000703010b80c0041c0d02c0c002d0000326498500c0c0c01207071b0095101403c542d14402070405050083e5030b0007208044281c004004405507654100042030a043c0700c2c15001010b00c041415507060128103007880c0044c80b80050f41140944d54003025075070f541011285180c000c540070b00e400e07820315061952807001d4500c604a4401c8803111a0301561099109220081c1c9040d00c5648014100b00719100e40c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 822622014 1250 822620764 822620767
    0x30504230a1109190f0f02031f1a070b04260406090501030c05070f0212011a0316051507060618050a0b0102070302060a032003070201020306181512100501170c04020906 74
    0x3100a0015400307034603580405070002498050f1420080c0a0340d1094403605101340000c1080802c0c41027481d0040020191070349800100d10100c007135036105004522019110500342c000040c1489040514031003241001440165000c803d4a203c0700690458094200010f1100002060301d50003440b80603141039a036201c3c60304106a6544000c1e82c03452509040380c11901014803226544024029101d007084e0700d070304803513428202000f4549048188001428014144c40040001d5160102040c82600310049065544c3d911814100003500c07042c0e004c84120000c3e02020701a5064540c00701d4007640600314148140201d880049940700700b5404081e51205080003001e40040c0603a000c00c4100d0b00e08020005001410304441034103400c2220800050b035000810064030746051607030712044515622668502c1e081028003440002d00c4079020354001c420300701d2603003a0680c04100c21072890207a800140090b40c0c480c4050020140304052203d500e00c078030906118245403074000d40d840740d840075000c0c0d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 822623264 1250 822622014 822622051
    0x30426090a092d0e151302090403140705061b070b010501271206110307091503020c19020306181009021503040605090c01050304020d03030504230a1109 67
    0x2100810f5103d075080c04883e5900b0806420303c031210752030b1100a20881d000503250303101d00a003500342020b001558543c0100c00c000c00582d080030160f1520f50300c1c1c054440c80115a070f039181c20b03904ca010011072021240c0b00410780404100c0002511480b40c008000607180d020000b0f8100202070080000040198460303100602c00c035445400c3c920502d840c07004031000c106000743c4480c1c400b480b080c4c1044540380d101c8668101405018040d0b11700601c2148262491440c0c01b1400801c5c0041074010070b0404a041ca0144000601c01d8050310111461002519030840d15980d207451103080c246000c88c0680900780008805039034011a01c1c1c000f880da40d016101c00f0b10000d10040c010282c200c82240e00c01b82840040220201c00d102039031145224180016050400715400c620302030311081240d0420004004210060305c03201140c081d6640e260a004c1150b0300e072842c1c82e0a5041c441d500e0300700781e0840e08000441a0b200040c0c061076850017502c403c60b441e0404800d002c1d0403d8201c030030407114100001c44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 822624514 1250 822623264 822623279
    0x17010b131401120b150d050f100506030c130510051e0301050f120a05030f07050f0c151e0a020c01030e0604030906080a0b03120405013c02030708030426090a 69
    0xf404801c400100300d005c1a042c0080311000640100c008002003e03698010041c0e80161200e4940d0040b10707024960048605e03000002d411848010690100ca42010507030030ba2036010381401d500038080017018118616032000b401052500108107141146001e40c109000000c01c01007264142c808c0903212001c0e620103001844030525080e401095544528081e074004901c0501c082d000520000700c9080d43d410031410304a140000410a0700a59044000c40154036654001b040821029480c0056240c0702c18504040c0e400c1e261100e802c4926000003402e441559000c2030081440f0000d88041000075080c4411513540c00080310014040b5004810500031340c2e005171203983c2d000c0110040802c0700f45008002ca42071412072291a40f00707590102d0180529a0001120321042c005007001201c0300c001d42c10b240c03114507507007404094500003113808a40780318800c0c0b00300d510894001081c5543c900709840d05002c0c10045080e80c1d010b0705281e900302958003030340800710b030180b8400030040c944003401c10a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 822625764 1250 822624514 822624521
    0x1f08030a11030c01051305120406081501030b12010501180203060a0b03040c03060c1701090c0f201902120a0b06040213180e0d02010b01020a0b0717010b13140112 71
    0x2003201c440d11007405100d500700000d02135544142d1440c07031a0404070b0180d280051600c070000540c1d88409200340418408954490307440f1b940055807090b40c0f2401d54100c0c005038010444100c603160007503a188004001c2d0901508154121841426510303032100e0303450452003c0340010303030349564086c42e00702041120310881d00c00340d41c006001e00481e12086030340340c1e40e03401281c0305102005d000c01c0c6a07003144541003076061031407801040b9002c01848400d50382c4ca8024411110190b0074414081d034074901c1080e0200610210442d440b200003254400c40d44514541d081510481040344070700031072400e50b007504001182028926a10189018548e03c60380c00b0031010b0340101440b500540d043c81e00028440000d07112444800c010300e039001031400c00c0c140d80f0604040074400351401356810520070060503603001030b0030026143c00030aa031110341c840c00c0d41140e2a800d0500d103610f10248480020034020050b800404a04c8100b011140002e6920850348160044899200d0301044c01503c04411302c84043c1c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 822627014 1250 822625764 822625787
    0x1608010e0a0809150c010506100f020d2f0a0c05040204050328020d061d07050604121104150807080c0901590f0414010b1003051f08030a 60
    0x6000c0401300010380030302000e541201c02a103090784e45840500140c2e040408100c002042d4a1500f1130074402c0d9000043e6131030000012460400011042101e203000410039690701070700d020003940e1800000f0003405640d40000003806d4a410000c0800010580340074421242181c1014024114080029048160448212542000e58001e0010050041c1d4401c0b0118500d540b00c3e910028016842240e0340c0500c0c40030f680d80301c00c2540324280c01d2040350740300c03c152000c94103082080281658a850071030440d0603442c111540040c2400044441041c3d8030f28140155942c1108440c805070f50f410a15688554110745c9540081050b40140300342c240010340810440e0b104481040503111131041d0390312007034a60429108502104814801a02c0c03d180711200300d00d510a0241114241040901e14800d030280c001421440300c0380880c0500ba40a40202501c484000c140e422120085000075029240403281d000c7e01000e00001e8450b5845a08888402d9541840c025418944101e0003950030031103e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 822628264 1250 822627014 822627019
    0x60915020c090c0d051e1b0306060f040512150a060b030a0e030c101d0319080403140d020a0e100c061802091303031808031f05060c1608010e0a0809 65
    0x13005881d503045018051103000c0c00124068100107a21103044048003480944140c0c03080c00b4400c03010301048051820390340c02c55422501d15a40b825035034000700306482240d000a80024003050340050368680410403260701200e40b1803003c016507075104508203c880e14011001c06420500200e07140ca0f660303901036051080840112403070088051401d03842c00742d14043d04802c0d1500d07801011500c0d0b202d11f00001d81022544011810900e002100048868440c0320380001c02068100250a25101d25080c0740c0300940740c0c3c900c5598184049520f00039600c9103030340f40c0105001e03003c10340c10760602c15a01000702803a82d550401d4050f8542c2c5040c00b03407480c1400001c00000c604c4102c40941e40d1140f40c0c500542051103202c4a070401e524001d02a42c4100301c050000003400040000072507420400c5a507c6108600451000f000400448a540c050754010a400030030106504000f01c00000350741e403814281c21040d030100780e500d440190994907841d840e080c40341c00c00c212100000e42d40704007070440013000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 822629514 1250 822628264 822628267
    0x20f0607021c0306082e02071e0204150617010509041a071806020a050601120f0f05101e0b0907020d05181005030f0c161412030a06060915020c090c 65
    0x46172401440c0680b41c14030840091032017400fa5114100c91428002c030041140001d6040903202e0722440140e440c00c40403004400c2d00341100d201190b40d6a805600c0312503840c6185845543c42d110010090220040f001100c1107100c0004202031803e102c040c0e01c0b442c1c0c803034408102c0a900ba42c40321810350300603004405010012140c07001c0b00303102c9017a08001c0c10302d44d401018000d0403428410f240890690001798009140311841000c02d8411001c003003440e03089040707599001c41a10f0240d00d0800005040e505581c81c241d0b6122092502e2188030364102d0380741005001e03078a019000c0240c240310036101d030005640181d03801c82031140150003420b00387c0d40c0d00d060442e80294240114a480052020a01c0001c030b00008001c01d4040d440d0786560030400700d40499003485450040c08924101080300a4011040803681d4203000b44200300e610800040d40100f507443c1d0401e5400b840c0503208902404012600304040031030030400b45040403105214aa000781001220342d018880850400303010700442420 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 822630764 1250 822629514 822629519
    0x4031e030e09010605120c0a021c05071a1501031b11160905180604050705012f010c030f0b09010608061f0203090f045106020f0607021c0306 62
    0x942c2507001d8024001c1d621001c0e038950118403140b807107000042c410f20200000740080b030911980040c00c060358114a03840c60b801e2005028080c2c9041c0682440203007103810f50003114004140000150b409203100200c14814410841c0040d0140c034021509c4c89450203c2886c605601841000d10781d032051140400c4e50210b039801d040e0025144099040505d25584800c00e1003c1c1580c1402c96078145134401001d0049421306030399130340d00c03607042d4462030307040180c1d00000d0b050025198655014003801c0e981350704026214046460302900c0030b1042c01c8e001c41c1c5800703101d40c2413050a008222a4003402041c1c1d00040c3c0c00c00320255034111307000d00a25004400c0000801d104d2001c00c6c81c1c09003440340740c0c0055840380f602c0030402400034054034286018508002418a003425020248ea505d45490150440ca941000c500c6400700509001e6492100010b24401c050060894840006407035156003500d903a480700258a80c0e0b00d910550740c3c5070042c2e06c0071030400307200000d41308081c141800900d4007064031035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 822632014 1250 822630764 822630769
    0x9270a150b0c01020a0f090f050405270a020111010b060306100e0603040c1401050708070311190b010906060801050306040f02030a0210080f161d0607061b0e0604031e030e 75
    0x1001a110340440741c4d4009079140e80e468020507079801e04001490000f8065080c40030b4084041c4240c4201c50040f611000440e61440034800d40315a050f013040020603d859030004015070780c03803c583c1d01b41d001c06c02482c01980744020600a5100312800034243e503144d070316003c080c0b10072101149543c8080004c04400002d0343d0340c0b00401035014902a00d00591100d040000c1c01201c1c24503485a02d0602408014a030b00003083d0100740d1700c000340c1604013115035182d000b030304034288208031001c1c0400300c0c440301e02d180c200044c020680781660701b07402081180307684904058813149000e000301980b40d841080000c001403d50804c0c0c0001501c00b80546212045c0e59000c80c025126100710f02003c1030a41c01004000806400855801641c03410001802c03101454060269210340a440384034106c800444000e588a00c0210760516600c90410041d02c001c0000100d400c2c005d00e155000024810303044070002d45800000d6400307032500a0418108003414a01d114101e0441c000c0440505c03005c50010900ca5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 822633264 1250 822632014 822632017
    0xa0605071a0403170c031e040c0b040f0603050c090d1415040f120206070807030b0f0a0806060102070909030806060306120a05011d0a0b010e0408040305100209270a150b 74
    0x891007902ca542141126040c0c904c030b4010000d24010310581c0510400c0305051041090070000c0300b0b81901100644c60700e082440e00070000da04080303a4820001b03000074001c090200c01400304c9501d44e40c10815900c8894800303529200781d0f00c1c500d40c02008540a600402d00f1440100c810756180701c00c0720700c1c2102040d102000200d085030152540e5003803080710f4040c411120903100d0201d40754405042c0f42d1600d5100035010804c09410329041503542d4000c2103040d03d64000107104000000d01104140c0d6032414217665404003260304074018050b1500000c1c1c3e900050085c4143c482d03041d00c801040da40c3c0c100070f101c0e558000030056503100004540e0402c01c940d050049003140d5000380c002041c0214049081a03184920030340602702c90340902c4c244004903a1910001c1c3c10b4801002c020320b010f4071242006201ca0080d90400b03003190250078250170001d030266001740512402586c0780e825840000900d0584a810f6403282130480440340c000400074440c0d036120080d504940a00003200780e031120b13514142c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 822634514 1250 822633264 822633271
    0x8100c1b0f03030c02010b0a090c0e060c0d1b030503150109031b060906051c0c02120c06040b1602030a11070b07030801050a09050402031504020a150215150a0605071a 73
    0x352240d0780d840c030289507050195100d90115400284203408a400101705061054032130b254655070f603204251002846400280c00a0000400c0c09858481c0b001650703031141d800807a01c2009c074900c07500c0c00707420800368008130701c0070f40c0c054865078119a144801074951020280410741006040c20700071001a15020094201d010308038100b0000f0760400001901c2503415030023000500038103115520401d00d0615024958140300d12020941e00d1b0300203416850240c00104180c0000408204004a8100011414802d41c0100d40c00c0e4280d444000c45030502d611540313407040c0142c00810030015414051400c0300c2500303401d10111066241d40c2c06580c481030300304000882c006000400104003514200b00200040c203070303044040010741055400203955039511400c00c15070440c01c0c4001001e55580340c0b4060002d00d03450444070602004603030000d44408540034101c001e0003620010929111005944d0204d07814003500092034581050801d464903041200100c41a0080101c501c1201130b07801c052900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 822635764 1250 822634514 822634523
    0x50903150a0e0c01210f1808030a06050105090a090e07081002040e0105041506120905150405150103032010020d020c0f1504110f09010305100f0608100c1b 68
    0x318107000c41211400e00701c1c48080681040345c0d6030600b400c2d00744c152521400d2007424450000e04012060007942c0074040706d940c2d490014650580b501c040c04440c600540c8038a0500e5000c0140b0f5454100544082c0900c95401d82c02035541076040c0315a2440d0360140103e02c008600303c54825035102a281d00d00014103645c5046aa00407504000d1540214400390240c50104c2e000d2200b005c401300c0341007840115216900c1002401842c1c601d0780700d5198000458940c01005991102e1100e000c042c42d92501660200d902e0f10502280005020b40300000c181aaa803641c0c03002078090500002c91002800c03d84080703098010480b01e42c904600d6031002b040c2c09c1c00c1d00f82000d61142e406e0140141858180340d64500603801400076589001c4003056604c0e0f1150780300410800c0c0c000c4201c0410729242840008a4024800c0c100100911100080c480c005005a0703000748200003011402a05451807841207400310740c007540a00000d0030300c80d040030800c545035180801c0d041c0c1885000c001c038414096000d40c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 822637014 1250 822635764 822635771
    0x708160309060905030708032a0312100603020c1b040e0105041a0c03100b0304080408061e0c13050d030509360601050702010e01030b0d08090f030a03050a050903150a 73
    0x8802c50b00521064010407046000c1c2c03240d5403500080a4991058100f00e05403c140030301080700d030717244a02d440c100a59000d000c030b9880c0c1c02d8600c030300709010780c06450030501840c001c3c8002512a21a0080380c00c0b441c01003015202d1303980072440359800420300d00c09241e44940c03078203299283c020092103424465030042c441d000030300000002440a100c800b40000740c800c6020010860503039640c400000848506075055a9a5942d50524110702c0c00350740c0102c00140912014820814241603030300040703400400c03910301281c03601c0080980074883d2180c2401e08030003d600401c040e01d40703480310324005802070910b0f910b0040d40c0000907070044010742130010134000e1060401040a4030b00403002c8400080800c010441c01c0c00c0d00080e18900030210000d04200c030b0340000351303617a900c04e1304400c0320404040c01d503a501081da840c1400c520740143c421140103920205c448581c61800081120b41a9055200c2d40d00d09000540e00b01c1309648003407401901845584a903408512520484500c903204110000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 822638264 1250 822637014 822637019
    0x30f020f12060f12150114091f0504050403020c040e0c0f06070f051c020105060a0608131b15030b0a0f03020d051f0e0f0a020306071808060403031d1504080708160309 73
    0x903d00445c10707081040751400501c61f2842c140c507640c0199401004410b6035400c03020302020300d040e0000381c0c1d82119800034101401d20042540004903148204012501800441d203080400c99840d8241001560300420a40ca90422400d14100400c0914002d0700010200d0003a034642074602000407a04242c20200c01c0801c10342035030b080c070400703801240c201d33082040c0a01d0000010500c0d4009000c58210b8206d8603c03a8040040401c88079422000300c1e011807580302d41d10a510450025075010b06800729042210a04861400c255100142e90b60710081c20842400c54090100d1030f005008119641d120313590140d03144500030b00700603c0801818102007003642d40c2c80d8403c2d08020021500741040d138000d00f002c80040c1c0d000b0800951100c40e9203400e810f0074010110404445881d80c2c040f03102401010140024960325410078100110302400d2021444804240039503140311032000000e20703042d410089000200400c008014a40c090088181032490003803050400a07040e840071004160f0100c000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 822639514 1250 822638264 822638293
    0x27120a17010b040e06040513050d1d090c0a03150e090106050f0d050d030b0112090f050d090e01050d02010504081b03060a060503030d0b0103060b0a0f030f020f12060f12 74
    0x1981d000d0884007030080d040510b00582c521029030040c02c034520407504e40c070014201c8404005012281c1d03030410201e809107a1840d002401940c1c029902c100000d5003500c0c07242d09030034038040c00780c014824166403a01d00448100210020004080d0312020640e0003400015006040900c06005111190001500d285000d00300440c065445042a015141d0300700c40d4404124085026880449a41004984541700c000100c4101a40c41114201c840c03611244505010020750ba42d801c0a00c10000c40e02d1401c21300c1c07020341c0c400d1607911a985049013908018002e50402810b4103160604c10305086042a03254000c803420040c40c804201c0100b1031000c029040d03842c00f081116000000207100b04503290810000c40d8076449280034000304203450b100726034441c0c0d109078045401840001c840e192240c441440c0100380c0d9000f210104002820050058a541107d100f100c04030325090108a180c1960294203581002c8010000c540c05840074000c002c0c00d48400304000c40c1441880d02804c0d0400e6082c1d05c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 822640764 1250 822639514 822639557
    0x1050c1c0b0616030905011d09060f040f02041d10050904030c030201021b0a201e060705070e091006050d02040c18090204031b031109090109020310020403051527120a 73
    0x2a00b213640c005104088c3c0c2c1c0c82e11008107540e08840e003601e07141d03c61040803000c1400344c2024101400100e100180008000214210031992a01c0307200d1010007039100d11000f0401c9003c54080d8603480b182d00008140084e010360b0707d031100b1a102e4000035041c0791411310a2201401407614403a030a0b00702001c904100034160214100d0001c41c541e42941405014011030742e0816440c024007814003005410f110f6a03600c2e8410f90b200c0c5503000c81280d100c15140c2c0c102c510b117002c05070b0b000d01781b900c00d00e54030341d00440070f42c05154155040585507024103007068080001500c0c9842e551401d003e0008010005c3d42101100d079405803200180259441c1e20b985840d088076041c803d544002000301c032005000140310140800341391081200d251140d600c2c0e0381400c90040034103803030003581403083c1080031079000c40e01d4026204490061042c0e403d51020425085445901100c40c006400303e903001c0313078500108213a603c040d2a43c040c0100d40d41703c1000d400c08809907110045c00c0020684a0a20805001c003412 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 822642014 1250 822640764 822640787
    0x905011211040501390b100605090907030f0e030c0d11060105060c030408070608061507050604060e070b28090312030c0c1506060201050c1c0b061603090501 69
    0x1030104180744010200160314055401903e0402c89040d0403503482210400420820400342030400c1c1940c9145408000c018452110464410000030000303a151000e258001d000c0394a03030b0312103e00e810440c10404c02c1040c0b00908000c00d042d42c4000754400540d8a01c1000b240c41c40d07000066541c2c81085111510700101070b0440c104100311082c040724205408162941122015203006071200c840175400717801d5000da03403c00b14180c0300303482001070a154889446070048106950b8410b00c000300386022011071041d03c002901c0c0d5805000468006055a03000c03228605801059030f0107603480320520b03850390340820b10340b60707400401c04840440610300508131500d01c1564104010003d14650fa401c45c1c8030845620041850358030160920110f0207124211035086d070101d9542102c000220080d07000b01460302444c1d0040d0700c5d01d0009203031f856440c230071160b040c80005154241c0c01c0c201c0f501c040c007900c1c80b61381d00c03a00000180000031a0800049101d2030003482600ca2002c01828840010034108818 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 822643264 1250 822642014 822642047
    0x50604050901020717070819050d0b0a03080714331f1a041205010f050105060a0507080c0a080c06011d13030302030702010e030c0a0b150906100e090403090501 70
    0x4018100c0000c0000f9030917501c1d41c3d14042225200c0200342000c552502404004a110200390b00030340200540c000b0040c0086c400c540e4081000c4031000f014008508042d0200a068100401419003c034020540f18a69411060121040a498018041e00c400d101c2015409031401d40c0c1c4e8103020494030802c41c1581b0007906811a0942d4041c810802d2542c5610b1145038250b1704480c1150b0008c1e410103045401802901d4592140744105180c41d070700034038070307000451607980c5044008501032030064111901c10280f6542c85062100c9030321642d410350710252003090b0b544078100c4200001503503000034081070751301c1c040500445d40c54085a0400a0b040e4160604030701000030030800240d6628242c0c500c100d40600d030058483e0781d00d80382a401481d21f1200b1994610020424000c0c444002030703c1d0031081c0c030a025205150310747e11100b9200c1132a0904040e40800c116002803098100341c148104c0400c407514043c40004000004500d401030103036410b6000462203c418021542c100080d8440c082d0032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 822644514 1250 822643264 822643267
    0xc0c0513062402060f15090f19140126190c08150f041e0506090705120a022224120c0611030c1002250f020427050105060405090102 58
    0xc2c0c0000940340d807030040c84c3c030000645e100003040030460350003503600c3d4907000541a007485040600d40c8951648084401ca80403401850b06480e948050f401008101c1d140c80c0f5071800c490342400c1c05141034540002c03103c02c90034021484050b08000402924019808030b00c1c0030446074800d03041c440d1151040b41c1201c00e0360750103e074190440962800c403540d4030503032003045641680c942d403401d400202c0740500c6080806444110700f070144400496401d0285800c0303012105025951404e01c01044181481c940854102c2840c801c05402c03d90b08001303035000d001d02d02c0d10400044490790801c65080e000c88900456050402c808210625402c0001518a00c404800e000742603654604000e10640919030070000c481c0a0000c840c9010405d83e0030503000d07074003239031000403160083c48004d4010348024191400a90284091804a610486041901318000c0d80c002e49054080c40058402d8040912030301ca1100845486d980080d103035032074100d01c101c1c000b049a041420402081c2c40d000780014405920 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 822645764 1250 822644514 822644579
    0x18120c05100605030d2604150c020f0d0f0e12071814010501090e2a0f0d060e100b0a0c0804060f090b030c0a030914061f0e0f0105010c0c051306 63
    0x83c0c5014982c1240032400e01d010040c7d0b0303039192001b030b0340b0f5401442a003541d0500710540d40140e0041078400242840070122508910041d400300c40d03002440c1d580502182c10038035030220b1400d004009071b07083c030803003001c9405150340c0b98900321500701c4100380b01c01003c0e540d020028020400c000e80d50300424003443d021207140c0c03d228403c800b0700000b13404032501d0100840b034180c404510052068100d00b01001031502d80c00384000c0c0d566294040c18108c004030340b4268020401c403040c2034415000e0012040c550100c0c07400d100c1c1c84503550344641012070034030401d008018002800f01c001000900b00c0da030389007544c0751812030740603041c54856007050102e4903040c81085145105003058a465407003074a0301158880c41400c0c21498039840c1258881540031300b104201c0c1c1608044413820b041c0400c0e41301d5116056542c4403604444c1c2c400d0f20300394968890800100201d6224441ca02000c1d8000d007181c1800c1645c800c000b8951500c80c2030303040a016142c00e420000006505020018200701e018007488076034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 822647014 1250 822645764 822645797
    0x50307030c022d010b04050a0b09011203050318010603020316090b100e041104030b090d1101110d231006020f03090a0e10080106030807110418120c05100605030d 71
    0x41400d0b190040c0c82d18120f40b036000c0c1107007500904205540035101304514141a11070a001e0701140302060301910003000005007004904440322601c540590b2501c0c10340d15030f280b1006a84134243c3c402211176480f10304c0400965403e000d00d010140c14070300c01d214890b14104c0c0c0d403801d032444c081380c180c4a070301e12101c03909100d070704030f0089507000d02c0469002400303c1000030400d480e07010305d81000d010301524804000705500c9c0024036000780e502a8442d1103083d800b04403940d003a107848814601c840720003030240e4080a541608100082c101c03400c02113040c002d15059000020008035400c0188071540c40e400c00040c1d80520018402450100c0030f103280c101704201150400e58079214004210110034002180306045040001c01341080700e00a0050958a041c03446507900002c4041e50701c0f0f003039540710080e20b02d4680305414501d1000f064091a2031001e03141c1519900900c1508010310119250950000300240a951f805c1030414030006403241c00d0006241c80c3c907000154007070a10007840000300180c1d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 822648264 1250 822647014 822647053
    0x6090a02010e01230c030c120a090e010311041e05040c031b08120904060308070f02040b010305060d060c050f0406030501032a1502030702060403080306010e04110409020711090106050307030c02 85
    0x600c0160300c2139660f400400c20041c80c1d4862036030a00c6040c004c4c580b207040d80008080051451191590341c2070303443c2d5268540c12500b440d085c400100f604510509a901c80d040c0390300b00d80100040c200c0c030030000304285451030003602c000302c404617045107031007605108000c098482540611240c420b04061541020707116561b64075101c50102182c46e0201e80f40a06a07500d030058009103900c0141986c4076100c61600e18245030302804100d20440c14101605030760b500c42c1c40b840d4800c480c002c25a5480b000e5540f0b403070004000c0c92009104200b4200526a203912030100100000d02c11960300107201d42c5142400c4003240e111240d40f0300780424031015820150310903405a002e4400c2990508401212800143d14602c14580c000b074000001040000511501c04050340c4203c078203898400d0031003c2d90081000b20380d40c2003842c0780c200c0000c0c402071141010a6000d4003040d485808803c80c07540440000a0045000742d204900003000002045445680343c000c03400c00c081d5500044c81011580003411010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 822649514 1250 822648264 822648317
    0x130605060913110403083a05060d06110a0801090b0105250c0902030604050a060303021f060f08010b031e120703050d05070207080d08061011070806090a02010e01 71
    0x19284425802d0104550759001400030155824059070300c40d507926041d152a04501e1500700b1484c244182099144801d1300c0b022070380030031041c83c06100b003c801e051100074103010303041a4210101e041348400044961045441c032001c240c810300d0316403074480750080804005030000301c5003c0c280440d854242e42c10109407002d2032814001d00d0b01072041000040c0303440c0c144940103428400d04400010f52041c441e40150300507017054909100c141d80d20844001690b000b880018010f0780608003031440240340c0306001140001010000c03440603500c45d4503488516464005100b075941d20703010001c40e8035007000700c0303102442c06569100115105040300d9846001062440d208450700043c89410184101c04403101080141e504014600307054078002d64600c0d03940580c0380a4410382ca44040c205001d9191140300e01c0700145103488600d404141103c5045440e0f11162003449044000716080ca03090100510807101c2200400511229000051584c49004182c3e4144601528201800d58a420a9102 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 822650764 1250 822649514 822649519
    0x30e0d020118080318030a030518030c0718090f050c0306100e070c140312070906020312010b0f0403050a11010e040203130318050d03090e0a02122a07030e1306050609 73
    0xb201c0d80c6070300820845d00a401e01c044441e00000070b10407030300b58155101c50700a984034070f1380322024000c50380d040d80e50307106221a820060784544010031450902101940046844440c00701780302c4220b80c0c85070460242310100700e48a03040541042800d0500b0800c0503440018254200070719442c0803980046180040c045030308005410b035101041c049805012110811864201c4c3e655003e084150000d007401655540000f03500c4410005040e0720000507030315060416805013840c0d919140394200d50340d002071694029044d0901002010500500c00021018007a0702d101e039440c82c209000400d06400340320304130300c00da205005110103400046080c142031541821320950351110389a0b8002a110180c0c00643d005102c29002d01c20554456488000c5822882002c0340d5074440d00100c20a034020750550403000078000c80028580720400020400001d6594000886584071000100003640700300f41c1600030401c0c4c16012406414444160140900404003c110460410001403e203203e210142407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 822652014 1250 822650764 822650767
    0x405011802010f120209060d051801110a0c050a0b01081b101e0c050610090e031806030c0c070609051003050108060114030c031b010f021f0207050c0907030e0d02011808 74
    0x304c0004099046441c80d403001400b058980008104a03805403038219545104040c525640b590070200c140915100c41541e28003250404d2040b0004440036004142e00b61442c0c40f9192003000030608100c03180b0702810b207020191030078202504c0c100c9006c0019014850181411540c0c8000040e40004542000590340a0950003043c03407460450340992000c00240a5001d07490510054540314032a003400c0300c03081002408008070707503810305449010f800d030029016444000b841c446460840c005690000443c0002800c02c01c082030258030f0416247c10280108007548000e008a1900f12a012108541483c0601541d030500c00c3d41d84c0c540c0c130306210f12450b90030300c1000100156002c0c06070507642d0790702504445060740c01400341c5c0aa01d40b143e00d01404107000841c100c181d2840861840c600c90301d165182000207400b4100900250b10001066495026078646983c40b9600c02000a00819103a9000710700340e034403001e4040c10010f81015640c25a8540381440070800090003071501d1054024070151b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 822653264 1250 822652014 822652037
    0x80712021306030c0f030b0306040314120403080402090105060703020c0f03030c010504112d1c1e031404232403040c1505030f0702160e0405011802010f 67
    0x140603005030807a040c101c05041d4004515154541c2c03203503003004026a656808003034000c50607011203c030b8481d01034162304284e0004000c81d0107010a2011030b041541c00d10b107000411a101c00f0400010b41e000c50000d074843e8203000c107619000040c1805050304880181c07400556a030003075600c03288901303e94010004101c0300416550180155102803461500038001480d00b840c02c8801d00311190840c92061940072583c1d81d1403015160741c02d0315001d00d040440300040142c020480011900d52030643c51420710061400000d0355030031400034421103580d100310b034810386207005003044814100c14100288244010040c00d06908040302180d0908280d240110440d180800c3d01a1100300d0f44001c0ba04600744414540ba82c0c4074000e51045006141d40040075488400c400c101030300200d107490006009001041180c0c009015094004103140121000403005080600c144800c9a01800d01c2400d02030800c01408428080c0000418403120315070940c41c3c0d25400a0a00e940d4050711000700300c0c0c0003001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 822654514 1250 822653264 822653297
    0x250305060114070605060910081506150c06070305180a0305090316081e1209040f0603170706051e04080f0c1605040e0a0b0105060c0a0f0507061d010807 67
    0x801c0114445000b080d500c0c0c0c202d0622a01400090306c130a03029012803000100450040d006400680c0c910b50081c2408070080100c0200302007024055542c00001c8810904819030381000030010321841c0c4000c0d000c10315244030003908030768000b040d09132441c0058910000710000401e4010400364542809500c1d40c42201c0400d10b81441d09418804284180e000881c540900089002040c114654020100c00c00803905c0c2c0d803200d412851016484000740724800b190300d481c3d080410040c0342940d001851955170f844070110404126011140410000f500e0740900c01c00380901584503d00304a0b0030350b00f030b8100c518030f00c40a10080c40540380c003401088413403c0c40300050444260ba038180741262070070445680036240d400014480d444c4568071303004200c1110321012070611306c40e0303170010601061070380782c0001c6c413075194004c403e052481d02400050000041003406c51140c42d41c040c1004006075030610304003404082c00d01d081a424401003030300c1c10700c6503a4800310060b44802c2e540307003035485400360703a11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 822655764 1250 822654514 822654527
    0x5030301180b0904210507050c040f090512031f0305030a1419080117161e0306110909010e04152003090a0c17070e07020a08030108070e2503050601 65
    0xb150f9804180d420070f00090203000e4800c030600c9807000702114504e4000d80019140ea00c0744200003031141e006003045000354501640040306070348900c02c000c1620130302503503410b00340740341e1089409503924003005118840d07910b6081481c03441c4030f29104084090a6442e00c550700e004810b43c1c44201300d0500c0d00e900c0000d1003c02601c81074509158070b2003810500c0c540103882d0940900480e003003c0003520403002003000c002103244158000e810401c56080c240000004690b0880d2000e108524080030300000045241c45030b06d50b0040c042c69115150502e20742044009401a4000700003541c04001340008100d0b4119407139042c0c071120b500024120481050031040300d42040d000d440800010007004480300e0f0104d0f501c0030300ba01c140707404840551554800c01003121300d0a00f03025190b11000081c00000b01c41c14a0a4000754980111034510030240d4500d0401e5000340c200e0311054221400230040381d100e015031241c2220b80b4541c14207070302c80741800404601a56401d01b1082546401c00702d000741e402443c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 822657014 1250 822655764 822655781
    0xc08010306091b060c1718210708061905060108220609050c0406440604211403130f06230138190305091006030503030118 54
    0x145410f0210303940c0102600b0070354000c82c162582400c81c1011034203402da00b001c440c420704078400046102410031041c00051401000700d681d412040760f511080030807040050000421020004040b02e00d0030b50b070756540340d20080c1e402016580c203103410300280340e0300400316580c4900680740c02040c800921a81c02401d140b540c0003d0122072419011074203001c804996031b0700540d0181e4007486810355440010b101e10f59002c000c410120040040900c000c04402940d032210002545600b40107541061080d05144080e1070403a00231320100c9000207171001d0722403900d00c0c540290800c90b1035a0007405070942544402803002c010b08107000c40c0c903010009285d03010340d06180c01403420003204042c0c0500702000c2880c00030b1486c59007503071800028407000c2d9078824080806a0005015031101b0b0070b00180d0342c80c011004080400100f8407484410311415800b411140075595004100344c144240702ca42484500c100310401036040280034408200c0020844e41100c40c04020075000c003031074551440c020b09022 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 822658264 1250 822657014 822657053
    0xe0a060b0a0c031b030503071224061101051302211209031501080a060e0a0803190605040203040f08090a091109030d1106010306090f020d0c06120c0801030609 70
    0x1ca14001d000c0d501211400e102e91007502c3c0e50386940f241c2c0440c1d0b100207580420042c0002c50030000a01400d00c20050564000307100034010883c0090300c906000c401107950641d940464030104108065907110704010401010000204001e060501544408083ca648041c0c0503001403820700d10583c1c505696560f90f254500d09035001c03004242c104015691041d40f800d482403142d8540d40301c0030f03141e042c0707010b0480718400300030680041d4559842018211404c00350200e40103580241c2c2c046840780004510401e00c41c034110a080420f4900402141e0303107504038034000e81c81072041000161191580382c40ba0b94004026079115070703071640010503c0d06a078000301c001d02d0903c460512044502d4000c2c0070015401c8090b00c2c885c0d40c14200c00c41e030008103181104440d60204004001054440d0b00c5101454014020108041c903540c011420b51030b0044821038462030307a07150820040d6032150f4071b408544c410b00d40902a142d0580c0c0d0003816010107000240101d0b5803180b101007000f15003c40d401d0341041c0d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 822659514 1250 822658264 822658267
    0x3010807050d2306010f06090e01170106050d080a1b05030307200f070e0703200702040219170c0c15090304150203120106030204050d060f0b120d110102040b03010e0a060b 75
    0x80c54181925403c00380310365202c1602403034007ca00940501d6207082076600305407111185a00e0640c00c14440310f4017141c1c04015543c2c0d201e01051a0b00c9174002010482e02410050f59138048101c401060031042c3c41680e500e00920b040c0d088000388001c01225000050343c503103e0204104407040b8000e0402400340d40f80c6030303c0b40c081048803c00004c100c9800301e0b1001840c02c44242e0b11050b0580c1954075009039841c3c030700c00c00080b019881c00104d01030208580064001030507c0c0542400340e5048030124040b10118180f400032405401c1c100c4101070340300070ba46c0d007441c0c1880400301d4030950b10a50300050030700300c042c00700000b80051410001c0d03074001c150b42225043c07414030303041020707460758002548980218034950020075114040d0003102c04440002c0d0800044c8002ea4468000a01003014050f8480740c84100203101d03565240c40240030051224041d1140d0300d032081000d0941012220707000c06031790041c0410001a00c3d03290a50381110f241e0003041300550b81c2c0030581c0d801010340d0b41184041302c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 822660764 1250 822659514 822659573
    0x813050a06170c252109090c23090333181203061825140a0c1407030803070801091a19080a050d0f0503010807050d 51
    0x40c008180c801003504644141030a4643d250410b074588205185482901c00b0211003a9840c071080c42c4010007035001d21130072280300503c00ca2411000b680800300c4800510540c4080c82407200340d03c1860107828540c1804c0340c4100800046482d5a1500228601d00309c5000c070346d0701030701d84042c4520000e00c50302d040c180c0e0145000e140007510703883d1807070a5a8004049800055a603520f80c0b10381440c04000180105540384040c18803200e00e0b0b000400194000140510143c5410481d40c2c0c61409020346200f41c03131002680060710010310241240c01010400031004081c0c121903280110f59101b10316151801c00d030000da04202c1502ea09aa2a07200f0b180f1460318004180b08012000c7c600644403a0f41c1c4051590b41c030f02921040c0c9005003840821b80340c2c0c82c1c01d00344c0a46041c0c0c1c6d00c11f0101c1029960301600a41d244020360500c1d810200c2600c950b0007213030301807210303070303401041504c1040a9041170b83c11541401013165448102d8000c0034000e122540c000400e008225850504010348806654110035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 822661870 1106 822660764 822660767
    0x411509120d060b071a07030b06071b0b070308240102101a0a0603020301090b060304050d0309080d050103060b0909010c1710090603050a1a01060504030813050a06 71
    0x2d950300c0c800648460740b01c0c09021400c1c01180c14141520200441c881c65500080c1700d0300405180ca5800e060a9885005541c025600401188c185000e0410300c5825809540c104124075640407078030008040d44041410b103d01403000c45210804100010001541441c43d01503015810a030302d0408072180903032018829405136203a012412040f10086101c002854000e1800a0b80010050008020303500070b92440c6041990748914624203030710b81d0b070740f1681d00e00315172020035032545100000d0010600a40d034912040c00020003440d41d4a142101c002e2240d00601800b4804003000940b8011040c490b03140c00c0c0d00a40c40d85103128885c048491a11500209070280a4140e420040380955080c405c003009103115200030131400361641088040e0b10032110300f4484060014006000c1285c0c8a025101243d0f40117000a40b20440e10042c41c0d07404d08903411103070b004912440e0005015 = true := by decide +kernel

theorem cover : BRFrame.Cov 822482014 822661870 := by
  have h0 := BRFrame.cov_init 822482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 822482014 ≤ n) (h2 : n < 822661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
