-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2164
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:50:57.729172+00:00
-- url     : https://prove2.me/submissions/21e9a0ab-3d67-48dc-96de-ff9049b20351

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 389028776 ≤ n < 389208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 389030026 1250 389028776 389028779
    0x20030f030108100b1f0306080f07170a11060a09231c0b011e050a0306051609050102030d022823070f171e0a170f0c16020310020a0207 59
    0x703600321a072844102d90305c240300b050407002c0c550548901c08058141c1e800d0003d1083e56500d00c6900b489283da036892901d4020742000e000e0307420b211858411128403c0c005000c1d00809566036846500701018140c403421001c200740c00900d21503031880d0040c2c4680c42e40440c0054000391610f000d0000d00300d4551003003d96440c0606000060007204032035682200444000b0303441d1201801d0001408804544090300d801c501080716115446260002c40c070881c0002042d143c4028006600d044017004c600c100725015504000680e0f000003074070784c98444004016522081da00040391032020b11076030780d0780d42c516003206120f0554001c10104c184a41e20002d4000c0c1e01c0503000001030b948120034004111040300d5000102040c401d80c0908007071003001e00054500316120118134200000301001c00c00100340040d804000c15401602d41c80343c80e644602d480d4450500380c4920a40b1000100124440c420201c0c0030203020003403039640d6059580240a0718110004c07002401c001c1e41c040d80040c0c003d441003840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 389031276 1250 389030026 389030053
    0x1008030f090a0e0f0c09010e060c07061b08040b090409051e060a0204230102160305070317030915191a04050105030307020604090e0102070b01060f120e0a0320030f030108 75
    0x141c05220713000341c910840840c1d40d260703890701c05504030320407050400c0b04a020040460b160070380100103002e1940028900645010b00041c5080d02e4080504c41402500c11000300182c0140e041d941036905005c1c0031602c994001c00130400404031404058910700c19811010742883c0701070204680a00c1400c1610a15640c1a0808060b88036500c643c182c02086030544807503000c04009007071044481403041d01c0c1d42240d9a8200d1020f0442c41d0020344960b0041002001048036240702c1001684100382c0c05400c6251104d0616101c1d203440c4140f0f1242000c410008900d18851411810004203241c0200401520b80b080e0352030244c24015164003407882c010021619250000554103103984c0100400d103003038100340c00000075208914003010b043d90203201309400905c030210018003070304955072017000742c0c91407800082007001c1403039140300f00e1071400d0380300340c0a080081100000a90103042000c140c1c0d074007160100c0e540d4a100c0f00001c40380004034010880c900c4402c009c504941c030090072101304c0c0c0705440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 389032526 1250 389031276 389031299
    0x4060525090611010207061104060f0201051003060b0109080f01150f050a0302060a11100c02010c0e011b081329030f01060c110406060e041404020f091008030f090a 72
    0xc18203010541c04507040261512030803440003124049000941450910364a02041c1c50280522141c08040490240b103200e034080e2100c40c1441852001380011f00f050384142c0341a03101030202424107034450380c1e0241164000d004400041408204444504000c1082c260081010760300e030f208000004400010015001c01c0b900040e9400144100183c1c1c2ca10b5080084035840400144c080c4040c56844801e50403086c0640e404c2801c80d031700c010801e000354240090841d03441148074030600c1a420713000f01c0307581d0f403001c0e6441c1c1c0200320881c041407216150070b146060b8054980500c82c100c200c1400403800b80e2203a480340ca03240002c119580110500d42c509101c4a00080b41c1000ca001844030041040341e2240810700c04250080e204201100003110100301500d500307400134404203a101d06160054207043c0700703080c3c00a104103007e452a04065000850740c4541c0c03160b141c4a10300d40400b03e10041a03503c1e0480040400c00205c80da1066051100a015084404194890500414001018000d06 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 389033776 1250 389032526 389032591
    0x61807031d1507050313080c0c0901240e0402070204020c210304031d130207050a0b0a0608120a030212040f0501140702060a1109190306061a03190b0603040605 70
    0x101a1440c25a80c2d00804c03903194000418001d1214200024003020511b1840140321000c151409006500030000c28055014030603400204510300c925550101ba03880482a0501005286400f94100c11888001806809001e00180d03009100007401c0d80c404000141c265404600d501c46041c241c4041c510005890004544c050082003d2809100078001007800c0205500170003007820b01c5840c4440f4100d000c030b07000305504403a40e61041480c841130111900403103031b2005019800744499410214003135111940c592074902c0c0c2000114403040000e001c1d405503249a4440380044400d8980b070b080a020360b40c00f815082e60994a0b0001d0b8200540318203c40368402c10b1990000c24241d121100d007040100720ae800070300c1c0c01290500103100582e90b0143d46142089800b06001646070642c105142100d03416405082c10710805001d0081a80510003641d40c4403100d9001a00c044628410920150102180c400e230b00140c00020801040510b0740401d01070044100020303482160b5008541400810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 389035026 1250 389033776 389033803
    0xe270609070e0102100510090603030f0914010909050c070f03051206040c090605030406090503040602030d0f18142107060e06010f1205070509010605040302010f030b0604030605061807031d 83
    0x151625030f044612500440d8224200c40d06107c66669182014800c0303070041d400c1140028206180c60550f81d80c00714200000e8110315141403000071602d0006489082a03100300341c4059210f10018650461074802c2c0d40c084d03034000c861140c06101d2881c00420f00e5024030035a000300010040454440d040030f208601209415841c0c010740f650402070706075000d4000803c1203030a952545103080000c0c0e0107101500040036941c00468561034103540880c1540c030b00d1325049481500d8000809502d80702082d11022458112800c10803504400d62518200401200700d0341b501c40d0070986113a1a0b07a903500c02020003c0c0142c908110800f00b0401d441e844076028481e1801060401a040c01205041003141c3c038500e1140c81122005940c0c0c2000c44c4195909034080800b040e40410304005658100e48044c00000c00c910b010050180c103100000e82c0740c0105e0101400d10755903000000c9064440102d070080d002d040000210305071070240300007009846014104c0c1c0c1907440799110081c600200003a0407030301a0382c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 389036276 1250 389035026 389035033
    0xe01080f01031511090301090605060a0816120c0902031003150903090e09030412050a020405101a130905150307060509181315090501050c0c030a0e270609070e0102 72
    0x652074540c202404c2031001ea036042103400c00402c002541c091143c162280d110304408282460f1441c03c00c10704030b8180e40504215000440107100000460180c60280c8112081c50102041c880c2061041c1e0303c0a608401d0300f95100100f07100700051403415210469205490080140003001540380c10303561400310040110f00040e006000c0c001a0321600b40d805101c1c2e108803414903542c1c000d140055656484250f400350402c4459909504190041c0c0d03510180021041d1280c03031038002a040c0421341c41d0250090414081103a15610780c030500d0580c014940d01f2000d02050420a10812400d140c040001d8828490040005201e6014509945503060002c0220f44140e855000740500001c0c010f0825500c40b00c181c0c2e00b01d0016614418184901083c000001084602440e0040c2111006011031001c000c00388000c0d1007491000044a204403800e181680c1c000114001207500b407450b100d41c100308024040c0661444050f00301c80f041c0700b61000c0780c1002c0715031285103058404504003160a80180c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 389037526 1250 389036276 389036303
    0xb31150c170412051c020301030b180a080901030906021b0c040606020a0303091103120c160e0106120b040c02241320060d05040201030b121f0f020a0e01080f0103 71
    0x1050f88081d00c845080340d00f0301c5440d18078510581c001003400d040502110550200060042c05110020240d2003d20071802070310581d080c18582d0340e0344c0b06000c4014100900001c6a103580e9200e41c00c074080880d403005065469000c030040641c0f0310000364480b2070b2180300f01c030302415584c501402240c0440b07009402070981c1da0440e4030704a016262100e0107440038450751455032040d8904021175414200c114070b801351150b00500b1041e04281c0d00203203c61a0b4069900705200031031480701110704599250421540c0030201d007034020f0141140c0500243d100e490018061891500840c0d8116450f0600c00c0600445140900c0300c038408500741c030304402d940401c0e0340500014602d0340503d0411108680e202c0c0f584100b5400090707a035445030b90400c0f001500e0748184000c44d40c06008030029044119507040c04418002d11480e95040310711070f11a20201010980d04040040f540700318a04017541c0400d540d140d1205001074017190303c1c2d000290020709208006402e460b030240855040c4ca41c01a0001d1450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 389038776 1250 389037526 389037533
    0xf140d0806042a050a081b0406111c020c0a0b04150e01020f070b0904050c0307120f060503030f03040b010608130f02220507020d0c0b31150c1704 64
    0xe11201115103200e0008206070840f00400c90100c100c5400140d403419503880d40344c04010440200540340301420304044c601c009041000100b51340070b0768100c0c58818005100b9102081c0307031030260502c000030000d0013010155140c0e4046402500318030140c03000e5004d642d8907640c00c2c003688542e100e84841130340c81c40510140d10348108240072140c88148100c500c601240e04040e0704040c0b1a80c07024000d4a03001420050a0415000c0e1039402b500740e248050030352902c96070141200c650032600107075595a4214010000916030f1050f0040d08001e82102e44800780e500a001065100782c40c1030304e01821103000020810701c590401072140c02082880c0700034102e03580e6401420000d003007049910112200b200309228450113014503890400c01404038883c101180041c1c200b48442056808001e4100066008076045110040d00154441908403c121410300a22900c410080007aa00803201800034424802200e2000c009200e101008020310381a040065411440815901400a16803400607010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 389040026 1250 389038776 389038781
    0x10e0306010b1308030f07030f030209091503030c150f09010507050d0c02011e0f0f05150d0804030503030907090629161704030501050612070b250f140d080604 70
    0x102a1080c0e1402584d0b140c0300305074207540100c00301602d142000305445051682c45030600b03140c60300504003189441552030100d124140000c00c0303000016030300d108031510360320b007002110320084000c000d4500c940f00038a0710301443c4100342d80500035a014507000c0340e407007007040c410140500b000f52200d502e090303249a80d002c040d00300c1d2403502d030540d5a1500541001003401c1d05402c1109164600015205040700c00702c02150958511061038500e0401003191080c50822880c1ca0300e0300c129286030750310699190041c041e20803900001c1c100e000200910920003030019082e416100162800e108440d00e0380f0300b1701c50244000304d130403070761580c1c1c00f00c4414042c505038001c01c42c10300d6585d003d040c402415150b4800c03060066601902030303c000102001400421300c10340303400c1041210b032844080c071100001030f91030b000ba02800c0c5407070000191681da14143e0204444140490b2610350216064504041203803408006d07040c2c2d07001e00904820030603a10007142d10010000a074032120f44035251141440300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 389041276 1250 389040026 389040037
    0x6060a090e150d03080702060a140601030b060d0903050c0f0f0a020d05150103031112030606180a03060e031c09020d030e12010204150225050402090604031b050f010e0306010b 77
    0x201c1c201400c0c07981443d46440d5000800f40d0f000e0345840481d41410311001346000c0c0c009010005451404500311124071040d000d1070f03000002403070003081003084c18000500c14403842d1401003620b481d2007220b0081640003409003070488402c40c103542d10b90a10001907a00c50542211001d1183c10400d0f051700149009204090f400303000c0e00840d03c401402c00c1009108120a80041d000710b048075044182804042250414030302c1080071250441c104080804c00d54090014200e2480302980703684403950700c6509042000b0345c0c000d00203005188200c440c40f604d1390b1101c034813440e602c400607145d101d400909024181c0116405040d00e1034450950300d080310761001d05048030343d004c100441e400040300800d002510150402d01880d010980004001a14141d90013090200840e843d41040107005035440c25801106e0080e1005aa100100e000048291203240c0000b00696280441581040301b035103c44001d4503404e841d4030800e140040c005456400f0401000c030340c580d20110051080c1820b800141c074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 389042526 1250 389041276 389041291
    0x2030a0b150307020304090236090112150c030e030d020711090105060d050406020405121c02060405060c030a0207020406090207050c041a0114092e170c071a0702031206060a090e 78
    0x4841440342d981c40d101040883e8030700c809442540d1f400c27441d5241c00c85840e40104070b01c040e004400c400540d11400e000c33101d003001c902119a034010380320280e4000d03080000174070036600c203403640d42c1c10300c551000083d0403c180035200313403205045c140c00e18100404071a0603103000501243c10000c200455502070300f0010021103140390284000296038807501c1030211030b403540d407014228842800c0c2e1002c805000b24131142085520190511010400c0800c100b90403444900406982c2d42c4c40d223100b40040e00c60048000d400a2600d880003844603400c2c3e001c0d042e007500c60801d0702c0b510f41c01c00082000740c49408200003480704400d15640e00b50760150003000303803500146200ba81021031203000602540340e03403140c0d4030740c51300000e1603501030982080c3c100724100d00c14100782915080e00340c4117010790800101051401c0000107060824807a0389440c4130403e402c100c560f01c0c0d061400710740094480d00001946d000f102007040110311f003450b254050b0303010070700d9030765440301c02c5464007501e2040c0880142004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 389043776 1250 389042526 389042557
    0x2030105062d0d0b031c082403060c04030b06011d041e0f0c1b0f020f0d1506060f0e090a0b011205070e0907030917030601030f02030a0b1503070203040902 68
    0x140d000d00750b00080d000d002c80035400011600c00b04800c0c10b04000700c55000c1e10520440351080c8210a40020151350090f070201c04140481c5c0f072414146078000100d9450036032500c00c000c100210f0300c9080b0000c001303503480f64505a00e00d441e2000151200c0310040c100604401800f610840c05003800e90000c000c90400294040c90004088001022a490345040d4403a80342c840d01c0ea004400c0c3c100d0b00d0f001b04421040d0100d640c05905840750901d03d500030000034804c418000194509540b1b40901c035407099004090200440030500c1c0f050004c1000f440350701c000c9080e4911401006000d041003d900035406000319030544c1e5410500c400404081c84e00506000030102e110001e222035200300c07071258201d52100e03044003440804000b40c2c0b900080c2141c0806040c890f02c40c0c001814500720b000403890400c041922600e8020058018150b03218007101c4d03446c40442000201c503410f801950340308600356101072201c429400e0030841c0e4442203e800c009680104070400c0240e0690740103040032644490b08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 389045026 1250 389043776 389043847
    0xe0103150621290303040e040807060b19050307060f050714120c0a02180112150e0102070f02090109050c030f09160902091203090109030807060902030d0c12030203010506 75
    0x404103c0c1e40d0100c03103101021440941061181c40248203001058049004505080c6080401c0d681c118005000500010b030200b151800c00c540d030b410690b000c0303034000c1010156010f10560381c41c0348011032088034840d00c1041c1c6c00081141c0507218107413100c21144e0340c03e460060b8a03100c1c800f10030400705a50461384514402d0300c1c012070800780600f500f43c281101070a5803041030b0041021080d0340714004904030316054010048040d041015059140d80071100c04d42440022921000414038245954165400002e81104101225401b10385440c4229800c0d1001e03600c030758640007222000c071030b54040001c003000403c40f02e41c555044c00d640041d958007190303001c1007040d04240321076209a006800310340c0c02140c1c50496240048018003038002010080d82801001c000082181d80d5a2102900c2d1440014405040c8081c0d50003581615030054220ad080414048004103c1d00f85850180c41d100c00a56034542c40501c0ba000701c90407140300401c030034103050388082100265603040e40f62001200f0703107050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 389046276 1250 389045026 389045087
    0x2c0d050604030504030b0a180303050405010b061b1506030316050c060f04060305090c010f12021204290106080105011b060e0705031917130308070506070e01031506 72
    0x4540700d54803d5807000c0e2103614500c1c21100049001d031224182a0030012071a846c58044043c080d50380341c061030046510384031030a2450040c0950940b0716040400040e40070f900071910401820b01101ca08100d4214820007001300307940c4c280a48110764950804c11181501114403014110014060420303188010103074070014600c0c0d80320310f107180342c00c000201301003003801e806100d41507000c0328030006068510342602c0001c140031101d4401b0b00c00c0c802102d45501c11400c440c0c0c19103000f491054001e288604150500101440d03010301c0602448840b5403c00515000e0ba00e8118101d8080c0e448110281c0d00b4040103464040132412001502c501f4007000c080402da050207400c0102002c1005420014241020b2500705403500364040e445802901c42040022040b00795001c00042c504515074468403039900752402d052041e070024001d4000400d03044240040030552a000d08a5030301c0b1041590171290040d0161080621500c541c6580e5880800c1000d0040040e20840c401e82e020500c00d0084960 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 389047526 1250 389046276 389046283
    0x916020f0102070b0f060319080310030f0f02190b03010b0a050909040c0f0501050406050f07020301021605010212010e060904020d210206091e0d0e0a0306020d0902030d2c0d05 77
    0x62060f02c0e0b031310310348003849840441840500c0e0000c0056014041142c6c1c055003081c40c02c3c00b191760091908800000040865001a20610146601105010b21581603080080c45006c00c01402e81c807400d01035a0f841212840080c04108542984111500316071804083d415150030011007a401e102c07081102c0e440c0da9a46100d5203100700c2c032400341c018800e4241001a4546000c41d00800c0c1400410031042c080b079600402510442c0015144c0d0035510816880460f019004010402c4083c40c004230080e03082145c10f402601914050f0050021640c1c0d803002c07042e1210a042d15001c0d04048182d000c42c004d400d19401748800a8021000c1c2c1e58521511481000c003c0c0404070b00c01d00513005003013889006081130158010b00b030311320308003800001c0f0040d480d01c0c3c032401504815820321007410081c1641e0340ba4042504000d6400031000c5482e4110400808007130034100740200e2180c010145102d41081c054008285000460841d80000703460a90b40143e521108c4400194041030650102001904c01c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 389048776 1250 389047526 389047537
    0x50a0c15050426070605040f050a150506010504050d0303330602010e031e0a022401081504051207050a020904030c020a120506070f18090b18060916020f0102 69
    0x3800002807610307042c00c01036400812094998010704103109040c0a202400c0291882e0a801400008154541e4600403e1000b03101c03030000c14038040c81c54242d05002c00180002004144c01c0307000d00495440f10011190340c400c9000e040d81c050000044800403074800c0d40480250310603c400c2070780c42010441000c0b040700e28203280ae04181c17654907040c00401e40c2070040d040d500c00507000039818a003804021f03006c0d0010740e0320ba00818980100d00040041c0c400c000061044403680006001c20340b0030702400444d00d8003409a02c0192281ca20007080034842d00711424131440d0441b020b05507550300c814014417542d01c410003d071450301c0342040c81800350365002c20550042d48203443da6246040c0500c10302c846441694000c41c072659809000401003000070543c19404005441c101c0702c04403480c0825a11075481d81da010754a40c14400000c1140c5145a06c050f1000b6001c95206603507031501160701c40d04c800704544658000d01c0320b02c082401200301101851804119005a900008041c082d076422038000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 389050026 1250 389048776 389048813
    0x30e0a05060702071a04052e02010614220b03010b0a081005180309270f0901050109060b0403020f12190b0609060102060f04110a09090b060f10050a0c 66
    0x66081c0401160104101401046001504e040105e4500b0120700c45001c0d5104403402144600245a0080c210407141083c511110313504400030010140c00134009c00190060310a88517101c88664614034141078104207696001c0384449001d122031524501400c00030130001e80542d00c46485003004d59900003000d010b070a211004000800740c000103481500c0c0043c2c00100412600490700840034004411038050074020740300710000c41d030841f031210140e06400c0c42060045800d0024402c00001000c0702c0782c005c00b4400005d10050f40c86c0e681000889090b0b01c5103001004c000c002c10030041c00d241c074007a9140500288102200b96900715014184600c00c103405000a40701a240f008102c0188060341d04200309640765500c0746440c41c0081c0d80e404001d00102c211003200300008040154400d5102c002ca02c020f4061508103540f41c44140141040080446101c4200e00c00101541805002c3c0032111200402c04011001381034002d590075071140040c2c004104404c000140070820300c1c0307181c01c01c0f00c21 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 389051276 1250 389050026 389050033
    0x1505060708030a06090204030803040803060f12010e100b1e040624030f1109120c030106060c02010206090c06030711010b09010b0405130c0503181c0302030f0f01050604090c030e0a05 80
    0x300728210708200c4c0c0725500000d070018030500062003c641c111065035849948040d10a58a86802002a402e60f5001034080c6c0e1080381083c950100810641016892500300b00403903680d41c0c200402d010664441d0700000b508081e8a8083d11102d2086040007040d0030342c0500001986515108901e14a4401c68002c95442c1c906030040365400b6492320408555007009013040040982403130295000d4800d40c1d4030360784200418492850f841c001400020029400100200f0015944041c05031403540d48400990246c01a000000c200742c1000c40c103100c0c0014000e04003480c540e117a02090350210040a001c444943d41e65244031015110130640e180603040314003400f921249030400304000c041c450080d804606040403014622280c200c0183d9401c0403040c94408001c04007a140c0034540b10008014441c110104100b20250f640c05500460007840407103189202a9554100204007071003e2041d260040002c100030800c0d4070480c0e00600d0700150794613003c65954045114a03182801c0d29030199800d42 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 389052526 1250 389051276 389051281
    0x27030d050d090218010302130603110d0201051323040e0303040609050703060c020303010e0c0a080114061c150b0c030a05090d050609070f080708120c010b090f01050f01050705030706150506070803 86
    0xe8030323481c0b545503100c0410052000e9401c2d81d0b1092402201d18001e207002d983c445c86803100b168001c0f401e454a44400d891070500c110f640707241084440301d01c5003c1400c00d8442c1941345a15040034007840c4080b07000c00c4011072171a169513076590000c0801c25010b8403540a442e0000c0001003950007403110005890b40215120750410011600029024100c60400b21081021703c551ba6003102c0e04034112104a183c000c00c0391070240110303561307101d280c1100c45c100c0c405000c03801c110302c89680300181c6d010311302d0340c032451464440b20307213908900c9401c4440100398014480342105510400050080031230180020f086081c082c0c0d40d41d85801010303200e4034101c1c1c101d0360080c041c402c07034080810700600075680280001403420248689030312000014614a00c0002000c401d50b800c2500941000d0302301500003a11840c1032803560f0300d1540b00303004140c4900b03c180013180780380d80b1a00940c0c1c0507030b8000300a9454880641e560500602d15890801461030341d24000185507916400a0700f2224041c17030003242d032407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 389053776 1250 389052526 389052529
    0x303042409120209071e02011e020f030f0c09040504150b09010515130f1203022e0507020109050102030a0c03050615040b0a021204060527030d050d090218010302 71
    0xc8141881010000804410030962903088050306800340c064407070b41c2c40751302c1d0307101d08030344070b411035044600c080346444600c0c403505505600480f0304824480e44103e51075108040da406a00c200f83c01d11001e02001d10214000341d80c02d40c6015007107000c9608451070720440d0030204d02540e03001c8400b920510b03060320802c40c028219000744a007c000c104c1d0305502030340c14000080c2044020050303c1d81c4d5900c011441c088204606036140010305494148280007a07661100300700c003041d004030304800500841c025408a6145109401c051174031340140a90350000f1082d01000034000281008119900d821446020070300a10042d4021038500c000800c001c501c040003c1c0c02e072000070b45036a002b4141481c9162420901400707903401c4e903115003e02603440034035420882c42c115100c0c06801017694002800145660007d00030f08180040c000009051441080302d2030340c0500f81c900194241d0071110b000c0b040d10340301d02d000f8104500361040001740741a032600400c40d030211448078030303514401c90303401171055 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 389055026 1250 389053776 389053829
    0x601080705130e01091a03060a09140703080a110115060e01031b050306030d0c0506040b0402120d03060f060507020a0e0c07060e06061f020309100903080309010606110304080c1e030304 81
    0x124100f071081b020349178206000c26590000240890340c000d5580364480100f150004818169074040c0c1e08642d2569201e0803d01507980c0100354500c003140c080c0751150464003060042100c201c00d402c207400c8200e858000d00b41d80040ca80301e0514101540c6011541070420f185001c002d013012960380351034807032800600b81071524030103180c000d00744088400010001100029107a40c0164840c404e06041c5e180c130f1012811044003800c420586004407142c030843c00d5070580c003050841e10010520f09440b1307980c050503250b40c4500f181c080e4000480b940c0a1140069450040381c00240300203c040c41c080e1ba5481d400c0488600c618840ca9540180b803d00040703103404d268039111b80d01744844000501c0d460f9000a5aa4030440400c5801003071200003030384005001e81429001940c008410235624074101514900130b0140c1c0c02000040743c207012000070007600002c1a2820744a03284014000e41140b030040200304c0002c050b10b41540e2180c0301c102e80c0c16440900140000b04004070103498100d011170300300d025 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 389056276 1250 389055026 389055041
    0x22d0f03070302030a2003070303020102030f010f060e10021011040503070e071205101a0d0509060c070620130612021e03070c0606060207061709060601080705130e0109 74
    0x1296201d40002c2c00542d401161884003a80d02c50361a1858525030055000303040524210070350306025654000042c15019001540700c0c11001f4004a50ba0381c03030302000c415956172030290307800044404070004041c1c101030002c0c51405c0618011201c560400070280c50559401c48101082c0c0803004c10100a14281000024017070001017001144626060300018211051110504103103900c070408502c0d40c00355a16600c01501d050814401110850f04400b10158400c160681d000c41c80c10001419111000c101030f07001c0d00811810b11714081a50b118180036044981c400c1d04c00803039042890261510780303801458418032801400460a260003c0640840601c4ca1440d101d9401000b100046070841040c1101040300c00b18003a84945404104071000308010100401441c544000850896000103c1e0000c4500702d540c5c1a0100782c3d61035001109120956040860b94440c0c00403071101d601078190203034404001d141041c2002074034044400344035101d5001706a10754640c8018032409620703016046 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 389057526 1250 389056276 389056279
    0xa020a181508030a0c1104020d140a0506060a230d2304050a032601170d0513120305070b07180602031207031e1104080105070c110d022d0f 61
    0x11010740b400e03403500c0d100d10509a03a0b400b088034030b80803001045580c05492214490241045407901070410b480c00043c039203821040c90b81150307000010000c104034000c1512400c40036054130f0030290091010b407541719980d41c0c0f8140802c26a10a030300c3d00c580c50409440c0810781c500011400030742404203852401c5010100e44d020250500402002c02e81c00101034401641c5803030520350f401158031190810361800c5100010400c20305000280b0764100070054018034000c142901c0344030482d500181c8a6208000d0a0188901030030810821020038400d511402030003400d1041c940f240701d56601c80c0020f0100e8003640402c112081c01d00072008004001d5014018900055281c070380c120902c0300004200901c030070f0070980c81d402c20101107403c0d40300f462500c04e9031000a101d02c0f1507000240c10340d500640035180266180400081c100ca02c5400c030070301c1715a00030a1441410134880d092003c4191074901c1079800c85081041c01603010450003c600010304003404050680e0082002c005c800d64004184a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 389058776 1250 389057526 389057561
    0xc10050d0914064006060b0706290904060207020307031506060f08040f20030304080c190b0313030e09090c01230405060717030f0a0b030d0c0f050a020a18 68
    0x103000c0481c013034900078901245039991400c4048075180c0003003d044160085000f14402240410411113a5001104264021366051804804100b00b054643c4064520682d00c00300420124000c142d140e8000c24283c2d0012307082d20441038494540d000e401404c0c10408a04070703a56441045680d900c481c05030103c01040c640b81c0610b00301a2101c1d80784905544014240c200c0c0a6102800004142442000300d0b802030142c98403250744a805036202c0c00004241e5003e5000402200491242c27406990150340b91040d1003815900c0d8401807800301c0c0554541101803041200c0f50300810740e5111592132103004404020020320022500040001c034031400c0c2a968480900d9100990709407900a0300c0644105a03121078851085050841c03e4222030091039401040000602c0000042411042d01c100c2c18400c0c18000032080c0802d161b80d540c150300070400080d0685110800288002000044c414015400c0b945900701e20b800040b6a134042d540031762254980e201c803c4151141c0303401000062100ca0556 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 389060026 1250 389058776 389058841
    0x5070302071104023417090117041b090c1215060e19030507060807050a080f0c130e06010f030b0d0f05030403080f040f05030c10050d091406 62
    0x10040c0c0214802c2240b0300c9503030082294044000401c0c21140b10803807081c220784100040d040d103019070070700074442600d5506480202000c010500e40c00c403044040103079144103241e100b064904501071405003003222070161611440403940b84445003031000e850091000181c4041c800c401400030740102180400c10b40c00c00e80c42c504011145c02d42041158001d0401d0f80300320203980005882d50350024218002c2c000303040804400d02c4000114034003a20308644034040c1c1c540f01c000065400d409070701c1c686d0740000c9505000607541c510716441c89410400d0764000c20f00f800442d41451480103e99003120001440d81c40400c000ba40c2d01840d4504002c8107400c0c10881195010041400c01648541c09401980c0081c1d00740d04005040080360002c0d07811008140d11008545aa840103601602c41c00c608070f0401100424036190204035951440002404910080a0100d060f06c154010700c3c25513010030f95454955010405884507280803649010141c00e191a203500c10312894202c410341c16100b15420b080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 389061276 1250 389060026 389060033
    0xc0f042c0417310306050618010605401d0f040503090d0506091005010b0306040b010e10051e0306030703030309020406031208070f0822060906060609090507030207 72
    0x880600301220b4580082d0703640034a21034180c2c00310584066010301c010066149000c9040c040f00e4100f42d0f8031581041c442d40d2500700402040703802d000c2e0103800042d00700b4010003859000c1d000920300c8140c020000703100107645228020303141d8411850000800c030260f0b00740e44018924114207000e420600c248449081071203d00c1c00304038100401c01c8440c0303120800418140002001542c8040d0b50090840000c2c203a10714007182c80c0c0000f616000c01502c6a0640340e92a0900c8e80a02c6060b540c8208955055640303950070032026103100d030046810300a0150300140c441c1c8503e120481c443c4171320b44405d07650340c0b840c140c031544440c62103000e100110400e00130f00c00269008603988080340d80514bc0860001c1003400000c000b000d45601c01843e106504064008060704030a4091007500e068407107030110b4140407030a9a01c9001200c0700c000c200f4070055500e603103a040c0401c2c1445507001f90000181d40c1c01d0303552524215802d5402100225415800c1040002000d00645500441c985000c2d82080001e56 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 389062526 1250 389061276 389061293
    0xb0721050a11073b240d0210020102042108070b0a0b030304032108090706050714010e0102031807180203280e010b01030501030503040e0c0f042c04 65
    0x5071000c0c100036400c2c850303410103501000b078000a409243d1a401c15041c02c080c0d104502083d484107000400c241045091810b142601907070700c180c54015464a1112500d0001c4030103400d4500e42a81c03110386003e989000d80c803181d004407802c48064000507907450410301506402008110043d40100609010030002086c05050301e030050b501c549c607941141c489003071801c0a0440c0b108600d40600c000304000080c0719440c901641d04620000229001c01a455021150a0320495064149511104007001060302c208020a841e600130380c0518035812001c031030b144c00d441040e01b500e200c50f900030052006040026590301500501d1600415010f46803005d4004082e00d03806d00b0500c1594007000003007603901d260003906413038082d40791240089a0b035901014020903103143d07035480a610b0440c501c91554083e125540c180da8001340154203143c58610800d0003590014180c9600080c107100c00685800d034038000e40080c0003e0001041c00600080181c60921840c803900116600c80c0380600005c6803482 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 389063776 1250 389062526 389062537
    0x50709080c0a140a0305010908040501090b1e0a0311030f01060e120c04020306130c02011e02090d110607050f1c03110307030b06090a030b1902190309050a0206040b072105 75
    0x2c048981a020710070f0300085041107280e0003d0318650801b10700b0340c10030a9040c010026600c007606d48841442e20707807030740034254060254183c20001c0900c0c040452910900701804841181d032a0103c1c000589100240c52a002036800c806000c0d9001c0060008a4208040088011042d10004071800b00c0c40e03030107a50360650000e0503004650020100780c2c40d0329440408040c426401c2c3c0c2c14001e006a10b41c0c001e00810b240c0c452813941c04001d40c07403840028000d0080304c1da100c0d4001c040142484c0b05484403501c02c0c0314034000c2c60f03120313100700541c0c00081e500380002c0c00751001c00c5016150031451800440c64150440000c1d5081501c3c090b501d103ca022468240e0f80c0207a0746140c00032b0141000c001044603440390f022441d91140980000000304200c42c1c019510680d40040c1c400190804021810168000c0175144854a0208102d9805042c0319900c082801d5004404440c4510402d4000c00d0360b80d4003a4101a5040500043d400c060007507a40c14582e40907209680c258000404180040050142 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 389065026 1250 389063776 389063789
    0x305011a1f02100608030a0e0a05030a021c06050c07030f1b15060b0d0c0e0f010504030b041a0420010206010807050d05030c030c0304050a0e1b0702030a1203050709080c0a 75
    0x40c01c000003a014420003031180a4544004108a010740740c407011a5a500b000050000140550461504500f003112a190880314060018041041c0990802100c1140f06000307120f222016103200022405601030140a901002e00301540d0716042c0c1401002c1e6000c051121090000884c9004404002034500d808002d41203119603038000c01c14840100981103a600c542c2c1c04060209000600036030550202904101070b031a80003000c1000001d11000110203000b8502143d404e00c03040000c81c114003043e85d400748c4a441e4901c6400c1d58509074404800b815142684e00450340410705030781421802006201007002d0000704003642c5000c4000750348a403507024040c003401a5401880400008201f42c50012169905076901c54000c03816440e40e80c2c20510034213216000c0b50600060540c003280e4524010b8540a010183c02c0c140d031002c45078140e01000d000c81c1c046c42030403012000300703620201402200030550380c04102030611041c018070b00300c41c642002d8043d030032901245a003a80c1e450505001c9a50b1b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 389066276 1250 389065026 389065069
    0xc0c070e04110a06090648050a0506071b02151606050903030916120204110d1401090e01020a0e0f030a080a18060509031b04060b040f0305011a 63
    0x45914003502c034002034100389a0049030804000c54403903007140c0400d090729110303a034541050b000da58066400d8200c03a080303110050b00b070020050714000602c8501c810740e0040894211782c0e51859950310301d400c03884c0c0000e683d190801018001c440e84d01218000710200c815038152101009a00000e40c81b9240e04541100d6480025816950030305c102c42d82490b09421100400051070b1000ca11030700c90b071048030120502c0c003d80c19841500000301050b081622a1210320a029800c150b007848010040c81076201540c840500000302050142e010f23806a04800e4042d10000c0e501d01032004044d0b0341d015140180380d9006108406445502021411420390110740c903545400b4150040390405110100103014540b0002c4d00c0602280c1000e071100d400106480404400b5584040c00c43c3c0901a0344002589a0407481070041c2080781c100e40040c1880006000040290780d49248024981c070542c0015911420f101080003841000c2c80342e0021805000d13a000b11902e0020001a072022850b16047e18944 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 389067526 1250 389066276 389066281
    0x90204081f0b030706030618270807061802151c02030a0b0301020f0a02060618010e15040f140606040b120703020403060903030207050c0a0b0d020f19030905060c0c070e 74
    0x7402d41290580c0300d4050162090b0036210f540003030141c100c9014032058000c407418072185240c03051085440c8070035a000300c1030070500740e000031441018410134181d807586018009a00840c1041c81049400c140f8000300d040d560b1010700c1808140d069a40715044d180509010280c585400c010060501105042005a40781d81c0c07010f0010042899414103074041d80302041d06000f2220180090800d80388030f1f021105103659000030005130101c0300410b5100c82c1c0401004200c032420420000380c01c428000c1415016410500c040390448411940791000c2503100c80302e0049880960002d260440700640740b05181c01e0500342500c1c8a44900b500800041c0d1130800040c1c641072013035040d2130203103034804400d0182d2816420010040e40000b60241d801d07014103034802e01c051420203c1d8038200c42040e01c2490400c00260340c07900094015101c54458072204218a18600614107a9448071340d5282e1000210704c11241803040c5071441c000c01714448080204030904c00350a001035103904036880c0c2d402156440c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 389068776 1250 389067526 389067583
    0x2062202060c0303010807050111030a0e010f110d020c1005040812070c0801020711040c0509030c040b0406030c090e060106020703150f0902062d0708030f0405070807060201021309020408 82
    0xd1141c030240039100d003c08000816000d402103242021243c0990b15010840d841441454a80c428142d80e400802d1440b201001c842d4090300160722045801e05100703240014100d05942041a009050350050304000d0058001d440c0c2100311515140700d03494407504141c02c100c2100e5441c1c840c0d43d1f040b5801000800c420003000411050540a089020000d540b104101d10740354198071100c01c03910784920f0030b01d031180d885240b01c0c030280c42613800f0080050411410544c10302000b4669014000c1e0029180c00d40800802c40e5485207500a0801000000c1c04905880c205410a481070700010708540000340100b01050f2100880e514000140c9000903801c03071549002c200034107140303100039000000800c80701300d5070003a030001a074603482c2c1800042d11944008900304842c40380030402407110805102083d0090024028603074031610840488a15503142d002003403800205034030100050b134000030042c1608200c5c411040043c034090320194101030030045129120310700007402d2900c0b00c0c5404c0040c00311 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 389070026 1250 389068776 389068789
    0x10e030a210c0b182506021002120a0509030f04140406060f0c170409051608090727060801050405070305070501080408190c0c08010f140402030a0201081305191202062202 75
    0x48085010702481d406000403c0611038006d02c40c44001d4081d40d8103a08500425008442000120361400d22841d911080040010600078040d03100a210074043c0d00740104007200104003502c191800500489098000c210541da810b410000400c0008014050070507046401661410381c003000380d83d956103451070250441c0c051076100c025503606203014001102903400700c1c0c02c007181c802d07603c2241e0350743d9082c465a07803140c0510480e4400714900301c0c0105824210003480d8041c000424021601c02e507501041425a042030b1001c0d0f03090782214104000304030081155100510080c00c000b0242d1034152514240c030300070001c51540b80011920101c8070244a00031590760b0304c0d070200f502041103498070407032402040f9004080100c50301c0c1610240c583d002841c0940c0c0b0881c0d0090007401c2000955004481c0508040c1c00d650300c40440c00500c1c00018010700081c6000740304001401501c0c115400e125600c180302402d4481950400c01c140a080d80b160b4240c842c014011348207410800c4114400b2950 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 389071276 1250 389070026 389070043
    0x50607030c0b0103111e100f05070b1e090c0f0409022e0f03090807080903071706070914010e12030c030f0414030d0503010e0402010e030a210c0b18 65
    0xb100c6400b0004010483caa007808250b10030151444075403c1c00c003400c0b62501b14818203406034454241400d00204034410380740c101100d1001c0c40c019042880c1540e40c0e0982500c180e502c00311112113a40c8034007001c0c004400d1283e0000c040c5000b419102c2c140008121103c80c0c8803c4140501d85030307101d060554a540f00600074203030780c000640c1f069988110840b032400460142c81000240000011500070f403107400350405c0c09401040140c034080745030380c0310a840c5c1e01100b880c54040c005c2400014a10a111440c4200c00003414050002407920740001400c1c034940d5003040c0d8042031403001092459070300c80038012031084141c403032140681d684040c50b0303e98000c403c0307004154400000c2541d4180380340d201030401c88000c100000c640d01c981e44100b645030003400c0b21050005900303000410100ca032100300590868010b05200c0451003042c00400c2c00c0165100c8142d6625420f40c03401250a440d003c4003a00d5444103240088074a28203a80c1c00c4560400640000e480e4180c81744084d1216409004115 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 389072526 1250 389071276 389071283
    0x5030406060e15030606190e041704060f0935070b07110301060803091e060717070c0b04050d0f05100c090e0105040204060530070c11120601050607030c 67
    0x141603d044449107009420300740c00a0300030b00864002c14514105181004c030311031503103007840300303428200b14020959180081042d207900c03010000740300840c064400100007034141a40c40c0130642030040c401400720510390340b00005051003079034414820a19030b280582100710352140640200811595240740c1445a0401003a041000640d0401c10840e169806494202a40240006a80c0f054069124090004c01c0d94009440941360082415036110b0030b51031942c0280060304244071070301c030020001d017403c190900c080000642c4100344103828050400a0031034180307007490701d81044081070005c11560070040c500c040c660300010400c1404d01401c03100303c0103404104203400c1441c900030024942032203450410001d103000401c55040c2802210161480c503165903142c0040e1384c01c4020305688098289220603900c1d0f507030308809000c8907840c60103000f03d0f83d0b60428400a41c200304d031000321700d001c419100300301c10968101a25000304d001411641c00310740d0306032661454201900c0700c086602008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 389073776 1250 389072526 389072549
    0x4060f090b0a090801060503060c250b0406020a021528090f110a14011e0516141e060703020319090308150906010c120201020f180411040b0a0503040606 67
    0x441016910002c3c10b400c40e240140284a80b9941c4c01c14075442e0700c4c041d5000700803d001001000c403003203020090307441d20265040e00041040e0482e141c4001c40342064030304a500300e4000a00d903440716810410b0030740b007082c00c0b1070b0701c1e030142048109600403812142059408049240d004107402c1107941c040800c5c0c0c0c0d00500d407070340903246905d07008500c07080b0035070760300e100305030340b03040841c40300c04e46000c07130061381810703143e0340c00d00311101441400118040044008004040088803104107a8001c000c1429203e2411001c000d400c80054074241080806c80014040b8842641c1440c000700241c03840d000b0105080050780c03030725a04900f03952a155180340a4000341044086000c265201111703501c10b070319182e0700100700001102001034500f003c1d0350560008000302d03201c002051981c80c1c8002100ca0600006242203407401021200f50030100c0e0305a01c0c40d0103080160941d040034090072918141242010780307402e0809082e120329000b500d14400c100300d408400581000a01c0d4400ca001e000400c5d2507 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 389075026 1250 389073776 389073787
    0xe030c010902010f180918050f1515010503010b030709080d081006030e060f090f012904020c100e0118051006081b1302090d080304062004060f090b 65
    0x918041c01064200700d000924504001040500c180d2180d507070780150184042d191498140940d015140c0f910b820300220525000300d9000a07030030401e0788220303000d00d03010305200303c3d00388000040c50000070254102d0f0f40c0890115003140c0e0348a0122815195520f03446030b140d49603000c040b40e4000d01900180c3c41031061483c0c02c80c01301d07000088a03215103040403c1006654843ca0210207a89011240013015400301c408111220105200c9039488480ea0045560b82081c1c0b2412600392182e101c98100c118004110401400e441c040140e50900001c0e5410b40c50917030b0f1480b0065403281030044042140d941c501c1c00c0164500e003900304c02052141201d192054110a05055440340c810000d9055850f1800c04006500e04001c10344850303621300800c2100e0f0792000042408104848080c008842940c00c010500c2c9550b1841c0d204001503001d030034210789038905440c2900c12160b0141c0130706542c1040d1500000c01040100c2140d054561030b00c2c0041c11580038140a48442c3d150790400e50201d640803ca = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 389076276 1250 389075026 389075047
    0x2030a030216050d120e0111193e06060d020d0c0306020406050309101b03020703050d090309080f0303040203060601140d110d110f07290903030a0606030c020a02040f0e03 75
    0x1d10301c114481070f4104000c03203041d040c0160b00300da03002619610001028411038580414850f10b40101074140c1c00c0611810203205454074120aca401c140074100400301900901c1d186d030744064110107901c40e400516079400c1540010300c0e4042102c1e4020301c100000b1040c0c400300000a030000c0300460303000d201903450726162800035100350400c55081c02e0901c0b585d01050160095070199410031a000805040300c1c055002c01180a58001c171001d0707017480410800510760711020300c18141c025010340c1d00d45d149107080031000d81c242a02582820b0300c0d07510600c14040540d07004a00f850b044031342400c145101644008034800240100d68903403028030701d0061f00205100002008000c0c0520f1040200107050b4800600c0d0355500642c98030200309c01c0c0906c40500051080c05506006050784c01c5556001c4400114904000c0000c071003804054101200380411400075000304006461641401e20600003841d00c001e42e211401c2502a214a4441d100d44d59504900d07480082d01401304010386e03650785031545 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 389077526 1250 389076276 389076287
    0x80a17280801090b0907080103080c01020c07030f0203150114061b0d0305061903110607020f0d0c030605180a020906120f07051002060613021305060d0b031c02030a030216050d 77
    0x120f035598a90421030001001d1424040c62072142c0c00300d44581100b030b400d54a0707841843c1c00101d04150550b50800518103040c80402840009500c103042c42082070400d0301c185803c21401004d0458000c40c90700c01444007124031805032080c804241c40c140c1e121407002c1d00b50000d2215569951032140a1341075241c84650b131680103148602d80540340d8000b00c651421419483d80c10610010303101205202c041a003e00e0301500600c2035a00040030034414048510008401c283d81810449684013064410810403a2070f0040c1075000c0131445950301c0d8010301301c08140c1c541914900003403040000b50700060752542c881d90400302114802c0111000140700705901903444146005d110f124205803030440f1011840061250f1088401814145070000e00030f2000010b50005000ca00c04085c25100221307907520380001400c841c06001101140c5a0b801c801414200301c41c1d000e108040400c0c1e80c0050b12401e800204840f4049041d240040e1354000c1081c60000610b00003000800c0c81c0105041c1e00d040c1c0d079100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 389078776 1250 389077526 389077529
    0x90305160f02212817070203010203101503020f0f030402040f020a0306060305060402030105030712060e0d032a050901180509040f03020d030e0705060307031b02010e0106080a17280801 81
    0x18045486802c0e40b0410b100701e444484c0b80c0c480756030700340c400d0080001d001c1006181104149006003410000194002030a9130421149640509a121001c1082c6400d0b40289e1034080e996007002c51608442d10000c51051150780d001c807003075080010100301192a16130100c1c0001c0c841010854550590402c0100034043d00e00c0703010002418071000c00e0140c54944203c0e4100d0b5030042c000d201e01482e084421240c01451070007a0345c0d85544403400d034522801032110f003841c128590740c00104420ba400d14000040082800700c82d00b0408102d140d10150b4000003151000c400034200b607612043c40c20900305811001d03030481c980101110f0240001c12003442007440c0014425002c1c3d400001140c0011011201d42400c40552980000003c220318100000110341003000da250126035402c4050a00458000d010f641c00010703951035031155080380c02842540007900b44c400c0a8007240021741c58080c07113a0b024818001341074100107103032440c42c01280c802684c051101035803005080d02c1c214000d000d440c801d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 389080026 1250 389078776 389078839
    0x3080a060603060e130503071b240212031807140901150e040c03060e1602010606020f1f02071e02031203061c020a0803070c140103090305160f02 64
    0x9141001c600781d402401a2401c0d01c088006014031903480c01c5c2e00d00030502c0c40410560300c034002001180302180586190114805a80c55500c00691500403008c0d68400b1004900d61790030842040d810720140d000c507000f200d4117090155140c403030700d8070090b524000030107820040903807064540026001003404044001c00c01d040300c0c03c41d801d80c1d9805a182180c0f0391041c18000150021024442c13074640366100310100d40c2603184c00034055483d40c11504200c413007556041c41e601540d986c0c4c040002c0e8240114400ba00381440900303180ca00303512189580f80d1143c03951103041c00c0440d00102404030954191400d00e074010100e10080100798820b41441090210240d002c0d0042d400000b003002c104800700ca00404000d404299410111008119040c0e8515030490703100c1a40c440004402380c00f0006040390a00981c0c12001003403402c10461402d680b511314003414182080e8011002c41d03004415078031080b0105030140101403161406955218010030b0096009414070321556042c98103090803000d00c0c20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 389081276 1250 389080026 389080031
    0x703020f061f0306050718030b0612011a090408130f1d0408030c090a0f1716153009050d1d040b1f0c0209070908030301090b0105090301060303080a 65
    0x655440c45440000b002c502015819003081c02000058040e521441d03028105243c401103002c00600522000700c0c0c25071080d41c08161010501c100b42c034090442d44030000c00c540007001254005103038148100d13103080450707205200140008061000c104100c40c100111130030941c0d010f0380c0311814003881030424010502200c00c460400b028491070807401d58026900704403064156507411000c1a84ca611210b030840c1c00c28200c0070002181102c081ea170394060407e90344080410501d8038001c5181040c17050b010049070424800800940071030f020040c0c01858030340750441b0b44c3c04560304000105200b05140c4440102030b40c06030041840d0581c010a08a03228002707446401c000080b00316041603019201508020b2a80140314941c80c1950010441080107401886041d030150000b04803410000b05000c08115a0144081185000002c1991110050604102160500c2a165501c0c00140183d20314607580341c0780180e0581c010015220b40c03110003802480030a80781d140081182400741c52200d030190 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 389082526 1250 389081276 389081281
    0x1512040308010608010f1406070212010f110f0a110a0b040b0a0c0809100f060e0411090c03090a061d061f0512100203072c030c01050a05070f0503090301020703020f06 73
    0x904c04d6031018101c81c41c040c485083c031420802468a20300507540d182c1e038085020484440161505030400760100780c9100001424004605114103840103485801c82c000800c10030344000b40601000c0ea00c02a6a620784819100209240f03103140c1000743d5000381000381290108010410031100d502d2003180d4a100602c0801040801540c0015050f154150203802401001e000610325521155100000c41004507420b0384d20903c0b6001d01e0701c00d41e02a14044a401d80740c0c1d985003440c0341441d41116038440028a0f520782403545680312030200e4001800552200d800807006400007134008031400300c0000b0b85909040102045520510542c280c0228141d0500009428034100c0b0f14401d04035182d40241008110910b1444001d41c40284524280441c40052210f031000c140203903a54450f01c02c0010a002000000b0545404410144a41004030801904035016806003d4400e2030b40d200d0315580e405000d51424600310300642c0c0d645078041d80702180c28014968000f0300c4c2440426410300362981c58 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 389083776 1250 389082526 389082539
    0x307210f021e07090c03020408071a0f090a090f020d0515060f03041401020705030a03110304020105070609030c05010219091d011a19081905011503020702151204030801 74
    0x180000c000d10009a0081c161012100c64004100c85181c0500d03010ba404a586440c80003086401010829000980c0031030280404602080440701030700030581404220300001160356080d200d0740030380710582e43c008900c0701d0351a1a82c0030760f4000b600c1011700601000030042c0301d100c002e40200000031a03040c140700200c0d440c00d596800741c098035440502114a4824403107140b918990014100710369800f0f004025060a030000c1c4003074a0024402d201559490314a0500282900c00f801d440fa0740d0f07200c040041c4030060b85c00104031110103a01c55000f061000450900307039196007011001510380d5000180300c0c0c880c0a009051516207503040c1d210030740c00640365455024803600044c4030117102c0506d03400502800344c440301041c01500203680128a80202040940f2911100c001402d01082c000014031007018099060240341310704207c0100415890100102150044150201c05155000841c201551036001814501516000700310348e0b28481064001c051f02c004407815030004007000008100e0303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 389085026 1250 389083776 389083787
    0x60e04290103020c07080a030f020d0e010801060f0302070b010f0f0902040506070b2208040609061d01050c0a14070e0c0a080105150412030e01120e06040b18030721 72
    0x340d0340018108000544028010350080d072010004141c5071040100000e0461010009408a14860b07651500243c0c1c4446000e80307040c9410301c0c808103006002c0500c000c5668000d00240c116809032030a0000c44180c02401e0b8020b200d54003000e0b0401c0c0100c0d0003c1015166051244203c80f8030807034580d42d05542c9c402c0c4800301d00550084581c0290100b03d00000b180d4905c4039a500449a0802141c203c1d101752505911400b00c1c440c100c52996020a0400c4081d82005111009210703e08000b0204c06404903441c400c06800e4440c50306220000c505d200842004014244000d90302028130703c1080390050101e07a031307110184261288410f29500045080c14004c090303691100c0d10b030b202c0e50140d9007003200300f0041804411840c00468014080020b560010300f9000b54403500a40f100c0c000b01c40354900041070201a031030141003841c02e203150000800800a0060350258001185c103085132035240121044d6299501c400c0c000f032001081c0c00c420701c54095803055140118039481c201d54102c005090b01c9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 389086276 1250 389085026 389085071
    0x33030203030306130b12010b0f090903030a091b060c0501051b070f0201120c1106060a080a0602030a0902040603080c0606182a03090c0310110406050c01020c07060e04 73
    0x101504180003141140c1400703011070303604c0c6101101c081000400c203008a82001819104030a56a44a01c6c10040c1030410351021071a411065a107802285000160a9507a11015006d40009c640c2d032842c80c0c041c0300c00c4640220a0340490310560a8903607840c240240300340081601910780c0d5103000c3c003150303d10711490145017001107050365660900640e6141c10141d8205c2003402da0601c1500308000451074084d20134980301010603211900709446090390300d0300d0028000c00c1240035600101d414402e9003070004031408560351080001d80c5d40e0365582c4d4214041d15003540c1c005e40243c107080c40841000107550140010810718400c0320349603500c10701000345501d65200c51021031528000842c00501000d041d808090520a1401011809507001403807940d2040f03480c0211500507a0341d550441c0349c00c0c820042034903030207181406400580c0301b410b0088c4c49103204500500100040401c5c0c0c4040030740648000c81c9880095803a21640d92030040c210b040c2e04103180c5d11a614100e40c842c01c840c1c1005c5081d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 389087526 1250 389086276 389086279
    0x80f0c0102120c2103090f0c0306150d0b040605190501050d0602090418110102011802030606012109060c0801091a0f040612050a14030c2e330302 64
    0x307041d0800101522260788100003a2025000c1c400143d0907505610504c000603d0000c03035042c4d41c034500350038902d081200400c9040c0c50f5030030015100300e490f45c0000d01140c001020683c038119074009140024812030800400412400a40341008140401da510051140307000c99241c40c07404910400020844009028041c1e11100c0c13810141c01049107980038007071455002d000041c110031b1994000110b005014812280424400e0340141556420b02450040c2003a010103602d11604640c0043d4840c40300a108a040140410481e60800b005080385043e131481c41808110441c2d42d0f007001c001500510040780080707180c04000245510007480754400c1b40c40000c81039201e40341c030842000001141804100da205844490200312036908501400e41a849140142065152460141101811019401407a030024045800c3d09800424080e04642c0e8140040ca4542030010080540340011403031651900e01d0580200211a00301820ae84081c0d9520706d02041e410040810840d02c401d2400000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 389088776 1250 389087526 389087533
    0x101d03040911090303031503100b011e1b0f051507020604150f0606091806030209040602070302010f0903111501060207050904080d1806050c04050109140a0f06020304080f0c0102 78
    0x400410310300740e1101004a100c04007062803d082c03000024596042501e6103000d20260b40039680c03c1d454200291040302da520320050061540c81350010700300742c14a5400c05411004092002d0b4150300c00c5400e0490320809102001c00c0d40e40504045000b20a407200854061040b1103141c80b020031242507a510070960f5030300901083d501e41e41c640f11080d156620a83e0b030507440d015900d074103910600581d8007031304d0340c0c3c0e95175403071540341c40c1a0404610140c0525001783e4030704581400940c580e10101c50344983c0200b005655030b041c03440e00700d00400b8455000120300c0d19006240c001c05602000003080e0b18184021240c9038420080f0400e441701080c843e50700036a0101c0d400700a141404180c00e580715025110540c200110200b214082d1000c410094480340c1341d42c80d02008001e50b500c58a5000031501030306500700b42c103100000c0c1060081d8040c56068204501c50600c0c40d96800d103400001e843c480003a88034107a908c0324088e50360b80003805014054001c810098519543c0000c9203280f0b07060581c0103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 389090026 1250 389088776 389088779
    0x1009060b270306010612060e040f12020c04020d020909071103090f0607060c0f120e030403171e0405120a020a0302060a0507060e0a1505060915040b030609101d0304 72
    0x10300000406a08241040d1580401c01ea84a81c1d814000c0c1070081100c0d0722441403004802d407480c0b0458003142c1051501101010611000c6040b58101c1089541c0c04220220000f50014003070303140504031100d4a0344175000107092810050345401070328243d4801c0d92000000e4445d41c0d802d49581582c800348a0880c1e04c00d10400d0401e01e080f5400030840100a41a20310b41031a40c0c44032010340741c041c880980898203a040c450310540d48031000c0d16428201440070003400c5040502c1a841e8840d03480050031070040c00404c0140d448042c0111500d040b81648140c4c03174030300011401c0c000d94005100b070611440d078200c00b106901d1f2001c44d09502c09540144000d090f2030856003080b4041e040b442c1c0b01820001c0c14401400001c80f14400d50024500031401403090aa90345409110000d0703040113040014100010701c10551510034045801c01b1001006c000404800404240203000d00b00002d41d06104040a20000c2080401d00050016040c402031049a07a110007141081c01d00c0c07a00c8554583c400c200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 389091276 1250 389090026 389090047
    0x30e0405060d11040902060c250305070306020d0612052d15071707020c030601060c0b060f0f04140f0901060f12211e020d0c0f0602130e1009060b 64
    0x1404030341c40c1c030010b000082071851031b000710b4443c3e048000b002030f41e80d012807a144144000003c080340034401200707203150910b0640d521503171200c0c442d100003000c1a40126951888030f266030416009080c11400c40c00c001c0d512410456a15000c40d032000a050310b00b07407401813021740d080342e001510315083c4008200303c1c4500c09030050001d01c001c00090400420304074880c54104001d8015018030003035401131100c0309a07034080605003801a0701000c180f20001816400081e003910710316501107001c0301c2e41c800084008010607406450240308552107860b11098a640051440c00d06000e0f2600c188080c4c2d41d80c0d1420422800c84d00c40c3d0042c059003072500c0d441009103461105a0304109845a03c440b02480c100304221554025140025004200c01a00001c207652960062120130b13039440c8003c140043d08010042e2505030100000340c404050b10494501b40318041d0110b41082c03001d028001d400d95a20040c4c03030105001034607c40f488040d0500c00003080d58044c0202401c0e0b511200030145070001ca5030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 389092526 1250 389091276 389091293
    0x209100507020f0603090d140702090f0603071a120a2f0c03190219032a1b1d01060f0809100c080907052b080c0601080703030e0405060d 60
    0x2007040380d01c1076441d0084455038481502a50080a00340c005041958010002802030403542884107043e003403d00c090380150b643c000c070858010400c2000c41000d03448000c0401c0c02d001154112200e40c0280003080d50300d2040c583c000706490202c03034010400c01d80310501d09400345e480c002d03140341c522001200c0840071320070000181c5990722512004586011400c00c841070542d000320414030312058a02c102c852110b50144002e4108404e0700c2c900400e6540b681e6000f5110418010480401d071540c400344102503501c4842d070a042a40052030012501a0305034032070340903002030091091400c4084020540414119980f9058dd006a1100c1c900f0100c61442181e402d000144409018445c003d0060440040d601c28088050405e5403100c1491a1100b44e407490811141d100601030b1400769400c940010018050360b40b06644000d651104000d642028110f074011940f16011034081d480001a59500c002052000ca0780309441c0c40c007203448460108411134004840190300901c406220800149101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 389093776 1250 389092526 389092537
    0x61202060301141f05070201090e040b0f0c090406080607021204061d04061d0402120714121501080a03080c0f070201210906020309120c1009021c0303020703090902091005 75
    0x140c600c800840d0803004105181a100a08401199000606d42c0035564880c3c0362a026008015200c1403d091aa4618410040082070714042040c044003152688a000d0704868207180000e009000305a2030b00130854603114181c2d201c102500c035901c6088100c0003154152411034090381c84448124074881191100171305400461544550744a80104000e1804101d101401030504c0300b2000c40c0c07405205000c521a0f01d640c041d00300ba030000808000203c1c103621061642d49064501c400d4125200c0461882d08c0b12002070f1003074400070000080395100f000a880c062481c0a81e49034034417a110301240200c1842960b5004030203031030802000740527500604400302c1c0000144c0d68451030f8504540010304403005620116401c0d074000040c40403042081042243d01240040400e02d0040c60b100a15564928214284c4034142c85400d00c1c002e641d00c200000e43d403200c0d03000f440c80803130bc140d1a0042c020740c403a90003200400e140c41c2021070281160320a507050341201800702c4582e0307110307d0002e95860304103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 389095026 1250 389093776 389093779
    0x12060329040b01091802090a020d05090f030d021c09050d08100312080601122408120a140c01090305191823100906170705070b132406120206030114 65
    0x41c181d4245c01078503100701c2d461040740e0490006031a412141718520507a6030140c00b600c00c0b40e201c00300b80140c100f0048101c90f490b042541c40103a4030300640c00b6401c9503010000840c0950741c03400880b80c05010002c0345004045502d030740c544406030780c0c0c0c604882c140d0149000140c41c2009084064070794a000b0600c01e904a0700504244060710401c002c1c5034196584030b442c14582c402c0b5074000140307146e04022484017404c0203401400713001b65007501184c2d4901035102c00108001114159050102c4010110380d000c03024a8000d0090b49900e05003c1c01c00d620058440d04d00e04c078a514150310302031041007401c05254144d429000c0c03103441c1c42600740c9001d034080009015081c3c100035580140c3d4404e41a1034840602c0d482c0c45060500d4010301402d403d11000d4031601d04500c881c1044480c0c0e521200301d909640c1c3c840c107860b110b502c601c825a83c42006000c0020b19010081481c3c0b0714241c0c020803280700e090f00400e014440c040e21580301e100904481c4078020f40045040c801804001034503286884036840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 389096276 1250 389095026 389095061
    0x405100c050c0d1809140a1d07090b09090a0b060402030627010302090907080322080d0806030106080d1b03140301030303020705060c0f09010c0312060329040b0109 72
    0x740d103919900f00703d40c01c030820010a50f042c03043c1e00d0540c02e41c00d14100406141d00104110941e5180f00308111034001c20300c1c1c9405d540c82481002c2d0300380103034400042110320402c0f07401c07458440b40080300030b0030014002ca02c181110750008174075042c0002c3c070008140e48885401c070162034810034000070b5003000e048141d01040c210662545111070155060301c0444003403482440e54034500500c00c80e442c01402d4003055410144050000c4d03d400400c96840c94000072038140e80402c040d000c240d0540d03281d004207560740151040c8a90199000030310f2802560124000c0241503620303404160384c0d613044250280400c80100348001d80080d04088030740c8042c0281400b4140c0e44120b111540c4d6640b09820480119501040281c207100d410402d880c3e000c005c1c072100c146090701281c914080d602030421031a040182c00010882054440e030f08545c84840d110380c09000d01a180e10701001e915040c44101441413a420840c00e840c00b032014801d5001d541c012000c1c0c205a400c00b00ca0070041e20074141200840007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 389097526 1250 389096276 389096287
    0x7080d03061403030711131a191208070f060501080123011413060803030f090f150f07020705040e0a1a0403200309060a050703231c1d060103050709050405100c05 71
    0xc205014523a0328100d60840526100604810081c003500c64544102d008000e0100a02c0800d80c29040c66003c3c60300201095291a058508400e07a180382c14401040603044c5800040d1b03084054000702011a4540101241910a4204a85044401d1240a000c0d00c440381017490282407500700c1080076105400d011480d9134448642072300e5603006480c07048090041400b0802820f00c18041c1040e1010b0313a4004c0c0c21036454189204a507c1409405104103810394004994214001c1154500800d4050014032880010701c049985a0301400320640d074482c49445034000c08001902e603944075640c9501c51902100311071000e455070f90500d0002c84501d200c10008003610f652007401030011802565512070b59120300f8640108005010107508001d0312015030078070310b5840344806407101c54603500c1443d07404502c24403800000d002854a0f841c503000e01542d00780564600405c405050b640580111644036a6500d45401100c4044601a009400a000c584000034072074200352003213031443c5011814503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 389098776 1250 389097526 389097559
    0x809010c030c02040e030a08090106060c0809030c030f0c01021b060d0902030709093816020114010e100e040302030d0507030902061804061703070b040201050c07080d03061403030711 80
    0x1502c010345e240295900c003007040850241e00c4071325079901c41c42c0c040092042c0381c038246014000d000c040708018100500440d400d107254400308100000144010120b600000440d0f021503260500c0090140c0140a501c2071aa11041d0318018900500c0003e0907040c5802e0784452440020a801f820480c0d05005140000402c240180030b0380003094003070f1010901508080403488c4486d840c1c41c84001440e02901e00a0801c503404c03a0703250354054a0810307014025120104124014000301c003c03007454648060001c00c5068510750014031858001d07601c3c0d0016900c540071402ca2960449000b00107a00c02c00c030b034903014200e942215070030a015041c082414141640006c2c003940110440640510b5184400b404c10b2409004200c0203102c80c101d08030304c5000015080341c4034411004003500c0281070301c0c041021a4401c404440c0070021402c141c030340302600c9441f40f44c0c0704d80c01000c0a0000038105000820a04410005202c02c0700000f8011450080c495952015a04a1441140d07002541c240c604441c2c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 389100026 1250 389098776 389098781
    0x5150714030a09050111100b04060801020d0902040614030d030218091e010506090a0311030f0a1b0e06130b0109080f0c270105130b060d090203060a090809010c030c0204 74
    0x41040d040140d500c44a10b03180003454042d00f0341c0b00c00d04112900e21030005201005c2184030242e1300920f07011800000d9003010a028181c5540511013070340c03001908039003910856100a40d4144226001d10180780d8581c00040c9610401c2c06183d4140c011100d0310740500e009074004c00b80051429040045410500c0004481e510100d550403101642c4010303400302204014143d90240030700301c1d130203414081644003090b0100d41701c1c04020111560542184140e41c1c081041c0f1840e002c4040894610401f28600062008001c0c1c038902904407249001164070014204454440c50018180315491681e0a01d4500a020010060f60511140c0000440c035070900303100c0d1185100810004216070703410701e000e01a02030f0740e40c07540c10003400a8182140f00490a681d00c203044560803541030213070100d519552001041e0f42c0058a81c810400620010b216440c0d4001015080c001c40964405030340e0700c02030302d0075a006040c00912030001001810100d47c003c60804510038000d16081e90380c1066580846e08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 389101276 1250 389100026 389100053
    0x9060605040e240f0409020907030b09091f0f0b0a03030504140109030c06050a090902071211030306032d0a050313120507150302190809060c04030507051507 69
    0x51000075060182d000b22038a0140c0280300700c0c2095800204090101d8031101d01c0c041c0700d034816048400140308076651908010100350b0010603000031b908120802800818039082c0c1c560250b02d02e500010340c8803a02041001242c0c6d050880c9818000940d00b061000301044082e40ca0a296280c286021a40354850030802452007510781c82e554030f00344900d5824100112040d41d042003440c1074144000381c034510000b4222a81e90410320b4542c82c103881d00b981e010380581c008600c01032000c80e400e400d12000300035140180349240c5501500b0029244515141d203c201c81d100d8040d404540c040020800d4113104461400702048807404000b41c0d60304a41c2008502e50085e80d29504c04107910f90b0350340d840c41e48040100341103c44904440f1310755441c240c071420503200f469400302d12054031301c4400d802501141c039088200c9203490f908000c41d03030015005031020380d09101c043c4100c1e0000780e920085041150192904500140b142e00d2500d420400409051620111112428000b000004484081024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 389102526 1250 389101276 389101289
    0x30a03090b01140a050402030a1803030f0b04090b04020f1c03091a03060306010303111903031b050408150c0f04080d0809061e130803010b0904140717040303060906 72
    0x25000c03030035051240107004181c00c242c0407140d4858111040350ba500300391a040b0754017980d02684030782ea60102007005159008580e0119165400780404050345648000b1002c220440f082105885031030a00c0110b0703000280050000750448003043c0507191091084148490081c0103500564800b07443d103000300450b0741c04034082601c0f40e10502a01a0150900003a400c400311824258501900040d40da40b80612015050040c0c03020101a40c0b101440b04000d0081c1c40b1622042c2c244113450700800410b412940a001039501c65440d1703210505c50000ca5040300d8540008000c2031010b0030f0807440f4070102408000c440391042007000e03803401c00700c00a8001050042c1c09401950400742c0081e0a1060040c00c0340f4040d0000004c2011401017685058006c16445081c03428983e0350245060480440c40d0740a810490040700016030320110703c00600c801d11007513a041c0f2160361140c030301c0313000680c0c161011004148002d004440030f41380c3c4c044199015010740b80116540b0785e03403254071044505d5038201a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 389103776 1250 389102526 389102531
    0xc1206011101151e0506161b080619050f0603120a17090c0a060201050705040620150105210712020105070b040b160e0a06050a0504180209100206040f081b030a03 71
    0x41404400021310800500c001d66804d4500f0701c101c90404243c00d15400018910b1810f460030303562200703002c0c14140113800414212401c03400d21000c480812009910403007840740c20f003000250030a074100b4040e4011003000d001441c60102d226040901d58010340c495030100904148091084005107010078014416003025028030140d0f90184001d0b42015004032041da030401042c442040c6d800412102102c00d28940403500700c036940040c43d848055414486c44a1090f0b0040c10072981c4900c002d94101e6000301c7d03c02c0c10300c02c0809c0c03d0780282d9803200200801500001401c00043c840980048019441458003034688038041d5101c4914040c10b0754107907a40c160a40812540b42024116401c0c01c0c00181842a60801590300050448c41c080c0a040100940812003c405900510654010b851200b2950441700c0100c21070f2002500701d03e1205201d00e1124014426480c000314000b4022500046280039400d210b480d0303494990300502e0a0300c44400c01151400d002c1d1000d0016004829066401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 389105026 1250 389103776 389103809
    0x11030d0902031504080304170c0d02010507091203020615010905060706090204061d0a0f0b04020a021b01050406020709020703020a0b19050105060301061209060b04230c120601110115 80
    0x10705140100380e0403070f076001c88000340512000c01c00000550740c0c0664803c030324519604031b0364000541c5000382050fa140901c141c4040710240742d01034100b14810f0300c0641e503161655554140b1281000c00034080900940c01c130901050811102c2c0006800d4242c06040c8190041e586074041601c552050600b5141996111000011441c0900075000200743d520b142235040080c15003185481d100252541c0e400654403442954480303895080270080e000300500c21034460805c490081e40f90100c40021700ea91700d040130341102c1d1540c0075400fa503096034065401004598107010301d00c4007c3d80080020b40c01c0d071084900380c2000603006484544207043d00704205503a40001603a120950b201a04800c1c8074400900042c48015807003100650069046003012602d8203a904101e00200180c0510310b4009041c2641c2ea441843d01c6004004050382d00701c0c90030490350b00d0001040b0320b4050f001030f0014042a00012410a42c40b810f400c264001c1c1180000a00003002881044035480c198446805c0e841d50300780 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 389106276 1250 389105026 389105029
    0x70605040e0610170a150f06090815010302090c071704050405070c050c010e010507020a0603020918060f0108092a010f1403010515040f1d011205070e0711030d0902 72
    0x1d41d6004802030390381c0f0f9458014007602806401e02c080041900c1315400b40091501c8400d40c1140d11070403103158050420585601e8003c1da081da2500520001c505e03a05c40009152800248103008c4100311142d1700000d90071503080010100014000c0c83d60b0500a12161001c10400024003d41c0d01042208641d50340c5401d0030706c01503407001840700302030220341078942022840224003808020401d00c2d019243d400c4020050b0359501070058040d400112610f00810481c1d0140c0c000e00700c803181280c3c1c401c2d502d07211411421100c1021544250415550900141294021043c00c2d03000341c002c1c419102265410104040d84070000200b40d48003404103000c0e0505541c110310003054590b640d2421198141443c01413441c2da11041c400e0707034041c1010100c020007446000c816500980b664040201d04103079140000c0c0ea000c90380600300003424100d5000003a464684030b10800010b07502401400341e6503c4c042d100307000048001c0c081b20038030580081e80346581005000800e014030f607098000a1040b650700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 389107526 1250 389106276 389106299
    0xf06010305060f0d12022b0206220204200d0606090b130b07051f090c09060602060a0c050412030c0510051003061505040216170a120207060e07060504 66
    0x709403d0281011010315952501e5041a40d8129a0070044410b411085400c01b01d2500d0179800d02c091000c01d039002090204010035400008182143e0b00f100c0c003949621100d40d0549400d040c0107100c4240da5944d0000604142d00b26001c0840304203010000c002982c1d07242c6040da4010801680e80035602c000512803160403404420203020b190b1802400d00d00540c141d951055860b0040c1d464038040440e00310700300441046a071b1350010110315031131030420495008502502010004840c00c03070194801144144107480303014112040303035004002d0398542420802c000c0c00c03000c0e85141044003c02012400403064040045042d21079540c3e10013140d214100a0304181c0145810b401e0142443e0a0103c206413066100307007541e07003200d000101840511b504c54007004990f80820340040c00170032a45010303025054240480d5024401d0011044e1801c21408441c1c0b103081c9a1001003a01c05218030000c8003160b02601059128580c001220000440b81034540030095001800050000a0a0059241a8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 389108776 1250 389107526 389107531
    0xc0c0607020c03100513050312090d031a100c05030309152d0901151412070302030322050d060b030d0f0909020307170705180109180c020f01050f06010305 68
    0x1840503100d001000300000340c540132160803488a0300d0b203403804035002822644c90034141c0b0358070804981d03590b80b15078499003844c40222881416070182c1c13483d101c416406030081622102c5d4803a0038040b490101c904002d9201d2450707049204101c030b50800b102c0052002c00043d4043d01c100710007410804140012903599010040c0f0220804e110140007880c2050110717065921149001c500307943c0c555544200754014882081c40e002000c1e004540000c140074500403003140004140e5400361220148210542d4881d02c0707210083d01503000b041000c00c401d101c00a501100c10f504e4103110000740d511000101043c128a00035600b01d6510030122806140800625045904500300050101889200079004403100e00c00d40000ca90004000351200f481030310701d2104800b240c7c01c490701509000500130995040307001103100d411014407901c105580519060300490310307148002804c200d5a01e9200c40034040301240ca07002d40c800d0a5465072941c00078010b462041580e13114580c00391400000041c2503e001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 389110026 1250 389108776 389108791
    0x30e040c030207110108091513020108061e040b042a0314070c080702010915090806010b0c071401020a0f0305190507050a0308101502100b1c141002030c0c06 69
    0x420400000510285118803280713401d080c01c02c00744c1d550403885400c144030200b0644024600b03000f0040d03941294192220180d0017a41e0b1500696900802d001200060601c5820306080c0c11200d80c3d1035151582245480240240000c1590b0b40f54442050503004d503011500d03e81d00d0f80c400c00b40401d0340e051094100c103d002c0038401d500d500f04540040e04903910328001800c11b0394001000801d40e402034064a00502654407003500f00b2a10980c020159241d9002e10083c0e070080c20000204214000143c0e031020300c042d00034120319403030f28055038803400300207500318158004d95401d40c0c080b90700384445a115601070344602e603a803400350f1100f50000c00d1000003101401004d110384030103d03030f0024003040d0040d450305020011380c8402520201a0480b640543c0e00c1c41c0f4000c0c55100b10301c0e408140034004002c941400e1044440500400025803c44810b07446101c00a851010100e5421000e40240b2643d20b001d48860b21b014031a0740c016a07000310380345001801c2c0000c1d10103644030100403580d48180c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 389111276 1250 389110026 389110031
    0x23a03140a0c03060e0c0702041a030c060d09050106081c020706050306010c0507082d060606070206030a0605090403030207120801060503010b0c0f030a090302031504020a06120e0109030e040c03 85
    0x1480c40c440c20884000303426458200da650803030400c0c0380c0c041d6100c0b00c05000d5110407800c0d00d00c0c18045100550f40010002c80c052414800c0340ea00148208180b090030080c0100940311021500301031110541040380b01100003a2580080d1001c500d0a11804002c1d0030b10b8005450746881a150f100d0f040340072442c500c0115402858200700b490791100549420400911704202c14141c10b040062500100d40c120000305e0183c01c1020802a0b4016040080d26120180c2e458903c1080022283c440a048548940102082183c400140340c580001c517800502c0740790020b861501e0708041841076008440c22000b00e039000840000b84000300301c0105410800d403a00e084950704024004007070703003c18800d81840101c01310b104042264140134040030400320004580e00c54400c000c0013061408644010f9000c0d0080181c50a03d42e074034102940c2c402c54003d04406222441d0080846070075050310300c0700c91919501c071034280398054280952421240030765601c04416000c4010401180c4000d01d02400723151 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 389112526 1250 389111276 389111291
    0x106020f2d100c081e0c0a03050c25061109030a060b0d021806040606050415080a0e15040309080115030f020a0e0a0c0e040b0916023a03 60
    0x188150900a00c2080201c1503160408040c200280340c40c02510b4092a190f0400f14400020381d07100c944030303120340300c2c080c080e00e00316200c6141d41450325000d40d41c42c45a00c10030040890102d00035000ba80d00401180304032032602d40e00d007240000c45440703119110740b0408690155414418580202e001d195820511f413403600310000002030b40c0fa24591001080d5644030b0b50b4858456480c1c00d03116410a4003d0091040700d6041040c0310f040135001c0300c43c14403a61605002080d9903200d001541e00395408001c101401505400d01a2907110008281a40481d110005800110302c01d1103941c40581030b0106061245c10309180180c0b5120741c80c1c202008982c90000f20580005501003441d0407690890358441c0340c0701684c00490125010398000301d80801410007800039125081d07001e6280138610b0f5442c01d40d44184513007000203072030214200b0b81d0b000086801064601000c0070301c0b1205080c4500440305410140300321500d004490307110421300803190808850300800219010749000e56149010031042 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 389113776 1250 389112526 389112553
    0x25120506040b06012a0516090e210a050304060b0406090c0e10020d110114040c03060b0406050d02061c1a010206090f061b04030f06020406030b0111030a21020301030b0106020f 77
    0x2484584414410300c918109600c01b40981480000d0200f0340b111200c02113181c4501010020b401d6a074000c554510400203900d201d603010f54020041124000e0308903140140704881100c4540002c1c10070341e14543c0d2825000340335591845080000d2180900200e41c0203802103014022414102c8030501030781c1c90340941c200c41276003c1141c0404000307505000012004405105006014501113100119013100a00089c0b0800749009000c032440782c80f0901c003102030481480f00350752540c840d498100c010310b28460010700d0071601900d19000440010b8413407500414103a004e49030724604008032000507c5c2076440c00d503414028141c1c0250190014000903510100d029640c0304000c3c0319004000d40d00000410b8500200115801960001a149611812400c4c100029030107445220042854840c0d2001c0d25401100001030035801c8202640c10820b00d650241c80105412960b0f00382055004404a400e03585c070301c0518007860081901c88000e6040c080c0291400e4260314481620794449417400965 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 389115026 1250 389113776 389113817
    0x30309051e0105091c0204060e0f07020c1003020a0302070203060f060f0301181101170a1d0c0109180b1903260412080904021909050f0325120506040b0601 68
    0xf0308180c4407078060070405d03e1040e80912a4810080d0f116041107000280c00110520f4980100ba94221402c51612004810f076510400c540341c2d180c00c09a5003021054540c0203038050013108001e0f040141c03400c01d582d4000f03800c01a0440d5070b81e41c403081c1784040c440d160034045507190172020194000c101d00c400710b80740001c1c1400681c2e001098010504c0f03228203541d200340414800c541424a08440e242080e0380044060144a0030449810040c1c040507200f010000884a0702c03100c068441da1030150070410388000321461440241152919460132021075224401d5a802d800e00042a01b81194214a444402a03c0f480042c0c01c2803229002c205103d00088070031102114010700c0c400010700c03254034000c4403a001d00d2008941c0030344082201043d2015080d5800403000241e52290009a1140204002c00790710b1400b1680641c00180c0042803546102d101100341904250001c01c1680c0e0380110400010701440211a603401000c203000400100c0840203802402c01d00f007121031074156030141280c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 389116276 1250 389115026 389115037
    0x11a0604030503040b0f0739030b0f10080708070e01050102010603031403060d02092a0a090905060f03030c030409060f053f010b1f1b110a030309051e0105 68
    0xd600344c0004075140380d0352a0b2401c0f202d0a9912034800c108d03003a1003152800d9a14a2041520b0b1801d002c18001c0d000d203038200d4454010b45c3e60111800c005500c49818000701e01d140100384180b40c410600021a5022040040d82c0c001d0041ca0001c0410600385031851211070740690040c2d056a041c400e05000003604001c041101d100503a261030b031203030303205000140244100e20000c0d400209842c117001440081099610001a20120443d518a00ca86c01c800840c4201c09102001030f14080c403e0125884035013000d40c02940c0100103c00205018000900b141d000d2804441c00d07a00000342008900c2c0c650140c0d0000341034a21725074075264074103000b103640030f0f010101400d104500800200c550302c0d98070100801007000c0004508040500f84e0f400d500030300d0040c42080c810358074141c82007100480c020500c0d80c0c00403207039118140381007494105070b90418050401c0350f01c054170090480301034807011100c42c000c41c040ea580d00d110700d2500041c001d402d90303c0740b4440e0800c3c08483c0805001d9811000301e90 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 389117526 1250 389116276 389116289
    0x90f0b070f050102040509040b09011b1b0311120c0709090305040501210f05092b0e1201020c0d03110702010c080d020d020d050414071d100e0702011a060403050304 72
    0x180c202680c0c42c14500a100e243c10459120440b0300a1105015480910380c4c481c0e521b180080064040b041e042c0007031004032809100000354072a0000c2004201c2c60800034a4034824104401420150b02e030b15820961407180e140c07410b10020a4003a0700b203100308480c100030000b06a003003003a10110348004081e03101d14054207061002c12000a00c060b07141919090303814803a44400c00040e42c0001022020f05011780e91156184200f110941d403130003d004586030070318524061103259031120503040e80c0c4d40c2c0344d40c00030582c8010030301c03500c00c0441e100f0300041c00180c020310080c013868004110003408903007841c00b102c1c1584000b480b04000603600000d4040d540790304502025100c81401c0704500c017030311038207003900341c1c10f0b001184607107046025400282c080c51040503c0040301562a050391b80d605480d200d0310801c000c414a03a600c11224282c1e1450700300040003450340c03120352515010101e04109640e6040182c2d5112000200170322414540b0b000040e084504500d000c0c13030758a0b1140c0d01c0c0907500944 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 389118776 1250 389117526 389117543
    0x2010915140a12090f060b0613050405040305070f050307030212160b060f0a0b1305090402130f0902060412120504061205090708060c0d0b04090222060306150303090f0b07 75
    0x1d80c42a002c0c0400d4903004803801c0d4140540d04d010700d081440c03500c1507a021141c180c1040c8280449140c4801a00c5c0200f0001c6a00c1c41200d14000c1040050030703001d803040c0c00b0300c002040401c022400304450714002ca03004400842d551003c0f40f078020701d480c042481e00004c05030140891490102c00c285911903281e000481011151160341c0000e054088000c03030940c0c0300049400014003008060042c0c00c040107084480c80c1000e5450043c09088101100c0017540100002450500060346900680d2011850000025040d0f001c4c0d02040c0560721940140c1044941c0c4504181049580403150f200a940761800a051501e004800307041802c01d5010400c406031030b0000500441c4081050800810320401114554200070b480300005c0c0d80940c5003100b9040c20118424154149402880c0c644d550142231066581103071015030f249281d036503228060003503e500c00000440c40d5405000851140f035000d80302d40310702d5850040c203c0001944140511404000c040042e806550107a400c4940c001c000e2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 389120026 1250 389118776 389118787
    0x804060203041b0f091a010207050d0525080c0d0201020d140d060e0f011a03040f060e12030a0b01080603061317030c03010906060c052503020402070803040201091514 73
    0xc0707207210036210b403900043c10701800014030a034080151800315110f5103002c0141c80b18408a00d0043d030a29510360f40944e00140c0104402d0030820800e080c0513014900b5a101c07007070002c1031815a10784200403030003409258003082c44610702c140301801c01000c08130385240c0c055045034000303500c400012a968042c042905904000420040211060b8002d80642005440d4480035141000c2e0b20035204030101c4022480081003090144ca20440b00458203281c1074159607941c3d0392020b07034007000e81d07044982584800c61603c9941c4200900c0c0c2c0704995180324542c503458810600001c40d060348c6051030400181c0c1051168503200800d4241d0050030070030103140324880e103051405058030800c0c0611a0740380300000300086030002201440c140c41c606001070042c0340d6525400c9409d9541c010018009402042d103c91260800c0c000d4090032840403107201c06000d03502d13000101281c00002c400c6d074515100008100c210344e0320100c01000341069003c1c031491a40c1b07425004010503000f0511030610800000c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 389121276 1250 389120026 389120033
    0xe0a020c0303190b0109060203120705190804060c0c0206120c070803100f0608010b270d050109060e070f03061e0c0c170421020a0b0f0c071203080406020304 69
    0x4031800320300e500c41125681d0410210196803000d51042c1c148186180614041040d881000500c04541c500d80c0114248880c190b4400b10900d405003c1c40c0a01030200105034100300c1003070180100b5503454460140030300d0103041410654414035840b40411862445c104016520700c03058445000b541d1030f16191035621f401940d10144101d81010388055404020008001894617014050300d4507410704820385030380c41034266002c0c1030030300448103441010310240b081c9407010346240e2500317481280108010928907020402d60541900c0036110399464142000c00c0c411180600b030309065000000701621894642074803401c85441c0801003007107484496000c020752034034038607107005421242d0030850242c548801400400c000f0f64101c0f40c1c3e0900d84804d50010100606a0742200c20a01441c0d00007034620000004803810840104d0340a05803610104101c0140700140034141075102d030b8903583da44d242c41c415140039043d500000113400d2301346524000980c40080103801950001d0050703100d0700d9600d07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 389122526 1250 389121276 389121281
    0x60e060c160f11120604030f0203070c21080c0c040e0c030607140d06140f0405250504031a010302150403050d0e0d060e06190605030303070f050f030c0405040c0305100e0a 75
    0x10569944040d1804009801c2034000c142c40e8006c03407103920b5650010181c20b400fa43c0300d0041010280102184003002c024083d043c19413981c1d1442c0302601070104506564900f41b042e0050300ba518150fa0021006c40a11b05041c490042c525102200620a55281c180083c2d52144010111800c100040300000b5060f0b8441090301e40e0540f500c2018090301d030300c0d0225458214110518184a00000b508281141c10584200d9010b054010040040017800040055011444092000402004010000c00701b01e9213041e13603407a03401c43c0340944000c7d455801000344078400300e0100052040c1c20042080001c000141ca07200030700080c10203906025030040000d0155608000c003a021500f0107448902c440c0003c588207101d089403007000c4003804803210035141100c1d40350058941680c01040824480b070b0003000c5e842140252846c069140c04500084e080d40f1750401d6075011058000440c040c413091401d800f80951005140c50100000c0c17800c004a0002450ba501c500765a60200d080402ca1404464 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 389123776 1250 389122526 389122553
    0x70b03100915080102162a09050903071509141203070e150a08220f063b100b030309040903090504060308071704061709010612060e060c160f 62
    0x140000c54550425000215018008140031180411044041290501e5800d091a407487c5003169514130715041040c1c0078000c2501a11000d007610040c0000c1000401c0d2035850a1004040d400104925072a440d0950991481c10710541c1281c00400c26401c082001000352a0300251528054019041042c0425541e00400c0d00051040000146644005401440090140c0d0088041d549901600351102c100b462820304010300202c01d04501e4000300304980c01c0400c109203c60794209541140303c504d0550072000301140a00e00c00190346c02882c1710010300c02d8103c510707500b01091080e0440e43e00004c4d221301c21191300d980714a5480c0c09078000e15115a01c00e40150501510410880e51603040600403504862800c0742d1020341c4400306c01140100c03105403000c603030300c1c0d407035051810040451850f560440242041030540d40e50000103103a11030032884015150188000050303405c40c8a54144c10100c0c014403100745000c1c104800c902f15560080c00b601200d40100f130b00d11340241070340340010440140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 389125026 1250 389123776 389123789
    0x20a03050a0320030405060613020c07180605030f0703050d0206010609030b13050304080c1e010e0108041412030411040e03040501180906030302070f12150209130e030903070b03100915 81
    0x4800c1008011b000100c0c28056002290031107a503140c50030051041e4440c030035100e061900036a608101408001c0ca02c000d1401c241d4030b020801d26154404207240c00071024942078154007083e410020f0080c01c1c8071919030341100c0c1c406807185604220000d00045120700c402051b07511074000013400c6138810801285000d500000342c0359115031b14039440d035407050100422807048104c00740703000d4001040d484140f141c000c1a1120001120a0401528035100c014030503100181031000d00e1040c0c00d420701107605a2a4200040c90b120308060500a440e00060b2030300c0303401240b9210540134006070010544045401c03d10741582071700c3c1c1214102d14440d0107a8010190b1a04002c000310030503402041d400259403100c0742d54401c50395144000100d0b410b42c0a0003030140c4000312a9090440303581d170010800e080001d040a41a003215074041002c494058803050b041d50004a154949440c060010300014000705154a045082c5004007410303e070041d01c00e001c4010b03034803040000c4071b8050000c960001d144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 389126276 1250 389125026 389125091
    0x3030a050c160f08070b07210c060c0819020913051819020102010c090b0405010516330e0309060a0207050a15030c08011428090204030506010501020a03050a03 70
    0x5a076543c100400030740b0302911400d806030389400700300b0301040c400703841000350826000e02e04904411542c0592020000d285d9040080300c01c20140440c90f21f02954142e0b9000e0b640d02c000c14500325a51105111003000180403031401081002205d582c0d2450031002002d04200015054640e40f04a040301c0d921400301c50180e003c0c00a5815508295031075907100706000780c0090010f0b00e8440070842d04160b460260084031101404107000700c3d4420400340c112140c0c00400500d0103096510354422245e00002c01c80c1c448014002e0548400001030301d4200c40c012481010b21180d0500d0134180d4503401003282050043c1008100000380078400c00c00c0400601000d03001204040c3c8482c07400941c15151036160700481d040003688000544104400c1c0c0c100e075030030740140398200791541c20018002003807140d6009164041d84452000d203107a0805000402d00044010303950780c07440c90500c0c24118141d01442c19500903141250129030003404807008c41c1c2c558030300041c4100e07802c1140d0300e2940700310001010303403c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 389127526 1250 389126276 389126279
    0x1101112d0607080103170d061203120c052203060509060403031a0901060809010605060f0418020901210e01050a05070e0a05010f0f09170102042303030a050c16 70
    0xd20441900850015864603588050891a40d85030344440580c0c00c04002031103d001000481e4991540901540e00c01c034456103410140c481940a40d41c10f03400905401c4007500b1644205500a08001180c0396050000d00064003400d42c041e207680209440544041c1e40c980c1203960b0024010004005035522940411850a010b941650b944c0001c40b011004a8a0200710311071100300000712080e801e030020803031402c583c2010300441d200000900b1903c550b41d02e416001c511551040301070266040c84e086c5482c0c0702c51401240c2c0070704090b9100c82049161042000c80745590b4410010700e66044400961420130f85000110002060001c002d4200b552a02c41030260091b4980c0142d405000649e0b41c02060000060420803000500c1c4a1640072500000303a01c0030240c01103404401c5400d0301c3c2400300340c0320b0352102d0114411816684000f8240d5001809011084080240180801155060656100071031000c2562849404607802c24003201080e00346c4040710800003900100c80c0403082c2281355 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 389128776 1250 389127526 389127553
    0x40615022413020d050307020301050906071205060f060a0c050a030905040506040c02060a05060d0507030b011d04050c04150504140f0603030a0912050f060408030a0510060c110111 79
    0x6250318144000184040380c01c00c484180307603181030307400348a594600c1c07041c035402030b400c110211101c0142140c40380000d101d01d6001d42c1d0203104d51441020081c0241000c2c0c036108200402030301a032681242914502000c0c4620342e210b215408005850075500155128010b05050722806000080105144220848001019406044501203c0080c0c0b000d000b1510b07444100030598506240020051348160f001880d010b2090b00401d81001000e480441d903a01151106414458550403d8505960003c0108004c6140d04083c407121000c0110206042c01d190ba01c841c0c0b01c0306010f0001c0d100360341f0b40021f4561662603502d0b000050030024402c01c58410100e0103c4400032048421490101105000030054240442141c8101c2c00070340e10031850720b00f0040d01c410103400144040c0c40c0c512030b4038400340b00c1141c02c010003401a802140303000c0d10b9142070390201050f0790b0020002c00c000c01602d2020031800303401039112241903074094500c1c00c4000c0113400480d048840001581c400380f02e101c0900050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 389130026 1250 389128776 389128783
    0x121806020703110405010509040204051b04030b221707050c0909010b0a080714130f090312060501230c010902100e130605030319030b060301030b07080609040503090f04061502 77
    0x1c40c3d00c18040c00300800d2840d010041102c00910a46810040010000b0300501c0c113648290b50007100406942000f1046540c00a200c1d00560030444212840c0300c00d0007426580b00300111b09041d0001d0100b807540807650303281d4400800507904054050f5010480404010007171040300010360025051000d10302d403200525010b480c515484038054a6030b0b0b480887d010b880030801a041d10741d4143c680e6050b210640c280102203645080024055640381205a010440f50046400c49070083da80c10720b46407841c4541c0021200b8a600c45410701c01c0030801186454941c8044d054001c488030b1140c0e07103511100c80f0180c050280644004d51040300d0140c0042c020f500001010b071900c1094400c890703611614007115041b100315019207a4194014820071003000c0c213007048150000b01a19010601ca440d22001c100030740c00a03042250308043c0a02005102e551182c03506901c00750458002c040742c1000d44900741c50f0303c1346241040c00b03026283ca03c072203e61203d41011000741401100d800320603c401500944 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 389131276 1250 389130026 389130029
    0x90c270f0105012d0f0309020405070801180c0f0e010e0d05100b041e091505010305100c0c02010c021903230f0f1b0a08010c030603030e0d0b041218060207 68
    0x80b44ca0803031229001c505034500d104a0803d2a4140c032000f00e0f8403c400d0f120040142c54100405858101c50f0300180c41d40e010b200e005e400a5144c42510b541001100020312640a1a045e00a4035040e848400503a2110292912095a0607c1401580c036000121a41c4900d90304c510f4016101e2034045042060001e411b45106015040410101c4854000c100650381000c1000602c3c0386030100701c5082441c243d00c40c3c0708442c81001341c03004101e0b4003a0b410098803001d0b07000381c0703041d04100c60703e40a0004501500b80e00c0d407500e142a10780440d003540040c1502910180c041c0c040c0b50102440b0321060400803860b4091a000020031854580c4400d841d8581d90102000715114011141d01000300c040000c0d0a10710030b0703200300183c501002c030710303002004048040d06004d0703101204050000b4000c0083c0b00f82240142542d90104840c2e0031401c001c1c0070808031004c42c5000701c0c8000c1d850000300701d9030f0803e1074100d03500000410308408041c0b001c41e041c07040003900310b403400d0f54070800140298000946d80c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 389132526 1250 389131276 389131279
    0x6040b0a0b0406060503012303060a020408010506040902061206010210021b0f15011e030204020f09150c0d0c0204240f09050f0a0c02070e07180e090c270f0105 70
    0x9065407002e1205a4000b4410031001c6241440140800110804a4031540d40e450500710850401400064940703d0140c80200c80150700190501800100f800b401e60711030700c160307801d01060b40c442c0e0120303005225035a081426403601300c0114105030301c00e10200164045800e01075403900942c804022054081440507445441020b02c0380c81d070b0030404203807159681c500c1922084103a02e40002d0407152150300403c8a00708000410120041e65244050419180c0b40071403181c90716204420300c020501e80014400e5a54000d01492501000003e0300c405c0703000c01440c110070742030258808071300509800b004c0102010380701600100d0005a0080718002c541c00e01018000042e540d4007004100c8a040e9480614801c0c20400160300c0c00c0d103070700000c0d070a11a92040b1207803d50340d01c440c200030403019150800086e01302d181d0403807000303030030328030900038102d09044408541800240f441d80c88441703080182c056030485103001d00282440881040104106004000c180f8241c2e842c0111800240600c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 389133776 1250 389132526 389132531
    0xd090f0509012709081216110c040209220507080a050903121509070e0a0603020f070204150e09010903030e010b03120c120c0607020c03280c0806040b0a 67
    0x254030700e0680c000078100c03030b502603140044920003c540a280c10900d031100d03070b1143d269190b034000600311000401881841601410380c1d82400c25071410800031060501003080003903251b1001000d40415400440c401c11180141e4a81001e40400c6880c0c40c10b07801d07801800d00c9207000003000340e60307500314920949071903907150500da8801c210fa4040301c0c5c05440412103a801440074500800031075205980041c03c0c428031a020100b9500040c1c2c000e50125403440000302160002d040790b04001c043c00300540b1141c01e040d800d0020080c800700e204d01031100007a11454903540484520880010014003a008018442c0b506251158449028222034075003200000e00c0d1600c46109404103104000010305c00a02800302182034640300b80b00c6421505801100d80202d9030804076030301410300102900a0040082e00c140d140480020381421602c1c0c0c001d901075001007528120b41d2a007410001c0001202040701048200942007001c8184d0301c6402800483c8035079002d1105100460012911071980c5010a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 389135026 1250 389133776 389133779
    0x2705010b0d141e040c09020c070503010606171b07020a1706010906180b060c010f140106020307030f05071109010603140a0608100519051905010911040b0a0207080d090f 74
    0x2c2026032400302e50010040641c080702d052100ba01c6030005800c640181e00070407415842c1d848103c1264408005403070903502c4213808004c4d0b41003c0c0241001481d860920940d0041752800c0b6050b446001840c00c0e0903200310a40d400c040d11039050036101115001750412441a88501260180031041c124203000b0b4481d007400020155014010304007515640e00c103103e0407901040d150400b40000c00c8e10607078071030740621428201c90001d128800c0d1840e54906d002c1101e80c120320002d445034106030031041c1150400c03c80400482d410000d0091240d10070f00d8580e9842c1a03070b04103400020300829809a1002810000181050f4560052210310601007689101902c500700414201d400c40d02c02c1078a143c101820810102215a0010350b0289401c1c42010000e03040c50300a0040301e1049039a48a010320051450324a003511348a01805050b0081b000c203c601d401c603000e2f800c035000e075208208c0d440344002a8005001e10a01c5203100802490b011a82007004a0602078400c0f040c81c0910295005c48800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 389136276 1250 389135026 389135051
    0x40302070b031315090b0c0403020103060905040209041205191e03060608060d11040504210305060904080304050f0d09061103040f03080f160302100e06060102072705010b0d 76
    0x3101c1c014524098880300da60491303a100003a8482203003840710040c0d603500c40c0001107409452000d118049000c0c0c03c0341d84504500c009021240c554011440d020301c2e04040000580b2249866900030350450301800c60300158980c11905445008050400450f00c6110700c0043c0d074111101d2a20306010040080e294049042d0490032103446119007000904c001010071180d0402e5080070040900964503400c1c070b121f03804040b03400d071601914201d602080345c1d0400c0741c40c0e0503a0620f070410b0700344524092080782400c400090348803101410150500b07100002180c10454104000e124854401e000d0350840e0b8080040540241c04520603038000c20072400c41082190300220465095440d6495056812400d6485044603600600101603441c042007000101043c0304952900388240301e40c0c0201003140400010100751014a41600e945030b008206000e001d81e004070308682503030b050a000d50280d403d4007007100c01310392100c60981d040c00d00d8040085488904400100f490403c1c10009000d02e184518 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 389137526 1250 389136276 389136299
    0x307140a060b10141c1b020c180c0d020702030d0e13110d15050303030412120509150702011803050d1506211103131101020601060509060318030309030304030207 71
    0x6411002450032480f404007180010f001c0d000303460803407180c40591042171500e08125107000401d146881c0401d0141380286074100b01c000030050b015a5030040c8456007084000349214040c00d002001d00000c40d05501c000e07101c0d415507110b26001004c9491040f8100c00151510343d40f40d0f19540518009241140c0d1105c2d103006a41b411a03009001c0c071702e00002441094014002c1103662820701106400009407030364100099805139000d1000300f0a500c01c1c40304041d0088109110080d101400c000130000c0710000450603540891240260229035a01d1681c102c0c0103149074aa1541410311891205080c150f006010304440d01c1c1109040040060003040f58900d80440d10900000624010b00038058145e200070b2003104d400703000c0d0007041d00e0350340003424803080c0c00440d215000700d5a4000b140050040424180c0d905001c00e0010b0045941040401412440b4075204580104000400f00b1400c581410514020507111020b0700c1d02c4e404c10743c0c401e81c3c480d071060b9004d50042c4039124012544c60340c2003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 389138776 1250 389137526 389137549
    0x50c0f061b03070c0e09010b030a020a03030f12020316020c06030103111c230c100921020a06030b24120403180f0510080609040f050307140a060b 64
    0x2801a41405001020071001e89415641d00d10309010a000c14400112070711011006007000e000403801030300d0455951070868100070003541c825485800d60380050703122881d691065940520340b59041c0100b030001603d000e0250654580e40500c00020805407070045141c41002207c10340c2501e00b900602410400e00c1d010a00010f401c05844442c440401d2805d28666081c002040b100c1384026800c6445000d41c07124400c00d846409400f0406038500d484060001d68240e05c000c844030440500d0030b00e402813682031140100200494680c50481101e40c000d40c100e80c80b20341c002c0a00c0402511000e0017409030401d0540c2d18019941d6005090780c0200441c001c207882001d086229049c1080d442c4000d01d03000b0003030300c281c040c0640c01d60752403105001c9650311703005080d4049802031420b250000b84580010b4025955040019a10500c000e0ba640c2070312884d006600440d0068648000d03041c49411403203901c0d401055070500103040300103543c01090f001541d901841080024002200a00001e85000f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 389140026 1250 389138776 389138779
    0x4090c03031d0910090c1115160f210209042c060f0c13050301050f0405060a180f02040615030603060f0203060306060907030e030408030415030b01050d051302130504050c0f 76
    0xb211091265108580c1b0181c440d600c0e614104000011300300319141062803a00600c90003c102e0750801403c0030b90443c0e40c0444403040d03d082040c00c0540b03040145081803461090718003065440c00c488400242d178064480c2003500074010800713103000d403441150b81d1400900302d40c910802c102c102c548202e00402d18a200389103003100c0c0307240ca0b0f8422200032150f60000c4c902c20350201d1030318404a8161400d209052003502e007030314040c0709410300742402c51038071f50001d10015885040c034070f00c416140d01117070f0240344440c1e0050b44011095110304c0054003034402500007203020000340d194003a0320f41d41600001c0440c0e0040c0d40400021a42111340f10070391104a81890301944090003080460030020707044d81d488021454000b600050200405003164819401406640d002003010700403400c000300c440c0b20585450504101141c40040060028040c81041101039591107001440100600c0c200c401d0b601c4c1d0080800c1b100d055a030000000500081c4d80c1640e003031140d195050b0a0b42421101401d21030030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 389141276 1250 389140026 389140051
    0x80f070f0b030a06150815100c0b0c07120c111504030b0402040902090a02070b130b0403051e0d020415020d200a06050c120c03010509010e0604090c03031d09 69
    0x30401031000703990025003004205540d0b040b000800c4030142542c0d00d00381d807882c3c0d5568280e01b0861480401e81e02000661880360f4100c103141c412145e00f0105401e0709580c8040d1081c560340d100704039503015004103038024100e44828184600803d03031010705a5050f0327124143c4503801c1c2c41d020b800d00030b00400641044a9149040106001003515080c0341540030344024004140000c45501240150b0b10544c0e1348140742d500030980d41d042007c3e014550307a00c03484041e0382807070080c2940c403500d0900e48068000781c103001000510180e40a2890ba2013007880010401007561106015441002540a8890641040d5500d140100383d5031012a10344468031060f61004001030b840f070184152009450521440ca21466450710001100c41c09510300c04c40311454003544410314800b00082050006100050035074041005000395528501c503241514404140050700d5a6183c0106006194a0ba005440100c03030f80400001c2541c001c14500800000c071496858281909052052024042c0c0d01c8149050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 389142526 1250 389141276 389141279
    0x7030b1c0f050f150a0c09171c08070e030303040812040804270c030203160f020f0a061410030b0a020a030e101d120702280909020108061002030d2c07080f070f 70
    0x455108c81c1c0711504a003020b4035410a888299020071159102c164004190b1040030486103a800640009401209130051843c41c541942c50310054811554002d13656084000400c040c09410015240a81a01700c00351000c0201103a0150008800c0310307298002a08000018070031a02ca0300036079010300c103084004010348050740000c0d0f880b140d80b104154214072030101e0705440603404108100005d4061140001c080280d80418080d090005000c0301c805584840104000380c40c12010301e070310030001d64005848124081c4218060300e9044034150306071044825103041a50140e001900708000360410b090f90108400314035481e01c0c00c0b5064219695402e01a00c000b600381183d403c8640310804014000c1113080d141d209010000680100355020f5a4002510447d6000384120303404c604111a42500c0e8000b21200039a68801c2000341e5001c2038072900d814169a4008800700031110450390140d140c4c040545000e0786d110250320a00c400c52040c02107808103140d011a1030400d446080d29101d103140d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 389143776 1250 389142526 389142539
    0xa050315040b010c02091b04181104051c0804050901060f1e14071104020705030a030506030a17070c05040203090120040302100f0c020d0b010e07030b1c0f050f150a0c09 74
    0x1c50300030007408403542c03101e80c1a203131065610004d00203071105c0743c0350f204000d00911b80003003254004034034040c2c0b0780d4007004248000d5480c55012403100c80c040000003149040740c3b5204c1c000c3d00a035408560085241000411724982080603540001c5141e03071200b4140120030101510100106c0d80800410f2108009014031585c4100500c10356010301455171001c4a400040b40c2242d1140714181c1d0340780c10106162040a038540522a00701c42c0481c000c100302c0c025902c6074010440783c00e416a40d07100700026000200310407408403030014000100304645905e13024010901070840f03055100301c04114210303500600300180043c0c905072a000380c491916800d11000540c0d44008180402c0c0500c4a02c200807001a030b41d1507000741a16200c0d800909455141c88401c1058900152000c01403500304010786515489000c0c00880c032080c0042003120407030050402000149a01e0303000b17001805a1074600d0b802d0000024012454011403501c1b1105030388001000007110740280080001a40c420404c0051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 389145026 1250 389143776 389143789
    0x60411040b01090e0f0601140a050d0216060501091a010207030f02040c0228030e10210603060f09050d050a05041a160b011e03020a0b0318030a050315040b010c02 71
    0x8000060501801d0b0030381360010000c65100483c4c80c9030500c40040100100e55901641c202e110282c4041c0d440c3c24a004803070060500d0207120252201c95074040381008800c0034041c2003040c0690800020003103940c442e1080c0e4090100074155102c15a04c8e4072030140c4551000400710100c07074114062000f00442a400c01c4083c0920121301c4085200d24144040701400c0003a034901070300300042c0c2400161016103406070454451480300e40c440c10843d00c030074000d541c000c1c0400a8001d0103030712003441c24039480c0ca908001c0481da00041c025070300d04030703040b500d0728843d6000c0e4851a0280b012200740000802c81212103114200300000020380500c005c100359880c29080c00b00300801200c0550800000e0041d015040740700704410b541c0c803005c06004000102c03600d80741d600d5284100c100c441c80e442c295001300c0c458640e00c2c403c1c4a9581c6001000404101c2c0280701038a01030071500c02d5aa0321044040d00500d9908291800420380455086192052030248110b0f10300200c10b07105e0315240100d903000c0280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 389146276 1250 389145026 389145041
    0x70c0504020d110307020c010e1c03030905010e2a060304021f03021c0207030f0203130e090c2205131709010e10030c021002040f0e0c07020415090b0306041104 70
    0x1115141d00003440c1c08000da00181d03100e10800e171b0013000d1a8500000040c000810070304624020001d405941d01e0300c1c1c070102c1d0b0f13180c07040d50035013000b0403c80702038a031050041c20284a10000750040080c4000f007a040d4a0303850800381c2d000c10308860040106410040c243c442664001d50080400c0444c0c00d0304905964000a80e4455007001030510900740c00c074030114009442c1d1101407950000307140f0304140c0c110b0182e148a040c075100941c1083c9080c05582e024120300d0140c0001600c07010001200d2203010401c0201ea0400544030b9124100c0640301000141030102c40c41c0e600700d00b1712002030444002c0303440360000d160f00a154450001002c1101703100c990300c0200124100940449031003034079145c84166001242071070390005401d400c211002420030200d0015075040500401003004001203440006099660a00010001d500c841540581d58400c201000f50071a041c084043c22205d50442110100c0e440c140040c0800d0002401f0951134a4044070020140401110701c0402420194010207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 389147526 1250 389146276 389146297
    0x509030f0307180503071419030510020d2c0d0206060f090a150f09200d0e070f08030a0e030328030921030c0504060801030f03120e060103020312070c050402 69
    0x503d01e90f1200003280c00e06d2a03a030400101010080c0c940f00040c04c0c49440414040641111002524156901c040c0c940490340222000c8a801007000103070701d00309520548000300100b0710000c0020210040c003508100780074075191540583c00a01204900218020340b042c080104200c5031714086004200d40014007401051125580d24003807443d41e0904032600002e0070322040c0c085031007460060280140c410000960790602d801c44a296000e083d4482503810b80120b01c1404651041d0300e1044a10f005916071048801000750342000412040c0400101240c481ca0f51301c0031564032144085c140d40c1d208841006050320170841c0300300f50148004a240503805000d250120701e85c0742c00e80742e0380d071012807171440340400b0b0f11400ba82e501c2482d00352140b40050b42c02c5040984c103051400d42c001c0c0c50740038144070103007240c5140c1440400b018814094000b2440c0b00c02c404000403040180c1003540c402c000d000403400ba2041c00c018190104405040c1c03121f09502c22480301d0000e003440c0a10019402812412 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 389148776 1250 389147526 389147567
    0xb0a090c0902071a010f030f141908030103030f050306011d150d140106030b030607030b030123070909060f0b0702240d1406090105010c02010905091008010509030f0307 74
    0xc9034a401900007400482e024139581c11103408030845080d04401d060744400c103040e00506042001038452025050003d802900c911582c00021540c1414441c800010b03c1001d01c04080c071104215204019505880c02684e800810300741c01b0741d00713851070b2105444490204403811540c1a41d00b580e04582c40303c84902a10114480d56989a1000d03a500080950301090342c5803868280a0801141100d0042030301c2d103801d01c190160100400d0300c40f04003911400805807191b40310900e40e2003d420840c4030300d00403850000b02a0180b180b4041c810b506403500c1000030107040b4006041c8010340125001e54a070940e03400c01c21860300c010303080b095000005c1240c2140598070010000fa90b655020301c1d0946034011006e54412240410404440b02000701000c2d000c250030a01415072214100d090640d4000e081084541d0b01c5400142e401900503400543d0042e5400204401240c0034402d007030448100300f00a005540b10300040a4a03400344900d01c400080080c000200010700c503200301440e0801c188001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 389150026 1250 389148776 389148779
    0xf030607020307030305060f0d0305071713090e06090304140a0b0a090e011205100207061e0c0f0c050a0f0218070e0f1f0302030903090a030f05060f040b0a090c 70
    0x42418000216031035405a0004241e90040c0354042c092540d011800f00d650448100304500003902d056861a400350420001107802000c0042c0064116842480000200d40f1202d07080340724503400e0501c1c040c101800e820242c82e529001c2d0000740050140c0540009182007605101c1001e0b040444501c0710391303003e003007240f00098074006000107003e0300980d5034407004101c0c1080411524002c0692008000c0c0620107040408140c0c08905030303406650008025079180254100003000e484040d200c0b07042e00940d101c0041503040c041c0e01100a6440580303e005080c407400000b03071200002028080c183c0d8214003442c400103500a8000402e05200070803d43e25035801d0141100119002c81e00d020206190440f0340340ca40c46c00e040c510b070404601b03c071a0704075030840300512009403903900118004e254012000c244032801c240240c0e02d441001800101d60b1503941d0900a0403040b040c0c0301621a8040c440103c0e001c00000c0d002c0e24401c58000f040e080c8152240d80a1200030f18040c041600c40c4820001c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 389151276 1250 389150026 389150029
    0x6120105040c0509130b041407090605032502060702010f060f150c051009150606020d0c05240618011d0415060b03160e1011010902100525080702040b0f 67
    0x80741709449200c01300020b100d00b0a00d0600040302d4403440d08d0003120f0054010004416031194881041d100c0c607207052a22510b03403804046071b41a12a00c807040484078440d4104156a000802c80d00c0388003294000e100e84000001c1400c11a259805034001c14813172210203000030014121440b0062a1624001c0c2c1d6401450300c0b041d0400d4124607c000c0015150031010040c803410540d080c10210f16136000f08600e03450034a0181d9100212048141071010020500003407090521003035402442903556140d840114014103050558100c8005201d00030f910302e0100c90244240c00281a50310101450440d5488c030000b544860600500c101d800c4514802e050240c2281c030300603c801000342c1019207440f41410b512030320214442e001c1d000200700c2250490111982c50b0206643c1d500154104852001d42943c150307405040c05a00281d00200b002580f8403520b0360004c020044000c06c92110200b2903c001400714240c0ca2801010380005014040b0201610349036110b1700c800100180200c0551042c2c40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 389152526 1250 389151276 389151289
    0xd05030d060b070501060515070b040212030a21140c1312034107060204150e01020d020102070309050f031009060c020c0d0804150918020405040b06120105040c0509 72
    0x41010b44401c10205814040080034000c00d0090402205c2c00302030019803011740201800f8406016100b10100c102080564558600c0c03104080040c0f000d80356039020a030006071008910441116107840d0360f8034051308000d003900ca03807562440d04420020030303922000c3d0f5030030311600010301e1081002c1102c880003940c0c0c20382080044010b40302e52581030000b0564500e0300c0c003001c010011414108001c8030312514450140e00c03203c0525420b10a815215100c03400e15200900a0f5000180e001c6540c031005d441c100d400480c03147c070302a4240c6c01c071041c0c03100c0070000700d00380c2c010900018045081c44c2c4040c88149407201c22015411000742c01c949078041c814014805841a0b00003e8400c04d641320076084c402c035030610140d003462805032404401860700b035552070100e102d14440c0d00c51880c02c0d50b9015130b809114843c008000e00a00c0300030405a41c1807040b800c021340c400d200390b6114600d041c071142c455040510582d42c5030040c02220b060715130700c2c0400380009031041c0396a40c2c04100d010003504045a50b00c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 389153776 1250 389152526 389152529
    0xc03031b120a0801060813050606041109190e0108070e0a1a040207030309030e10090b16050703030237140304050402040e041406010b0706020901021e0f0105011e050d05030d06 77
    0x150b840f25042e514102d405400000003030903031030403801c100d00d0410120310000303001030f0006810307600026809190280c46880d409034060709588442045542c2c1d0302c01007615108400c0e00e41c91084074a00384d0f619441d580d510380c0c45e032203070b80040c10316080018144212a80720783d85c065a04402120315020080c006801c9030b004600440100e0b40d038002c10418507901405403e543c01041d40c0312000d070513507944060500502d80c8151803005500080020410750f40e1820600d13815440021103011540b80e02d0007a49400030103c07021480c24240c280c56003052040d1000380075804c4c0c0da1008030540001030b100d9140100c05043e00000c04d210400c4001900e885610042001700641107200361a030903c2e14218079400348015641e01d45610240050100700d06100440382029400741d40181d0310003600005074144201c04440d030b003042d41405d1006825140110703c1507071f0390014034002c0105030f0702c0340103001217130602c48069140840821001e10440c2040303009640424022002c8074181b014411408058410a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 389155026 1250 389153776 389153797
    0x403060e06100b09010212091804050f060a1401050112060f0b0703090e1e040f3003090309091a03030c070e09010b01080a05070e04150f06020c03031b12 67
    0x40002c100c0c10b141071a202c00050410302c0f100615045035500002d590b240c18502d6003205003800202e054142d03036000050300d042a48450101c403145850b042442d103c248c03080c640d42150242c0c2000905003030039845842c0519040040c9a81a170b42004011150b0324003064070400e50599030038011504402000121008000703489505503100c0e003c0c6401400444540d02800032010381c07000744070100820f030b1562401d40c039660444c2c100c180c4d968104100c0d4899010340140ca18100c5100345c00e841d200140b030b0a254541c0940c0c00030210a8694011402c0368200b03980500028840340b0f0521854800703070040454107964107004c4030019031120001e0b0565006008400c00c07a44095000c01c481c241d402400340c6d021311640d0081024510310310000c0d2940700010030556500c0ea440c8001191240102400107103c500074004022002004204505203101d9000c3c00700740c004aa500001c201d840044c500b140603801401035400c194034210300944500f030710380e00c490581c0107900703401418129007030140480c1c408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 389156276 1250 389155026 389155033
    0x50f06040b070e06030103110108070c08030403020318030d090b0d09051b0a0b0a14160501090c03020906060403080d051005090403020102040603050a021801140d020d1e0e06040b06060403060e 84
    0x42007400038060310581c44145002d0b0400707000407c081a0a40b0103010300e07000030f0134241c0c500e5460038001c5444145c40200241903150100030321040c0350b070001c090001c00a401c03c5581e040d1100d41c0802d5507401c0704d0700494001031100780040c0500c4140034003800a0030341d00a03000c0f8540c3d480356100350620980d82650401d41407a0842a030700752401c18a5400106050f031040c5160201c17285004000710100120602810030010f081e9900c03031650380321440c005030030400802c071504003841c2004403040184001da200344a01c0000c1000303440d01c442141c08130f0b03920682d81d904d401d50b010415800b0f00001400d04001800502d400a084e0301d80c094640c5c4500d1081c3e000580c4c0300e0500402408442c00a0403000040d40705200103141d1203600088840f030082d00f404c00c3e000107025051885140c0c4580321a000d03116002103140e035000c1113241c0204104400800007440484038020440046038400aa507090341c0c0c3c03103103001c02c0205829100081c3c0210380607004910f4507440f51118030641e901001009503651 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 389157526 1250 389156276 389156281
    0x905040e0606040b010801030f0807050709050f1503071d0907050301091a0109090c05040203150402191121030405190b0a0b011103030c0a0207180e150105100c050f06040b 75
    0x58103120b1340780441c0e401d00f040603e95046494044440a213050003c0182200040d03210510404112540003013844031002c6c0001d161070006049140d00968074125890000071040040b1f241c0810008255001d860088540c1c01e5540001d04204402402e041c005000b49800410592428004c50490a00608485014201d80c680c1030452840c140d1106c1c8126240c00ea0500c0059248c400360b908492046078056200c3d1140303844030300440030310386e1010760061001a13041c00726552001004200041074030b0382203042c407690030101e0301c1c1c590304a480b01c0a07015042414040748420f00141d5046401542204c1e50402d11051180c44410301c110b0650380a11180108003a144042c025611950320038030b04000c0440c0100c81844d1b80e400040c0108140301404100c81590307a1003000b00d4001413140001070b00300d0305c070780241400091459800c41e0303109010740d4001d0001c803200584641c0c12607070050319021860280100480b04001a210110f455028648240541203420006a0b008034024403100c41c035030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 389158776 1250 389157526 389157529
    0xc0109020108280b03031204050f010f020412060c05070501090602032520012c120c030414060904020304231b0415050a060e030106050a0b03070c030905040e0606 71
    0x4040100848001c0e5882803800208011a142110410399443e00c0898800a0340d4002411809071041228000e51400104002e2040005180342183c50100080007040c40722550312003079100740e002c0c0d04e154040b5002080b00248880c1e2144c55041c01c00c2c0790036414003a0030b50340c66003958030a4000303551058010080c4100b0b14108141841c20b044061905400c01c45e511802070426910b001e2600345059600c080d290383c00c0401c0d04020714600c41003081c12032402ca03406000c0c60606c0c80305030840030b40c030503550004d043c020038604907001114044000c50509217000800c4640720103100c4010303001300c800e010400d600d03241c3d80042c42c0501c0c400d207101c012051500504c20310300c81075401810405e622030754640d04031248601d4403a02011050310f0224400c50312000415140700741d50300054201288140c00620240c1c890700407070600508130001c1c852203603a841040181221405028024030040010990450040710b100c030b09240719003000390070070b80d907a400a4102c070318000300c05400f03070003080801049 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 389160026 1250 389158776 389158787
    0xb0d060906030515090c1203030a0c0206071707030b040603030f2307110a0b120a38010e0301110405030606041b1b0204151809031409150c01090201 65
    0x98000c0c03040030400c940c03540c1c80d41e541c0d5102d9010009030241c0354501107805030b1801e01c11200400c3c405400015101e050350043c40c1c0d04d41c4211600141c09213043c0c0008809072001c5006400780c46503a40e0300504002e81513111041020181c20501410b039100000c5802d5110b900410340150300075160454071400004006c0c00300000980112440055034420320703c4020342030b003651880d80d00f1031500c120705031a40e0086007120065130840841d180001c18106810f4034010702c0310784210710060080c40141c1842c211580045604403420451090f9850f4500300460140640c06007400c4c1450504145040c9001003400c4508854182000140005051180d41020800c544d00402d090b07804100c50100c910103214154000c8944600300903022020792101a0341c254850070054000300204001d102244001c1e00705400d03840b80c5d00101c1200102c81c50f00c84020301c501031500780c058891b0300e9441e11160001420b1782c02280859444641c0344a44143c1058140c0909a8090039000009000005000240c070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 389161276 1250 389160026 389160029
    0x903090305151b0c03120c07021309030c02040c020a1202071d0402030706140714030d050f0426070b01080c0102010e0d020a030c111305220b0402060c0703050303010b0d06 75
    0x46035440c007000e1000300340c651550200c012280d00c41440e00c0e101d040042c0c038118400d84c049243d20190346024407d40b00048001043c0c4503108447c41003891a84440c407209841c07140e0ba014001c14050201c05000d03040a030000c14000c482841554522080d59542150500441a00e0300050380070520921a000b0400701040740340181281d40c40c505c0c981603000907510501401502e04001c0c0b50104000e54240100a680c91035600c02240d1440514284509030303644c121012601140342032a001ca001c21b620765075480e0085420412804c1107085102c155600072101919401c1c1c2e640d000c0107020045544500b8180c041c2c444600074100c0a50720900082c255207022883c5200d503001022540348203500019548015039150400a02041281c24968203928200c901580c10440d60054a003501d07400340c0c0714074401d100040500e1000c0b504c3c04081c811000d0690001420b4006250100f4098680742c0d000c3d0034801750ba841201c545503200e41d5841d05507042a4802030480c480803d803011154030754000c440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 389162526 1250 389161276 389161303
    0x150105213a0206150a05150c010e0f0a030e040522080c0f030c010606080c0301061d150319110f1605150405060705120114010306030b01061823010f050403060903090305 74
    0x8170403400c1200061076898210040080e2250010344030044410a401c044240c840040955012000724556a41c07205400d03441240010344c01130400c0340d130303182900c02c0600a00340304240020001c490004000d1041801c0e00642c0c00300c1040c01944c414031402c21100d8402a40c40014585661048090340d080d559907401041c11300240e01c040007200b042c0502a02d0441d542d0385821410104c0103028407030040d01c48945103401141c1d40c01480007890038903004600440c08140b08020510203c2030b100121202c1c201d2020030074100704000e4007184a0200134045c1c0602d0301c0e0450740020307041d9032658900040c5084d69070154500d2010002800428041d0540c884c2c1d00b070600710b182c1a031010000000c0d802c140210f050a12002200000c41d9210b64090405181e00c92501d10442d41c4900000d41414985040000e40801a40000c2010410f19421100612290100170b140c1e48151006540303045801e0105c1e01002010b110000201c0c2c801d0180d418428002d4aa003099141107003049806c00c00b8403107030790 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 389163776 1250 389162526 389162539
    0x140405090604240605090705041403010615050c030f040e010f0e040c0306110c010507020102030a1802090402060714010207030c03080901021602010e12150105213a020615 75
    0x855426950041c1c8882c180420400285681c0403d00040c0040d0704070641040446080081c2c03160458010015a01c00f80c40c941d00310a521070800d405d9078400d008441c111088a0380000b0b000b4001c0c0090511400e80009076410516180318034171140d04075a0080c80200b80fa600104041c035054204040541150f4406920500c0c080d201d03980440d94920000313001c599521070110541c440203040c0d5001d00c10310701c024001810301d007400a011f50800d4070200c2c0388034940016031003203d650f484040320041e8080c1904196945075002c00c2800d03041040c054070941448551250440c2081c40107001c0b031440380c2c8804507010514100103100f41702c014040076040c0e00c1000b2101c0e800500d0081452925424644030880c10300441c01b040340c200702e08000390802d108120284982080d10550300d810b0350415180101e2542e000c450040d03c103445d1301012001034218540c10344020096109150610700031035255503412141010350203000403402c0041005030060000d00c241d80c010001d01400750a01207804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 389165026 1250 389163776 389163781
    0x15040b0307030305190e1c0215040e0a0b0102011e020a0e1c15020c01060e010329070c02041e241503050604090501050705070326041115041404050906 66
    0x360480c07050811120180c02c0051708010410b218a203000440500a0030004100c02c1845400e404a41c085800724410b904250342d60703042c8550b00c0113590484643c03018090b4503444180d40304005151514496046548a42011442e032101d16071a41305040000c1700160f6542101034000c102c50958900207204285450400f1b90380807503040d0588202e5041000d00950070500181e00c0002c0c402c525484905508280f4005421a030100b0300c40c0c103c2c1d00031940c440714036814241503083e02d070b101d00e43d40c5c20fa1525040401c01c02841210420740341c42c80039000040c282c0e140380065400d00520888601c100b91100c00302c202c1c0a40c0a00c40144001000c0c241c50645420400a10b1160780c0103d1080d04041c2c2d5038000440c1a900c582242280f150460300070403c07420707c68401000b943c090382d410740c0031455000d00e4a807020201d00e00220391a000074002143c83e01c681d662091611b01d0384101030b03840304080b500788903020f420100520041440402a44002100700309000035220020040d6580d500207008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 389166276 1250 389165026 389165033
    0xe0102030703090b030a06030b0108010e10110417030c030d05070f09080d0c06060308040329040b04020616060e0c0a0e0103050606060309150108100b121518010515040b030703 77
    0x15007406031130a000d10f40d40c40340d80302224500146072a60015181c03100000c000030300400c0c194040303d00b0202c0321095810700e611520340142600c07070008404011000c100420030003280f1540b808240000d0005c10303070b49003c0c0c0c1422000d103190000c01810100035a94414498160f8020003000f0b5004e209003001d13003805260084a5460303a03038000c0c41c0409c1c07040c50744600c801c000f6036621503006190310951180d152a245c4c2460500a5111410054841f4404519492561426102070320959002c0e4070400b0643d40c3c0c2d820702644e03400c28140c41e19000740c0c3c0e80c40c5c0d50001c1c20078002ea40a4102050041035100c10003800c1204000003580010340360160350340107102064000c60110b900036401d96803160b40e92a00c0802610340f00c031012625442e91826000130070360803000306082c101c003c400c65090043c0310040042042c8a001c90340040d91550050301480b06a0b2505120140d10016002002c049817098603082400d4030811a00c0508d20444405071428516151051007914002540189002402e698 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 389167526 1250 389166276 389166287
    0x20607091707030c09090209130f12140711010206241018030f0c0f05011706060c01091113110a030b031006030303050405060106030c0525140604030e0102030703 71
    0x40c1030159042044100d80c0458100321480040d580030304e55a1030580c0d2142c0c03100040140342412807080c031070a0089001650b120b0000500c0c07980040400c0050708003681c0d588030f1302e48110801000d00040d14501c0c015100d015020300390441c000d5503407184070042c400009007080c1008241c2401d00b121800c85064140e034101c800000701d04240d49a490011420381e054400d0740c10300c922241594680000402000489070540c804984603400394843d081c2c1728000910000914080d19002603201d040f03480c0d0304d01d000c0b94482c0e0400c00107080503280135007030b44007542555244038055036000e004102c160030710b0030a514109003007682307038408000050250820f01310318841e2107035841c101900c0b00820565550240500c4e600d88030080d10810540b0390f0780c030b00074000d00401c80b02a00e181c020a000042c0090186c00b0308038201065556041c9403a600740d0021108000489082c85404080462030000070769400d4030322000d070b074031100411070f501e002d10f0002c0540715090700090454005100f010000394004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 389168776 1250 389167526 389167529
    0xf020906101d0a08030a122009040213050406080309030c120c0d14010f06050f010f020c01050c03040f060203220e060d1e060609061d0a0b01050c0604030302091002060709 75
    0x1602d010000a1580020301c00c02103540000509000c00076101d81402e4100c1c3c481d5662600c1c03c103084c0600000c0c0c55042c0407610b0355a00c0015008001c101c0c401c00c91600713500900031284d07600a84411641c840c004602100d241e40c1200715031780d1001030505010b10302000a80e9000504036100010451116030054032621091141070241d003071640003008000d210303a04201c52055203002007021516020300440501070900c207013400b61310048152803540d403040300c0b0f0000d801540e0300280303103812000c00116901d81c00079080121600091001050100701941130310b00410140c2c1c0219114000a4901d01c42d031000c01c0740012800d80310701d00c10801d4020315030000380d000d5002c4031204e241c0351090414913040801103a000c403505101c0382900c0104001540501d003941c2445a08011690b164140b8036000081d01c0351a80c03aa03000c01001800d0545590400d0f40745e0a010f160442c01c2c28020400c1c5c43c5000c00940701100403d80102c0e040e04681051442c0d0b407054880c5100030040c0d070610010241c2003482c41d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 389170026 1250 389168776 389168807
    0x4050103061e05040c0c0b0a060510020d0e131404060605150415030c050c0d020604051c05030402060a02011103042a0605090d0501061502030c06090106030203070e0907030b01030f02090610 83
    0x80f9148421424050380b84408495044002207e040c604020360600034540360040d141b00304114042520880e2001802000c1884280ca804684840c0301c4c041140d42403410b005400b0068880c000d402c50310310000103003030045200c1c01010a2150910302040108060054a034a00c0f41f4103001c00c01090100c0d204403189400107050014140701c01c440700300d40350310901d191520107105a044051040d980010710f00e1142d4021030903030314503940340f545840d80c20b12003101c82400520180003140262070840002c00c4c040c002c500000a000e40c11a5184000e1740080310103a40c00c80704a42421f9459108110b152044c186d40b2184460f070790300380600940700d80200d4074002c0c06011389041c800104030003540400080e01a0116105040c69401306c02552513000c04841d02d0180184030105d83c402805020398025240c0c01000b50030300c0341c1041d01284056400410814580c800e808001010030031007440207000c0c0d800307a01800070341d1304a401401300c6014050640c5001d00701c00d2880c00000c0d83d000d8030142142d9075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 389171276 1250 389170026 389170031
    0x3031e07020118080f060a0506100e04020c06010f08011107020a0e0406140c0c011503031b11040501030303090501180b0109020706020d0c0503090615010518030f0a0804050103061e0504 81
    0x2510300040361000f00700040007035181101c5801145201c40004c10200550005044500681d1a0010001666401e0760036a400c20314031072162030b9483c014000c80104100292005040c003515074201c91034100280e00c081c02d800e468907001c1c00411030a009142110400105661611100d8ae010442d00405481050701180020707020608100ca0380d040455041300038001e06c481d5090407629000e90b94450940c40c00c0c0344d842d140c1070210221015480000700c1c4e805403201c110008601c0d41404d902440e100045a081ca00c100040c2da1075234403032042c0d41c080c44c0269000142c0a0280c541982100da044034640a0380e202c8c8140ea80c00500c07100220f41c15102a50409a200c40c0e0525194000c6e00954809004450800e01d00c82c6140b6880700c0034500c6900480119000394440f1a5001c1c01d098660a0720742c00a5820448d0846080044800000440000e4100c50002070b400a05500780300c054a000c444080d00000c080249603450302454003d00010480c0c1026114200ca0b0108081440d1180d20300407174 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 389172526 1250 389171276 389171287
    0x40806070e04091202010221010b04051903051f0606080f0610020120070203071d0a02030402010c05100501060f0509030a020f0406050603011701050726090c0d03030509070503031e 79
    0x102c0d01c0c0c00140e09990301080035001503641d0440603000c0c3d08800a021003d4510841c5001660b2001d00314904952112580c5868682840d003030103120324003c0b4007032415001d0340304d0010010354100090401a12405010041c14200c0010301c01035404a5114004201042c418411940340120041d6084441211141c000c0c3c11612401e80c09001d60b11005e204036440f084000035100f1002d001411920b2080b801d44604e10346844070381503c06807016000394142c003400000750180b101d55008582180c01418006124406070313450900d028826002464100d80343d000400c400c5030080d00510400407075060a6080c03404181c0425500c4a0003100a07104600d03c10f00b42c06951100d40c4803d0290401404c09a034070342e100d001100c52040e6202201d03080c1d41c6001c0000700d40c42d1040b0044844060802c183c1042c034200070b250188071b000090036490b00342c005c81811108070b684240001d54450311a480209e03041c079014000d5420501503900590181c0c1042011001240740d07a8001c00310166000c8209880700c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 389173776 1250 389172526 389172529
    0x20423070c03032715151e0f181a010c020121090f2901030b0a0e060907170c010203041503060305010603030905040b0a080607031e05041a010b040806070e 68
    0x3891080501040038503000c460b402d0130132182000c42211406500c0749951031102c45649030454940c51110b111040b40400c0030300024141c1d102e0042143da0640c002c01b08152907411090150541c2d5020280703c142c0e0b0000400207550303501070b2103002e070008020354a00b000c491001070450869950000c4c100b00620440c600c491035460b01d03100a507158140204450b407003034600340107000a40070040d1100c541c610608060358944989a100d0f40000c12041e0b05182d1030750b91074030f2501c0c101504c002007054450080c150303a0b8000f0040f041c800c405507002071060a10306460304042045180101416400045421110381d80000c212812604d002d04040e01c0d90034580300840040619420050195007064000002c3c154003444d0402600e0080b10300b0851150705404101e08141148240c4074a038002c034002580d01030082d841096104010100c165210799032440c42001c0351411241201d41c282440001c2010500e070603100c5024007040c10490786420b0518214641d10740000302900100301c950226000319 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 389175026 1250 389173776 389173781
    0x1030903170c0a020708070b070204020c01020c011505040c1115181f050609070906080702011104090204150206070e04090c05060d0c0311040501090e060d080d09020423070c0303 78
    0x80c1c180d00718102240707080c14020744490b03a10410140c001403156041c045944500414100704444c210700010380b800c0f050707a00f4007020b900140c0004015540c00c0c801822090401e006803044000b00141ca03840311400c10f801c100c11150030080e41010014804100d194042e800144480302c2c050300041c2200540c0c0703d60503412030a45080550785940103000c0800d0742a0070546980c503040003204014856a90368906001001d801201d40c02c001500c00402005001d004101041d0803042134800800c04044c8680094129445903111701c10320340d0b0000d0708004e00c1d0081d20321400007501d18405007840d4149680c00500c840710b410300350b602c16030703449a40104014943d4404002001c02a04003a100d40018600100424492203c000441d0a1a00040d00000c1c0b003404ca9013500c10584885400c941840340c14008071000800e455004002c00c410f240200f01060050080302c21002c802280b08205441071005070749214110003401842142c8103080030389040f0310383d03600c45809c0c80d00041e43d41c1c050a00710003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 389176276 1250 389175026 389175047
    0x12403080705010912021014040206160302120403110301051501170a06180203072d051c1401060905090103080d0216060f0b1c03020303011205030c01020f0703111b01030903 76
    0x4940c1791541d03002003680100324070307421107606c07581080000a031444090305000c0c2290005d521100c2004006030307960004150100a50003841200c039280084014110a07030b2003a0020307a4200b250715080f0501d80f60900980d9440001c0300c215080314100c880000c0c140000019580b40c0540c2c46900040400740c10b80c0c0000010980b2031100d0710401401003104000354030981d5100300145040c0100c6000f420b0340e118098030750546925852410082880803a0b242e003040e14078a4444016a110014040c00c90140c5101000e9141c40900c0313039450588007501202066000038040c000f588010000314a01d40d01b56805c1c030040003c013681d034141448521181c1c03180741400604103450030359034140690407a0301104440100380c0ea4002e14181083c0c10043c04c00e415034005005134010401800700071480c0b858002414401e0044034104414911a542607800c02e120461071031030007003104010706a020303034100c500c0c004490242004480b0a11001d000d99243c1920030306150b00c0d0456002094400e002109 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 389177526 1250 389176276 389176283
    0x607030509030709020409050609010e07120b0a080106080f0a0f02011d0d0602090f03010b031b06191e0302070506010303050306061b0312090d0804030e01050f0c010b030124030807050109 82
    0x501d425120130b2250000d42060140415652402300018018144040d5030380c103841c2c5d40d0601c2400d9030754000b0708507500340c0314003801d00105803a00c0081c60551035030f001f81d1024200c420000b04034641000602071400f8015510511183d20804210010440000d680006560207103014601d29180000c084600700751030444d15081000c80e201c00041c8000766003d40944035048a8400401e4810740c201400e030344402ca440c5906421a03e15000311081805030610b0500c0b014007060704112540c80c03103000000c030921461000c504503881100e40c85a40f488007070715202c0f00d420f00b10b04000a58942e2940d0341c50500004050140000100c0c01170b6a0341002d5514800306200d204a103040c500c110b180e00c1350000003e45081900c0000403d58102c404240080003a580341c2d0f54007010740d41ca807022500b05d1460040076041c4070f0208095402d45c134480f4000e200a48820f000480ca0344864400e040c21510300004680d18604a9511030411000b024042c1c404c60ba00003c92a45980361418403a005042d8690001d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 389178776 1250 389177526 389177533
    0x1608010e070309060b0910090c03020a0e1c0f0b0403080601090b07060b0a05030f010902091e040305033606090115050411091f090909120f0e0907170c0c060402060703050903 76
    0x8110707c85184400c074155080e1200c1031014030f401400076010303406140e054002060f9130b440f20b05a542400002d0507010200c0061a81001100b40c079480e074000300e030100030ba55080d500402c20081c160840241d9030054420318050035642e01e0f00c0c0b0700c5080e6009140d001400c01e9182e601d440394594440c1091409800001c054900d842c4290110760f0080030340c06012030040e1100000103544020b240e580132465003210380407407040d0383d4a0741c0807034469000070135140206495082082c2d2020300c1200c6c0101140180c030219840b081c022550610700400107215603856170401c1258801c2a00d200c1e81c1710120766055034041420440340800c90418050815680d40201080a100035030100d2182505c80c072404648030304510070744030890041910740b14100500403c1c0710940303103585140319244e4000744c1800752400104030080140051005030303003607501b00c00080c44c2d400505400c84100b180c83d0b80040b450b01d26207150a0034116041e8490400030400303403041c08081002818035004104440e0151401401e070b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 389180026 1250 389178776 389178781
    0x80a09081b0601050603070203041203050d110903060f060a140307030614100f050915010e0d05060717010e070c1b0e0a06090c0c0221010e061608010e070309060b09 72
    0x4541e210203160034000d44078070400c0300000399810110216030054080c0c0d0b0103140760500b0725041c0a40308240210440410804014150b0701000d00e110300002c560303034000902d40e500900b0080515010000c4c1c01c010741e015030f00e02445400d40c8e511040b0411555004202541941c00400080c2400f03150f51000d0710031030800002d10500b225115819200c1d003121000b0078038a540340c44c800d81d90304400d402043c1d00076030404041040200060b0315000b0801051500303c1c100003418001c6440001000d90499480c0c2c80071003442017042d00803042500d0a01c2000036692250b1402c50507200645015001a09115020001001340720a0320281401e4042618150310382503a140c080d0310709004200c611142c26858a01c2c0800e01d0f100c04c0c02810701034031a03607940408038445038081000e016100302c0341c0015004070114000000b4000c0c0100d80c1d00c0320b03130030000c0c10252806800510000c3e22041000040000381c900501c920105840705a80000c2989030029403083d003071a003000100404889181d100c81030804 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 389181276 1250 389180026 389180047
    0x905090d0215090d0e060d09110307141509030f071211040509060f18010905030409140c0706152102120708030403020103022503080430080a0908 64
    0x100150310540540c02c4a01c1c0100c006080110b514003540d90a03c2604800c0d821611148609160001050000c00442c60044a86170b081c003180d140850480748440c5030704040070680703404e10100e00102443e100060042c0f280c200002e0000110f00c034441c07460500490303144002d441c200508412070a800084030741140c2c5038070f00301480e01800b4408440030a81040c1c0036860381031502503580541e8a41d401000982c95224090310f0400d0001c1410b07100b44400f00d5a0040700700240176007154580074001440d521400e04203143d003510034070024003c601e011072081c03080780c2c030b020030841d85010703000742c40001c404a140c00d1508a11000d6441307004840f9890b100c80740182c60700851002350910841d030b86c00c0c3e6020420701c0191079240601c40c0b00140d8106100c1003015501940090000f0406200d050b0244a070b003030450200c7c98070f160800c0d40054500e00c104000c110b403000c1c401c0c3d074042694014040c0d0442c0d04194940c14400c007040102003244907400300c0c031b840307074980c10811009a010031019100c1502d0310 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 389182526 1250 389181276 389181283
    0x3040314060a0b040c120c0e03100204080709091a0a020d1a010f02070f2c0a06030210090503030a110f0d0f170603070909260d05161d0406090509 64
    0x124032440c114984100503c103840e1500c030b001a0048140c58100c0321120780d107103140080140350040400e110703640755141900c2c0d4062041001c80c10001e071005131107a04000126140203241d4200380840b80c0352000800221f036041000ca140e401c2010040d103510f0340e0f4440d442c006409004441d80d030850070301c070481b01c45413808481520004800c0ea01d81d1300c4001d44910407030b0b541e55280b003051906010030400780002c4602d100f23421800006450108003c20807506103124420741290001846a507441c8188114500344500c26081c0550b0f10b81243c6060402000a490744102480c0f8001e0000750300b014481d1000c28401c0c00e00c1150b03404255842e2080801000e800308441c4460980042d407030f4031115080701c0301c3c2c4849600074403001c0c005201142c1001040c00040606031020740344040680f0541e142c0b021401030070200b0390b642d131005a40307801030003a64a00365600600400c655418009914510580c005041240301041c240904405a5a40d01150050a454102c180164140800c0081c0c446001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 389183776 1250 389182526 389182531
    0x91e06030309050922030503070c02061b071e0e060d0210230a05161a0702030a020d05091311090d0b0103151b051e03090607110d02120c0304031406 65
    0x81d1100010750703a030014280c2d00b17041d100110129940300003106001182c031800185a1211782c90402c4040c1080c0e94002402c5070304900c60000302186082d0280201c40818441c280c000c01a410543c080d150b41c4e403502d00d500086601507140082c0031100014407507903980050012954025000c900344503107181d001030448034007180072070003902d1041c2c15800070000d100444441e400030f503503407900b03088501c0c108522504840e1020f44030106807419020ba560420454640904d2131500215502c130000c80f000f0341803041515a060901405101d00c1101d51200c070304001350f4150f88140060b048942c2c0801681c140104c007900358020302054000b20030000c13500303141810ba138003c10b842c10b80c011295500c10192031483d1003c40340c40c0c0030f841d0349107038160156024158042c88d0300c001c042d450002011031425500200c071082813503881001400754070707500f00c2c02c0700b41303a03410601c060880086107042c040d55400b2030480103030400800298000401c90b0a00c19100a075500003220300141c208909400d5494805 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 389185026 1250 389183776 389183779
    0x6030a0209040c1b0b06041104061d01081005010807020f030408010903140403020604030305030a0f0218040f0c05191101090501021237022206090f0f091e0603030905 73
    0x414420000c07160140c0000d08019401000103400d8610f140d40c1c0d200e080d17070040d00d041e0f0811348980c4014039150034400500b010b01450356402012040010120f400902010270803818080d16a0501c034032a400c020340841520380031b01b000d180c541c903900e4089140100800b03085946000106010414100c19007081a20501a9803504079500900303250380300a10452000a520240401080000900500103503a000c0782c01640010a5544c01c642001680d101005a44101d00e24800c45c0e03507289050f102e00d0f011044075139010413140d50405009446482000c44d074540345102010303c54145445418489404500070000340441001882d00f18040d40080d0202d20141a0800c001107614510340d8904408403003409198a2500614110000c54030a0343d030a4088141c007000070504c000301d01403010301d18084084c88500200c1c50000000d2402c04103802c1882202d555880c1000485020400f090545408810000e0124003441d1312811201c10189581c1410381862000401d050b00801410704840c0c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 389186276 1250 389185026 389185031
    0x804110a080c0f030f0c0111030c030403050109020a090207050606150903010608060406062103120e1506030c0a0302091602010603120507030206100503031602040b060c061801090b0f0c070206030a020904 89
    0x15601c2c10107032601505c1c41035900c01d620540c8144d1041d803140030b21030002d400083c1075a01c2c010350701c0c0f40203085501580040c0c41e147e4407509248114204140c0788001040780707490440c00c0480300d0b580d040d100c0e84054802841041184000701c0303400c50341021207002081c000c00070080b4130350301e01c0403548581d000c13a0300303440c850702e01034000404404c0380840044a415411903c241c055156a00380c1d103003100040b40c40010359907017800d0100d25808100c00703841030b20301c003014920030314000c010180741c09651a08940a00c01c040000c100503255080016040341102a042070902403c5104034010880c50340082c1100110f4403000010a0f004001020918001e500761203066480064200544245110352130f0558000c018010302181540c02008910348028030109140b2031450015005800c018040e28040d007003102031043c03d0549003903e4245201c450002c0c000e0060f20f8035180d42030540181b074204c6075016500040c903907a074180d08a0310710950003043c10b42c0768103120100390029042406558000e61 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 389187526 1250 389186276 389186299
    0x9240d11100e0a03140a0b090f0f010b03070308090303090d082d0d050a0f0501080c0a0e0c04031e0503030c0a030b0a0b04090f09050a061b1e0804110a080c 68
    0x610503040c410b407040001e0034000c0a2480e5980d4014075a1440c0c8815526000f5a82d00a000840f18801d040c02100e00d8070042c24240c0608080ca4200b003130900e03408100341c0c5000c28480d113a031408140242100d4202a1080c2c4030352403900030a095124605c80a94030a600e000003404000303a032005000150f038103400350340c04902c000101303d100b2007039400d401c0100e203414019542d203003649800c4251b00400569011030340c00080403268040d180c0a8000c1e00da180c010b490800341c2800c21841580080c50b1590a034034050901c9050300900d446940400707800454a815038030340d006081c80d9207586050340682140c0d92803800a0190303010380c00c90191540040e0904400301d03030926180000300e00b03423a03c03000c9541c901407030406090000c0c80b104455002c4d00362608400404220300b4408120140e0040038045013074580801c241110700343c2ca546000078040c0f02c0d0000300d0003403225401c000310b80f105810f210b420754489040940d02984490842580300401c20008617a1002c0420400d4610409880d600b5114 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 389188776 1250 389187526 389187559
    0x150c02030d0314090307051c0c0f0308011a030c09010302090a150306030c14030c010e0301180b0703110a051603300c02031213080c1204080d050909240d11 68
    0xc0c8180e0301c02400c01e9200092070031040849603801d080c412303036904280c0900300207952210782c1e076200b50a0a40100d104440100041015030031071418000142c0084c0d0b00d949030804820965010303968100341016030108100c0481e0702d8100000c405406852440382d151803134141d00401a04080c08110f800c507000e1080000e850280a00009100e4401405000390107900d100440d072042869840707136070540d01c40308940144444e281342c0c0e0701494014600d1a656103020701c000707001c1c3c0b02515101c03229440d041040c2c1205941c85401c0d0f80b980c04251a80c41100c071002d05044030090040c3d2268082a09180039080082c036030701081030880320300380e01d00f400b00c03502208081c1c1c2c980c02080610304203084440c0c00540c65000341c00d11000c1403403042c0342c202d0411003d40121403400c0911680728121040014052105607010802003d6005861408601d8180c5142c08104910070281448104440d25180d0500c0c0301c191011030008018068070800d2410703964102503620542c461034103801001200c1110010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 389190026 1250 389188776 389188783
    0xf04050103030e0112150b0304020f03120d1505090901140a05010b0f090604090509031803060c0d0b01030b04150513050c0a0f050d0510030515010807150c02030d031409 74
    0x407a074064449182c0c81c9011801540e41c03003218a0115105999007942004103c050400040945404200d0544a280c103205001d0030981400704588a0380c0101d100c040c0d0000040b0486800d100d040c50041401d00e11000f90a1040f042604071a6000c00e83c42c0c20094181c074150f2084c8281050300c100800381e6100c050444089840a0080440344031302000722200582c0314800070803e11001502141c078169980032040d044810686110000342c000048203c0c0f20104140b0400c42d1803001c901030a914103240070385100078803604400c001401e071185604003850380613520035410380c80080c006015201c0c55500710001084e46000340d03407140140c0b48501c4038030720482c40303018828168091540c1ca0120b0403503003900d0510b40a60081e040000800010a900c2c48030b0083d00d000e4111081e00b100d0a40c21458600d041c0780080d40860254940e0030010021544009131040c01c94040c106406541824000c00720340c5d2140c0840065018840c880030110b2641d85603000030100003181e0460401d644484515949 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 389191276 1250 389190026 389190029
    0x3071e21090501030b130203271b0f1c05031306020a080d0902060f04080106150c020a060e030a06050f0603070f03030f050306040b0909010515040608060f06061c0b0f040501 76
    0x5020841d081c421540203600459244100521024041020a00281c1079900840d00410b003010810380019140000d04440b41b4650740030303070103070a4022240300c040c003214030724400b4144140410070942001c1e8071040c41894100c039a6004d680010350342402c000740d4980c418940d030548086013001c00a902d52000c00c0c0d000100c0d034000c07603140c5030100407046040540100301c010b0740e010108100c1d81c03640c003e68000502c010301c1514000710320b141c5081d2040c138422803031705201d001384207401d034070a401a540c0d10496800da880c541070540141c151035000c81c1c03410030980c00050209240c0001d200346544941d84403442950120101c80050b51144011000c200680c440100841c079058014801c03140a031000d5a40100b016000281200b000341c00100054400e07200864242d55070803d12415800c2003810064400c01614184561454098020360311000207180c140420388031404a405685c42c0c90840b0824265418451114204820014020b0201643c040d204100141c0c5407200c9040c607028003030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 389192526 1250 389191276 389191343
    0x31806010f0807030f06020909070306061205070e0405190c0806041104081b0123090915030703140a05030a090e010f061b0c0503070f06080c120c070503071e 69
    0xa8010b00c0d41e50307000f04071000608111081b94007440100f9064583c3d441242c840c56059602060480c545400508260403803481240010305010410021540214400d80c4018042ea000502075542006441450b816143e840b04a14149040546a954010020b60041104642c1007007030085030741c080d61b000d21440c86117908540201280802c40401171403802c02044040c1407900001d5a0180c800d22808149006c21030544804a03404056040c0420165481455900822081c4e10740f4000240d44101a220061103c2c540f02102440600180111058150701104403a01e6501c000d030f001c0c1080c10075003d20000f858051000052020703c0410360070071520b150f1140352031a000f0302c002c07943c140c0b503000341602c40f507a05090004403524204221002445403540003419941000401050b4520141c401240e65505000301d10b44482114551900150710754000790761040e007032910508500070000c0251070343d002600002078102d0f035000b040801d036104510404071140d0703072007200c090f2241001448 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 389193776 1250 389192526 389192533
    0x501050f090c0310050607150c0c02061902030708040b09030f010c05073503011802040803090d140102030c030a0b1c021507051c031404050a0b0a0b0303031806010f08 73
    0x1c0242011500075500000321182c0d40402031788500100c0c5640c6c0c0504000c403a080c0c00811400d042112074031540b4445003e03860f1002c10000560002040c50081e2101101c401c1000c00c48500740c06d001b04100d9440542c03111f4102e465990301c01d8441140c2d000220b00d039009001d81c1200c1c4a03260018400c00a0700686030b00da5506140e41c0d51245101201007002403070110400c10b080700c000f003140c180100004010013507159601c0d8100821010038171400d01e07407010054014002407200d0320001c41654201c28040d202c1101904a90034a00e0140064400c6401c0300c1d4030000074403003048980c2001354401d520110080c000b1070100d00c00d001d100805a03041c880e800d034004060078014a02404d00030602c510350740a20b030800c012515800c0c24140c0310940c1c12401c03400e2040900602d6010300400040700c0034a030100039140f400d0784400b07490f20b801d118024415080000000e040b03401c194088040308801800b1a43c0740c0c03a00300030501c2581030400e140d0200784150000010191488955442944c0e00d603000f5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 389195026 1250 389193776 389193781
    0xd06060f0b0a090b090f0306090c0102240a0e011d060106140403050319050c0d0c020f09040b0a150b03150f0f06040501050708091504091103010e071d040204180501050f09 75
    0x38513016402240880d85d00c40300c10107058071283e8041214901540b04c0c1d2010780201e0701c0d510000f910303004100d8006a001d0f1004115131089001001400e0343c40f0b10400e10100300d040700d01103001e0045c032001e01c00700013900d03988044001c6090700041c0d0a0603a0542e880c1c14030946041040c4030214026844014410790081042400c9080c0101c0000141011402c00905080440140303509110301000c4580c0060f4008004506500e015103001d5661031081d83c5100c294101503c9007420540000c0c11109225166501c014003402c589280070020201d25503269101d04241011103001085405024419030242c100d1a01c1850170905030038808d0700081c059840d02e8988170041d51960000c210990b07034080c00748920740c2e003a180c000400a10400c0111a10380d1542003e5101c41207840e0340243c0d1604001c18001880072813140d051140d000496401d0100204403501112450b120280070442c1d040750020400044620311009000c0b5800584107040c8034a0380c8800603c048540140b05155103ca0754401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 389196276 1250 389195026 389195039
    0x80c010e1e0301060b0c01020901080a180b100e010e070f1d0f06090a030c1502210318011103090f0f0604061e050403020a060b0f0916030b0d06060f0b0a09 68
    0x10724444072405000030511560b03903a000200c0d0781016905e03060b00e9400240c00305040d0782c8241907940c006594a4100704074036016550220404242c0c00080c0752280d80c802196241100340b41d11402410082c4682c1003e40e102c01e618140c9200c1641e0460101d9020210300700060f00502103100e0b18400140d200d6900c0c0020010494404941d01803683c000004010b500500d0700d8030801e04000d90301800c4507410781850306c82000d050f01ca000b0302c50021500401090140f08240d07604500f14903003025503c0d91241c6504c030050016240780c0982041541c40d000c030190100341e1110181d40b01d411070307400341d410310035170303469442d496050520b41030329030750080d0001a0029800d98010604214058600383d2061040f2000c42e00300d0341c00342d0b000d03009a805a0003041c200542802081d001330010303a5820851004040400c44880010340381d070365072030f00c10f2441010484c1300c3c0c1c0c803074000c010006140398030591807400c04400500c254010801d0f0280040320100d2507603001c2040700e8008003a0380d03030742058038600790 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 389197526 1250 389196276 389196319
    0x501060c120503060406180e0607080f3408011403010911090403050c070e04021903030c03081f0e011a04060c0f021521090712020405040204060b0c07080c010e 70
    0x10315196026954441c041004140b447c0c220f521140134001c0003400c00c4d007103c2050325051001300301008014170142006002810502d000303400c48400d5901d1300132580321003040c0480c014000d855110414031000718418150744480000c0c101e03101802072102001d02d05e0701785800e940420344050500000e01001d03003954104000c40c90ba2181c000d00e0aa0304080f11100464140000d80c0c0c4001906c001000902040d490400060151200080411400140b655802504044014070041c09001008000421f4544161030340090441e41c3c0b120211044d46030240018200c90a00840b100c90815520904812001030116001d45206894441c42e80c01142d60301c2075800b2642000300d27000040c0d00c0c111b030114410480034008482c00c0580344030ba200d88244c07903c01c40c9500100190610b40c0114010003a41c080c0d580b43d260701903015207021500390ba0303c2c00850007909256200e1b906262002800079104540420801c040d201c804007541c0990410707400468501200450700380d0b0100d400c2e800d0348120b60014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 389198776 1250 389197526 389197531
    0xc0316140408011407020705010f120b010e030d02031b0102090904021302040b030a1b02070515160b16080f07120911030604111318080708070506040309090501060c120503 75
    0x3200036150644801d42c403403c0d140001c03061840100210144100c0d150180148400b0740b000386010401f05590480090110449a1300380680b1a514a490503160340b0034650f600a590340602141d103c0704100b13800075a6a48450141280d81d10541e110b1810038006008a9601440041180c04a602c80d602004180d031204a40e2080300e80c1e08210014903038401002941c4210000c88001615007078043d1a16001001001d414046400c403910074006030740d5840c1c1440f0580384898400e5211044c400410404c119691006481c03800c4203020400a8044224800950f00295407001060340b03860200300494281610180c0101d00051600b0105880300c0d401625850302900b9100e1801d81003501290412100391400c0e00c600b071003500190200d083c80244081300c0c03000d40074104540324400c407881d501504007110041c4021000291901031102000c103580400790080161001400c1c02e00c0c4c00351940242d882a140c2c80350a0600000c0c001d80503d05000749150450f100c1010408858401c4507a076200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 389200026 1250 389198776 389198807
    0x509041410050708010302150c060f13061a0114040f061409092a0a05071106360906030c2b060501080f0c0307290d020703080c0316 58
    0x60701552801c0c00c441e8010a80548055101d1406a50450052048400c2c460034180c90003c6c00b0400e000c01628005401a480300da400d240b5011034030307070104004100f0b0361154040d1040303042210000c0d2401c12020401940882622484200c0480e5808410305002d14881c824511840705020032010303000d450000c00034600d80c601c0703901c2c00c0070030000100c0e2180c0903174000c070440c0c2c0c2c8161281040c082e044803094491920070a039a00344a4031103001410391050110082040c5401400487d0799100c02081c1e80420700d078035143d40c00716441441101c6012090000741d41c1c1801d60804c0c55009801c1490302240150f40140280c014001981e090180d52070351001c22104560589a4004240c11208025200d480c800c0d240800d0652400412a2401c2c640d000000d441d0340051a40b80040c0d90f0029900e0100d40308a05440110080e1100080c40007410340c0501141c0703540041c400c003c404081d401042800e100b85c54840082d01e440d04600d10600049074080c47c550203211114071150b020b88d00c00c0408806 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 389201276 1250 389200026 389200033
    0x507030e1005030a0e0601080c060904113004200a090501230f0105030112080f030c0c0d14030a0b030c131b0806010507151d1b0402030105090414 64
    0x2228800715240340c64811060001400c00310910000c00c07514044d524008000304003c091079418070715815100d10003401c52512039440002d5102142d00d4540100400c0c6140246454448039800d030616a070001c02d842c0701d00c0001540407040d8483c04402c85407801035270402c440500e12956460303c1190580d8143d0042c1c0d001040035000940b410b090301500d4060b002d0450004600407420f004c6030724045062034458445c803801403050302c00d41d07800701c00d603411505170700042c040403000c80c1450410340c40392480700a0400c00002c200b02d140302080000b00390128481003110800100c48108442120356084c106004200400100c0e01da10b540c4e800c0200342e000c0c002c003a00e00d949a80000901d90000c0c0002403110340c3c0c0c6a00d401100703a141c81380b007000407502c503041002e8540360044c002003c2e81f00e0560000c201c2000c0c07050358200b2180c01c0d80504424040c1601900004d0705150010360307500f08040d41d86160180c1d03e030000304917041a00075241200d001401d0800c0e140ca940d03070750805c1000004e100c40b10910 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 389202526 1250 389201276 389201297
    0x120906051c02030403020319030b011209110913050a080307090e16050c070801051008060c0c0a0b0a0908070b01140303040b0d111c020405010e0103091e0311100e0c0a15050703 77
    0xa040d00c0181c0d222417141c40c005000c4002b2800503055004610f407040c1c40500c0c0945000c00324092011511090108899031440b41e5110080f42d44a21100741001e86907200d20091070040003041c0d4029400782605480f1401800c0d55200360314030410007114281c0485030654213401e48240604080c0c11615501811748180300e880d6461030f821500200e40e00034904205034802c00402c403041c0920360b044946a980103140c6a100b2078a29070b503001d0482c00401c6009a0b0f00011030b4000243e04c00701400740d2182820344d4030400c0f800c00e4082e84800b80501168068280b141804034600001180d0865588075152030500c100d0701c1c5040c0c0104807103401c40c1180d00b0100000c1039403401100381074055a0384000c005803140c0c01c160004024000c4142400d05240c504026100441c031000400141d000c4504541155006146400c5031007612002d0181c1c914410f840c481045940c041d0840e900c074206c82c5003110b448001502c20000481d540d8800c071080e0700c00700b94000b0340c60392145005100345402400c100d407290 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 389203776 1250 389202526 389202547
    0xe0604090519062316080f0103110d06050403030e01050124080c1603170606030606030a02090a08030c01091103060c0703120b03070f06170103020a0b0a0e030604120906051c020304030203 82
    0x13440040c80d58403001100c0170841043c916480a0700e100005250000782c3d890201482d40b40da007818040984071006203d0100c03d181c0c1d900c00741100d00c0d87c2c001c005000d2070400c0c0c030700900600780401d2054042d508080012801340d4091109120720f0380040402c07840a280e1901c00d03104440060914802d0100c201310041c0b40029041312208420702c03940d148044842c1000d00e41650241c060f14062281c801001072120720b40c1d5010560382c004807810401a500e0341c1c4000007416000d40d9034400262408041031816101c0301c10361000740c0f83c030300610854982d00c416004040d00d4182c1143c1001442c0004c2c481e01021901c10100f42d5410400c44000050381c0501310b00007441d1081561280c0214910244280551640510450841300b43c07030b5400d000950559000849c1c49001d40603108401300b0205102d05881e10400703807200c00c0c0f8070103001e0b00c5440c1800d040600c503401d140d01a502c0450006500010380c18070510844101c8080c1c207240c9a81070741ca4042e010042d40c03000e00300f581103120500408005c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 389205026 1250 389203776 389203811
    0x50a0516020a06080f070815010e03010b09012c0105030a0308040f050304120614090a060f0212090102070201140309070e10030501020307171302030307120504030b100e060409051906 80
    0xc0d10315604d50356000d1801c0450400204c00c0145600100031880c0140328a84840e02000e42c075088003400d02da090318500c0004a8010042d100101c1c1d48502e5035000090315110764030203c9070b11110001481c43d0700c0308103940440512801e200b5a60164001020b00340828494002260028070403a4103c0a0810544805141d80c2103504881030b4101c0030f03030400d81005551b129000c4095203410201f03420f8038103122965200c00c031059001d000907483e0b4030550126111030b0f0440f0712485210f84510b0007414054241e074000e42028804901081000105043c00507020054a01c952080d800070701c10182005030400e142c00002e441c505100e040d44101100048080c005144182441e54a007040e6103110145c80001440203001c0e00050b071248035071308002d0380f03021084900e03154101ca2480c04002e07a0710021102845940d102034080780c8810180304803510508002c804417583e0343d0328219661119000c21080b80c1e802d10006095074031450080d90189018400d4840103801074800103001180149800e00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 389206276 1250 389205026 389205029
    0xc0309050603042f0102190f030c1103070807032d060c02011107050a02011815181203021f0203130609050a060f0b0108090120031b04060e12010c050a0516020a 70
    0x720001c402c0d1115020b541e04201400d01100240c0308900e10387c1d625100c45511208241001d030400516403043c00a008880c4036107000104081e085a40003a40c1d00180c5031581500d00045070307000c801c0c1c20640000003584808540607032140e488007240845980d1118010403580e01d0042c00c1d5500c0e0070040d641c98040001411402d40500b02a2080ba800d41c070004203114072181c851035600c0008030050100119000c901036001226041040703000d1085407070403c14600030790188842d05080d032584410103a003c2001e149171480e0340c0e86040e00c0e00d000d05041c800c0e8003040369601d465045074030741000400d10682100c41400d020b00103462202049460340c109468070030b0039000304103855000d030b0410381d603000580540c081620307002001402c085441a80308607000e410080400300e80407012030100154003104c60841c0c4034440480e40e5075a500c030006801c42e091005a41d108258405e400d10000d0300600905480303890f02c1d95400d240c07100c00c00c0d044e145500104545044214031088280041e10f40244020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 389207526 1250 389206276 389206343
    0x1021c0e0a03110f0a030b0a090f0c0605040602071a0702010c0201030b090405010518010516080c0c030406021c17010905070306120c14121504021314040c060c030905060304 76
    0x3030301400d900081c811407803004e03003501340074070400300c0204013140c802d15220750482c40f1120041416421400d080c08003400554000d0028103039040002400d607000001841212010f4090b140c4c0196038030000750710803044074891320340c0c41c4003004100300540c400c0101d0003995105050004034048444045100c0304001c440807985a990343c418007404820810303155000403604070090020340760000e080c1c45031400101012007800164000f1459204a00059603c442000402c17291540c0d55403500035070b00c103005450f0488440c0303094007400d85988039070392000304071171103520601d130320391030303d100c003801894000c103e0810556150000b061a03411101891012406185981d0040d0f050100d008140e0484400e017a100340000c1102034007480c000304540c40c05001c140c0c90a003942d900e80c00801d00c108500e03003600903030501d8140e0144245003801661400b5601403c10206d450340c80c0d41c8261400c1d001f12402802191035144100007602e002d03030080d07070701502c107200c6040040303200c1080c1b0100f8948110b120 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 389208633 1107 389207526 389207543
    0x6290f040b060f0705030301030c2c090705030307050705130b030d0e0f0d0b09070501090605090904020d050a0521030415020703020106170312090c01021c0e0a03 71
    0x103a50070b102440030f05079880c19546011030f00d03503009001c00c0312000014540031a201081d00043c120340400a040b0705a07000c00840010b028801c010583d0095106805001c100b50700c1c14400703084154800c00003040b085040c007013000300d10352414a6034002c1c80d02d415510081a0780005104a45c3c220509003100c0300811400803480501c14a602c0682240e420800c081c100022219520b1103500c18400340ca0405480e04011602400c01e445004001142800015003a02d0880c608540040c4007c003408910412981c03414100b094804003035a02d0380080d22203030480501018600e480130700f5a01078510390300c0c050b40c0d00fa250b444030024040c0c400b07601260400415000b54002300180c044a01280528480601c0103a500e902c1100c0784031079140300c81d02140740014001090700c40350b00160050b250141c2e118400a1003e1110b00c01c81e01041030b81d00070300036181c50301e601900185001d0080b2 = true := by decide +kernel

theorem cover : BRFrame.Cov 389028776 389208633 := by
  have h0 := BRFrame.cov_init 389028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 389028776 ≤ n) (h2 : n < 389208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
