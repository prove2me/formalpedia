-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2452
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:45:45.32136+00:00
-- url     : https://prove2.me/submissions/4445907d-2f72-4006-8728-4a94ae95b04c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 440827338 ≤ n < 441007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 440828588 1250 440827338 440827369
    0x6020c040213120302030c0304030b0109061d04020112270506060612060f040204090c0207030c061706040510260c100f1d0a0906080106080304050112021c050a0504020f 74
    0x95904007000802c508140c070b03c0d0f065000e0700681e1b15100c1c00300c41f090306640c000e401c10713600d035014034004100c0d4290a1050304c000b44520340b85d03c007001d019541c01740117030900608040c1c104004041e44d4240d6003255440724924104030ba08642410414043e95a0440500c03901a01d03207001d110001841c5083c0481241d00210200031000c04a607a00c0b4100511b403074550b03a090303401c103174240004a506511482a88201c454179001001c9461a62900d5114005607410000812050100f6040c3d42040f44a0190700b04d1011100810320345d4482d070000c0302007520b0350320504c0300881149444403160203129180c1c0e00c003800b80c0159480600e5503820300c490604469104400a00b2207601d6040c0e49108500070f0300e401e4101185642c0700030813038000503141542c80c0c20041010f59201000c01080d5000d200b55001800c45034081c600b403d01c2c16002820100385181071204030303600015013801d450303402c01006030f4440821801300814100139000400801e011130f02240118842e48554142d0316001c440804000b030b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 440829838 1250 440828588 440828617
    0xe04180807060e01230f01090c0933180b030402010903021c051c0206180316030e0a090f0b03151305010b090a1e020a120902030a0b010f06020c0402 65
    0x1000c590710140100280d210081e0703c1c2d565801c090400090f000300b491380c4211004005105414581d003060070307650781039211b140102d103440400c445140e00710004408480c441c041e2064010400b003004c9a10704000610600001561005440080d0f0803042c120f104030200707078030607000702d0f1501144e4017644010b0f03601074045500c9480400051074051000c004462441003030701000c40380c560380c05250400d4400c90708005106441102403480c0d0400c009640413070b2000c00512080b50000c141c1c4e45070b01c0761240d0b51004017019416002454007c0c0310214031808081c4c00740d04403e95a1181000034069040074041e40360811460380010b240c001004000701011801d00c41c0140c9070420511001c00071030000b01c40350f540303412a200303584c2e8440611a01c20f80b60258049038181708506d00b00c500303160316000803551078411b110102d4015840682d16056000c1c04a0014201c406400020f160621541000f0088541315002007030401c20080388208990a9400311802c69038440b04202c240c0c01410b0907040c070364 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 440831088 1250 440829838 440829847
    0x316140a090923031e1b0106030606170601050906010804020109150203072009061908010905060604140103030c02100e030a060b0102010c020325030c120c0219050622050307060e041808 81
    0x1200c100e0300800c104146ca10408000b0024007004500756551588151940b907600c160402c41e010258042a40380d902039005003d0643c1040001066207502500d447c3c10011030b04005021a4003811042001d0504400d101754040d01c0c541c8000d56a0340002d074221980241000001c1c100b5424001110760402c000308110b1250360f0b04030502101d200f41080250303207072002600c005400300007071049060381340c0150040c22291400d1000d01c400e691200c0c44850703200441e0300041021039031002c0c400030401d5049468408001032070908403024104100043e0b458014500c0d190104a240da10940320040c00b0f800074040c100c0c0d0010140e86901a0580031010040200c000c0501e1841c03402d54851190710a050452614801313403510710090702e4800581c1c000c00c00040c1e98800754584140b14982d00d01c0040c10310000107003414003148441c010003c41001206c1c804100000001303141280b0760207002e014088804060b43c60900811003600901e0847c02145003203119551015580308100d03040d80c000d03000f00c3c0390 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 440832338 1250 440831088 440831137
    0xb280501170a05091f0b040e032701031d0303100f08120d110a05130b0a0c0209091c0203072a03081c1a0306060316140a09092303 57
    0x81c1c14002c003904c00da40504018190042888100300c880b4800d2514000b442411000c14042243c03840740d8411201c1e402030104900945081c0b04038000000c22403200509030540800507005444015241d1041004250500c150b600f800000b4520917001d0084030340c5d4a80d6908200c001211040c002d00706030340c01040c070f620a044c5039440100001f40b1888000146000d80c454401d08035000100300c08000b600005444542c17114010140015000c01e8030240e14040c11450081e0803050a0000203006a0b000d02c0040c0c2c0144081c440840503d021100460012903000c40c02900d070391100f48125400820305d00510070880408101a440f410b8101c1e4406544d0300303588501c00c0075000020014046c6d9113000d000c0c8000074541c025034070090880c00b21000896500010181450401040c0318000d40c4180346161f03400545190303000469580b1090084038207a408c0205444240c0c40e04218100ea04105004040010680c100c14608205050940601506800080d203070b200310450502c20000038131010f001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 440833588 1250 440832338 440832341
    0x140d08040b0414280623040803070507060822050a02040e030910030902030d031d0d030f180b0f0c040b03090a1208090a062a020c09180304090f0b280501170a 69
    0x403d0b002c1d0201d450741c2e18181b84082d0f00710b9402508941401d803c080744e440c1c00c1200401c082005400603080a141e83c2c42c00312410038100b2911b881b0072040008021010302070110030f01c038281600750003420a1115800c005187d903901e5200b40e50690140d90000d0901049030f00c60310034803021942c0140034007001d400ca00401c8000c0d042108440e4200d010311550065a090204002e04510505490201d41c05000c00700040440d100304001c110707886c1442d03140c0f200054680750030b9503110002c000c0c60b400702c0d1074030740c040c2129000c2c40d0080e1314820000014021145000118417001c10f00c900c2c030784c082c664034446080f240504207480140c01d40c0d010035090400034229401c62024100d20b0040307200f034102c0070f0710766444484010305e803030015030010003c1c07150a04000c5051980000511503028020098440050741c0703105501c03811040700e0380e0f0301043c05120311607001503030b01c00e000070329100b000310600f80040306616460400c180e9800e042440001c1d00d501912030381356086007807445da251a9881d40003010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 440834838 1250 440833588 440833607
    0x60a0206011e0e10050a1a0a1110020406200a0807060507260f01060807200a0c1502010606020a020612040f02030303150a0f140d08040b04142806 64
    0x1007007100000c0100d030742c0180f0798583d40300d4914400d2000c9420f00d8a000e10a0000c059009032490302c0711307580e0001010140000311092444a454040da20b52800400907080c5141c0c203444100482c0000b900007102640088185030181c01807842042c0d10005103112581c0d410401001880702d05c0600c004c9000c11362039405a940059a403c20b014481801030400d6114160032403009074480d18481404004240000590301501407400c20743c0781d904294501806000e1400328200326005480c61107602d030502402000d115170390001350349441c3c0382c450201d81c3c3c0c19042607200100540c07800c0c80009000e440050300c218250b402030a11840d007000007404840034100108103036030700141043d9603401038804000175845000f4002c0307090125000d040c200042c8050300d621080c1c90704c50248052160394407014500520b24011685520000c920b07250151260107998850013440c03202090020300c4685a104154000c2021500d00c5081d0000000303030229408824004804601200b00a0010600401807030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 440836088 1250 440834838 440834879
    0x304170708121b0304090c170405030904020a0203300f0403090b030a0e0d03060f080307020a09181b0e130c090507020a0804030c03030206010509040302061302010905090a0605010e060a020601 84
    0x20701c0040f048445162031540164040100c0c655500740320316003982e00500e9a900c02c01c40304144060707070400b0740b41c20b07030342c6c0c0149081584125400143d20050900030000c07901e80d10460048070140f503000c0410b86d00651490074000b194100c00c040020a0340441e04809480745605840720203040307040c8682c0760303565000103024100003a6207804407d0000740410420b1044550b56030041411403c11403071100003062035019842c594000c1c0503030030050b80c5003114441580c04034540000d442d03009200c1540c136000f4018020b408454180e60004940510341021401d4a0310040c0c80003154603508003503880da0400800160252070180740c00d0045807aa60091900300a9034411120507120350788800106901680c812281104a481c003002019014003406004281c11034590f009407600780c501a48800d00100800c400c400e0304000c1702e04680c018100c2c28058940030b444056140b600e020700400038030b0350340101d03030114882d103c1c5000d280c542507040764400d441d141e000d086c8036481e0041a0300380d80442c1413107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 440837338 1250 440836088 440836117
    0x61b030921020f01020102120a020a0c021503040c05010801061b03020c0a0806190b011d0d080a02010f05160e09131a041a2707030b09030417070812 65
    0x140c0056501c584420051068181d0030612064810046001d0103840040c2c156401400030312100740700d84d21880d510031000c010150391005e102a003110f45100d04480294080c8200c0000702012160402561096100f0000119125281d40054036801000d20520000a8020070440d504040914000406070310a0048614108645000802000c802e400c001c902c1c1c2c1c0f0500800010004040040c40d43c4000504208880400000028101c28030041000e040d0256075154640703546030701004421041e00300c505583c82d01c001d910700034080c2003075881c111001828840489c000c035055060300d201e880103580754a0f0500030305405000c02280c0040050010fa524000d00401140c0c46100c0e180105e441c6055241d00ca1070a072400003040c00c9400002e0f243e10082c0d10406c2810200e0308a5070340b02c1e5108441c20781c0c5601c040e4550314a400342540004100b0080703c0148401d0031000030181007900c006901b00402e5040f8205e0050f6680c03d2446401407542c40008680e55042d0104014140f0700b031549803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 440838588 1250 440837338 440837357
    0xd080c040302041d011107150207020d1b1d010603050610080a1e0903050319060b03040b13060606030e070b070b0c070201050412050d110a0f02100c0606031103060907061b03 76
    0x3013607084079406000000264400594282003010904010302061800c910447c140700c2c054011401d20b8403040d100510b1810411702d506055084030b4030080040490f0107615102d0078510341e4003010a034003845010042418080400c0359840c01e503012174a03e00d8a5680d0b0041a910039071180701030300225802e529035004280b1111090707644d501401a0807030207621420354a00700a17000303021300c1090461042c40301d45808030500500084108880d00a5009010340d1455103c108400d5000e0044110040049140c501c0011744203400d900211228481281540e4642d5507a9540088a00c00c4010041c00301c0f4011001500040d0380e0405000054010314000b4200b64a580b03c4170411160600c0c207841c1544900c01720030b0941d9104072407603041e00100002d0204a00a961942c10408051500070b108200c0241400d5000d03204042d01410150481c0041c80081c1d545e05100343c1641c40c68000d05c1c02805840006101c00340c00041420850f0f406a0752205898020324603900509400c0c1e604a040001d030342c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 440839838 1250 440838588 440838641
    0xc0f0108101205150709080a0f02040216060b0f01020a2a03020d0605010801050a0b180a0b04090803010806090319050c0307080a0809150114010c14010e0f0d080c04030204 75
    0x1d11407030b6480c0c4641c004081201c080400203102c01c20040202d410000b0301034052101c1c503804243c004245500001201c080c410360320018010340164100300890a00600040090101c207800400076004246c0300c940164555100481e12000701c2100940049400d112030315051061a40c4804042000080b01d101561a80d0025824511200c42510815240c10051010f26000e205080d084440c004007040b00c5641c000115001000b00464206041400800241c41c10465088550503800040041000d03820301c3c80d1500c0580c00030302645d441c900c01c4200056006a00208036092420200c0c080000b03c0d64008045800381d021010310020390001380203000004901d100540382d02c0c006501ca40e000340c540385600a240c221010301d0010402003040c01006803010940709030b41825003e10740704041d50060f080000409000301c0d0b562129610342100300c040181c012421200b207a4840c01901c803c203442c604207c51800c410f80340b059051900f040104010301e80355001094100c01510410014440d08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 440841088 1250 440839838 440839859
    0x30f180d060c020a140c0a090f0f06151d0a0b0304060207020a060f020c0307030b19021605030a11030903030307050d0e120301080123130f080f1b0c0f010810 69
    0x10203145003da0712035100c207010050007580301e05404c281c01c00101842e000c40f40000b8000900c80c03144001c0d50382e40707900b1040c20b01c8854200d0300494101c200709124580c0d64600556004030101c4c0b0f46000109480c051b0800b40c1d144103022500405c000700a030042c5d50400b6480341302548043c00441d200f60b42004004010703218141c104000700f01684500f441d90f2180314002e4108004400c03a10300c42d8201000c288001564a24100d80203203220390242083d103803e410600003032040783e04034100c9010a6101c1001c004000004000604296031008540a0581f40c49a502d0240b0540d45a15400c280700141d031807440340c0301030040004840f402091908829450f641410704610248040440c00001401440c200340038650744aa540722145003101a907500401c0c04800152117039241c0010b4550080a21822a021469540c0c11682c2a545c3e0b01c40703e68200690b41c4042c050000030400080c90802ca1840814950a4090302908103010103582000441d0503000081458448031842c078400308000350352 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 440842338 1250 440841088 440841101
    0x6020a1b06021c0e060109110c0615010f0507171c0513110d03021c030608030307030501050f0f01080703090204060f0303020604150e1203041109041b08030f180d06 72
    0x25001c01a926050304107015603405504610a000b00d00b001030906000c1000101d990460308801e00010b1b550384c0d4101c1078541c9124400c00e80c01c0c98410036090091840480d5001903102c84241c031178004500c54544151a80e0045200c0139007544c00016003200403400c880000d14045c0e02d0040703000001210045204200c07030050340c2d90855400c064603c803041200c0b1070302082c400f640c01ca800e2032540301d41d0f80e4002d41d9040d9000c448860300c41491074403c6400c3c00794000340054400041543e40324901941700500a0500348038452042c074503c9c050711447d0410279255040c60606a444d5503450b03a41506c00c2c1c015201080d41282c0050342ca03c0c00017606d801251007213015501c00d90140c200c908003820305101030760000508480345441c1610f200000d00d0f0010707180850b602d0f142074990300c942c0c803070a2045060080741a07280d00000310707a0401c000c00111042054a2a82000c00301d51a15100e40d01c5541d24000e20208030078005040103404030402c8652041d060441c4000c0c5180070074141035813041c090307900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 440843588 1250 440842338 440842343
    0x103061706041b0b09010e0439080c0d0c0e030d20160e0a0902150307032d3204120f0804140a1b060e0f06040306020a1b 53
    0x7042003400100021440314804001d00c1000100c00d25050010181203481000b0300d071810b101c000801e010054603680c0107040c00c900c468454000ba8201c5014001410702251060300c0030000b041000046140640c0c10346010f0444200d0042c10088401d892070300620b4005240424080424851f10240c0d408100e9044071034030a0755901184046560300d580c5008041d0301b9041030341c01000d0005190551410080207c9105450950554454880e000010a51070340065004a616443c010542d100e10000f94000c1c1d0041e030b01044030201000e4007980082c03c03200140c100c4120150284070101068201e41d2044482c003044900802403004888100d80090801d04203c0c0c8041d020041880105805070b10145030320f0810414030300c0250401070a054000300020302d101c084103200260070108021140190f540721100103503401f011103035040400007034816100010006501d0f0342107410700c0c0d80150449440540f0741d44c10607007140d0701c1c900030750400c00201c0d04015044c03503040501140c1c00c0c1760700704a070f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 440844838 1250 440843588 440843593
    0x90204080d0504031128091a04050906420f030304060905040f0204030803130b06030c180901240e010608070507170f121501090f060e01030617 63
    0x3854502410709108110741c0040a009040c4010030100740c21824a110a0f10308503a240700a00844aa6003104401001d41d079000d1681c40700d0101d881040c43d4070004c9001596029180d850301c0b081c0030042520000c440841c0d490300140041462003008a081c24000700e0005051101d100c4003920700b0004445011100c80944462642c0103014101165040f5070188160301543c0b0340b500f0a0406042c040051050f20f01a5907501090310445969a0640d000346074007218080d0340c0d0030480c4034120240794142050320003400c4c080c040360f124680098640e8400f04e0241104900121482800403941c82c02060304266548407480c00e03200c00d5015045512103140f181e444200c0347d04101c25003d0f0308205801010600c980041401031031500328042e90005640001078000204a1140441e60340c01340015400780740700040b581c051103540e04c581c541d100d40200080ea100b45500c0c000115440c508501c1070072020700720480c007807103010f10803c040c0189110604000c01c0300703039480380e2400c003031802c0c0700c0c000320b00b0f4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 440846088 1250 440844838 440844847
    0x13091514100515032404020c1e0613140f0a08030403080a02090d020613090c211b0f1110020423010207061d090a051015080601081504060902 62
    0x5428051401c0040c0c18166031000e02c0b06840714240f44a84005803400d049802c603010b6640c88444200303546074242d02c0150040d51120340da117255650380c1e2140d62400180c104030b500312020311080020202d110b8110008420341600c800d486506400405402c2c801290058603803402d1141030130081001c01511800b815035480c9000d041c000c0460030080c0540ea0400e0041283c050705980b60f040007101c10750110b801c140e83c3e0f00c0c402c000c02c6110004e64840301040d810150b48078102c0350020f1100c0390319403010040342c03144a04805040110390b11000c0701032100a00c41d5014421900c64842e0310101925824108068003824404030710308035802c240f448180c0c1e00010f00b0700c0a41c50000601c4542008050100314801c000000030303440b1135043c0103410400066083c101d0314500e002c03044140e408070180a480b11820054400d03009804201d42031032a52103e94800620002c0351700c841a11801f0a6035040212f442d07680045072454000b030401d00c040c14400400000c42e80da20b01c00c507001040286801a5070707 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 440847338 1250 440846088 440846101
    0x1a030319080f0603061504140703020301080f07030f0b0c0f0c1b0f01020a08181207030302190305031f0e070903060b010f050d050603070b040b0d180213091514 70
    0x201d000003003808072000c20010038800c0f9a140001c00d590809406492034028000e1500441d0045c1195840c1400540a2405101c60140c02d0742c0214140d03001402900c0081d02064542669580e07107210041407000618100303c00704083c0c0412540103001c04041f03510f000b840d054002850703008080c01030002d400a07400c2110305142078180701141881a561405c103010b01c10300107500c5004c1001c018203844030015561742000204405401d80160003171514a140000f440c8447e0750b28400d010460141c030a1130003c10f28900c1385034040c00803a9140c1d80b214034560701c04600038026030030708540504000b842d410100e03000c586080c80511851055442c01c7c0d1141c60340c10f00d04140d50b141108c01d414440c040c481200c1c281ea00c4007c9400703009600307501081c0e684a60b4046850106190b120708085840071038042440200c040041c10150501a014030030b042c0c0510f421364145075509002076204101c00e046030303410303952500044081401602c03010403403001d10015606858000d000c020300342e606041002031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 440848588 1250 440847338 440847347
    0x61206070e09131a042f09072a0c0e07170703020c19020a03050304080703060606141204050a020604120303060e0403050a080907030507030c090e010902030304091a030319 75
    0x6128079151142c0c1003410040d01c036000014000303138401c034400e140f140014061040c1d5130f064070108000800402d50344c1400005d11550240c8420140303100f07903117000224140302e20032400d20790310061111008000c0b10b000051306a0400080c90101c40d007060203c00050ba00900740804c92140c142515243c0c600e09070482ca03a18407000081c01c20082c03601c10b0080c95400500021840d070030140300c030500c013200c0c022400001c030f1b01046684010281d100019021030382200100d0003000300c9220700f1050021a45a80007601d1b00d101380c015007410b84000f0300040000e45005680550018003032020b0352660342941d00440c1980d03200d0303040084c920a000f10154101585441248002c11980040c1441d9040c035540c003c20310710510503032404111345030004c038034814000d211030402158020100c901c0a0703035928051144908501c10381c03c6203850280620220201030103441589036000300958070703250034401010014102106602c0c0c0078200c0490f00b03a1162070400092a10180c440030304a00c40100020062 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 440849838 1250 440848588 440848591
    0x10c0903061b0f200d0f080a0b0105030f0a0b10020d020d0302070f02090c251707050d03020d06050d05060405010b010c08040b0307030e0307030801080f0a0b0a0203061206070e09 78
    0x194403072241c2050051140e0f000b03c1004180e00b0516083e1403403203204c00e40d09610f1620150403c0e0750b026a4540c014180e4010141c007464a00c0b50300d40101d03903070307541800208441240070303400e010400410006010a030b076102000da005241a100040d5914600c0124681c2400d40d001d21015a0242030240c603010b40400a20941c5036140c42d0640c54132800d507440b203480c03520b1050000d0088400201240c2c203020340b14190f03a054501e00c1070300e00e00c0ea0280848900a4691803000350340c0d54003880c0545c40c0a00111045a0001e80c005004025515843d0001c034005d40c0134016090610341d8917032010a817661204450510940210024030150a090502d527007143c4200e06c0c030905004201008900194011040e10100c0301000d1803143caa0b4bc841e44140c0150070b85411012290100141120030541c1201c0514140c3d8150380c11105050448911a65290380c0110080e02e013007040c800180c500001500110790000d00030301040c018007132010000b850410300356440c0022500741c0d0f102c11903d00301400c1c0030b07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 440851088 1250 440849838 440849861
    0x60403050610091d0c0d080c0d1206090e0613020f0d26071203020a021005010b0a0801060206060607170f0a0207081209090c0a0306030503040f140a0312110708010c090306 75
    0x2c101e0521135100d070035500e1101155070b0740554000c00c100024480c200c02501c0301400c954060705c81255542d00300905070803040c144000070510b004408150490782d8414034840c3d10b0300c40010442034030b6000f500d0180e90390018080340c1c08059502e41c190320b80c858100030071381d4500c140c00a04003250180c60040000f00381c20110080010280408800704003080426803500480b4200165140c0907168124100b0440004c1401d503541003200000300000c00300700030041003004c0d0340d5211a40c5d0300c0b2102280c5690084c1c4120740e000c3c42c284541d07404141074100d00300741d055050002d1440c0490080502c600c64000c0b01e5400f0150300104410080b501080c06902919442034510904d05040320b00054803504001c1d00c4182c0341c0c48045020342540e030107a801100030b503420504694940c0d58901c0c2d9207410a6007401404019045d5004802803401d003244c1040079298400c0310764811940039581102c8240b0785424000d800e210728034000600d00d8007845410061089945c072402070b44c0c2142000800e440035820074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 440852338 1250 440851088 440851121
    0x109050d020123070207030b040c050303040b22030b1b071a270a11010323070207061407020d030c060c0201090c15020c04051902040f030212060708060103050606040305061009 77
    0x10803400175404201441034070381c003c0c01c07000143c860381840c100303010072a00090341510001401046d4495040090301c40807083c0ca0708a00d200341c40b80c84400800f100c603c0b00501d520b40394030204040d203220300034050b900035408981d00c2c20012030743c449090300e0100000f42c85102000d8810b1001d5500061100c402c0580540d003581c0c151000d032180c45a60719610507001c0c0558007817030068100c5038441c0e0490300d9112601d1490aa103400006610000d141050740c10b00b000d0320603148001a105c1c00786030182080002c81c2c81c1785d414900035409004108105c03c904808006120001d50005442441010003910040d800090352005600d0400001c4009402c40042c040d00812180c820590000301922004c0c0155400b083c903071a0903804045103488155101c03501400820007058400165046008480c021104c0108007001881d80d551648026114400050a0440082c406500a800182d08031201600041c81c09640e51941400c240b005e0b070b5060040306440c1010821540580605061070480460 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 440853588 1250 440852338 440852341
    0x50a02071101020f0c1306051305091b0d08070813080304050f300f0a0302060906060a030f0b1003060e030307080709050a05010809030d02130305070f1202040e0109050d020123 77
    0xe0039aa2031040c411403e10501240400d9130324050250087c8008040c00341482c4000c2c1c181e0099075004d0311007100c2e4040e091090f55070f0300c00100406000601d8015010305096201165515042c1c1c0c10b0b8400039041d41c10100c20003e001c1c1c08118041090010f000901c05140c83c0c5081208000e22a065440f4881c410681525034110481c5803c00d403844110646c03201015508041c40e00724201140500041024050450f024003410707004078509100700401004d480c400c1c0d03190ba04220030581140005030081075000134450006080243c00b9410070940c100e95206980d89640304000c1d0351403080b9801c010b4002009200b0f1054001d04980d4001c0c206040aa0728a410f01000c030340c608004c0e226041c100200200842c41c4044d05000f160010686a8415135541c1031240c4005c0d9034024034401121548644440025402000350044045d10045024650740c00c05640130840506090261100107550742c91030700d40042d0080241b190940410740003c100342d90441d8694042075a4040c80d1200c100d503400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 440854838 1250 440853588 440853613
    0x5031e04050a1a1506090f150403110909250b040b0703031a031b011e09060809030c07150e0406090c1716031d060f04300e04020904050a0207110102 65
    0xc844c80e04940d001d030380d102e4a030104180001c03c290750b0b074900e20381c03c040c0c1484401c10200e02d800080041d40d00545003600706004040900034244c0e0b040312440f00941010040060441444400403c90503440300c607070904035100c1c03c446005502030350041183c0036000500d02d080540502030308650503440f996204a603900c0001203902c410344800c1442180d8084c14000070243c0c069000903090404007002d0070b00c2002c40900140880d9002e00440022520500014215034070003c100d95071390241d00050714110340744c400c1544518001081c0390b824010b82140c03550598842d807055600625540c1c00103c0d6010003203801400006c4106059181c2d0040c1c101085882e4040518594109045140003da40300020f0900529151501d031140b542e4025032003480141142020241d014502500c27071141008101d090036001c0702441d03010654014966862019050300a0b4000d4401240203400586880c1d10300b8002411900700f11882030360658042654010300855200240d5460387c00c4c0002d03c90311080341c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 440856088 1250 440854838 440854861
    0x18081314040902180c0403080c01020307111b040c0c140114060d0c03020d030302070209040b0108060c0c2d0f100f0204030519020406030b040302062505090105031e04050a1a 76
    0x1102e2984e00c01240380c041002c46803a072040700d00460f04101c1c0c0c1a04c6040d1001070034040c3d4400d035111030010301400e06a48000c0320126803000c516804040114000f4071001c103101c090800c00305c510b81882a0107010002003a030301642d0103903001e80e00b070001541c61100415283d04c202c005c0c0010b0300884400c0c0c403080000f02c01c00c00610071340c1c1d0111060042c400d11850201e01038402c07004008d40204507070051004000d0b80c003500c1c6068986070010340d06156240e0030001d113140070f2525007420561106040b10b210340a0f0120f04520607248800100d0b141c08602900d92800c44954003940580d8030249600b0007018003803040060210380d50009500d820320b5602d0307180d075501803218a4a01b1380c000302d04103021581c8980c840f6005641c401001d102900d440d090103515490101c5000365252000003511802040a41c00301d000d0035011b0715038504209a000c0115483d8000900b606002401092880244d80d400041c042c440d41c442c400070640400030789001c00024070300c042079143e1034a05205014491164 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 440857338 1250 440856088 440856109
    0xb040e120417010905011d102c010b0a140306060a06090501080a09050d051b0106030c060516020a03050715020624010509090a061403031c18081314040902 68
    0xa00d800300a682c540080d0b0041c0070000000f01198a401d201c00a01001c4a40615284040a0075101c100001c40c1d41b210583d070403134511070f4020381000724420281850000382222a90000b0000900e00c8075040072074405241e641010b0501c0f092003a1300301503843c2c00c001059100c00140d03890b142e800e00c3d109018250350b42a0081d00e0503c40260700203950b00d24254001c406564010382110892000c001d00500654024a01480d9909204100d400c10900c14041c0c041241e9108600ba1602881c2c00703801c0f202508214280304510310300e4001640036954950080380030710300810180044c5031801c10002c00c2c4000001c0804159082601040100120104451444680d00b03040294251513070004031018403c000101d9808400701050208800ca00e6220340291003410f1003a0482204507001c01d41d0301c4c011400c02c4240d403440b854a106030001140c000320b40c2800f00c1c0c0034a103041c0800d9902c5101c0307a002030040f0940340c40c00078400c004400c00041c2580800c1e60559007000146815000301e807040e1f10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 440858588 1250 440857338 440857349
    0xd050705042d2f03072a060b0d02041a012703020d031416050d090305060a0e030f07081c060e06010c051204080c0301060509070503130303110d0b040e1204 68
    0xa6424050a020035003003030b6841400c020007145448580201e0390799a1503001952494002103880013419001c1500071b6000720f2445203810070205e494455552180500781c40e00c846900002c41528003030068496004501070f01e0000c603402d114121071030000501024440e0140a0f2644022031040c2c1962104c0e8580310a032601610b500484810604054548045c201c40d4602510000120414800305039440401070230710540a684c400405070070201c5219000f40409400742e00b02001050403400b41c4c0d40a001000c101b001031707901300000e020115142c2e410075a02a02c50340f4000a804a0319201e4070384038480c860b00440704120031428489040080740004269a042c01101140e100900500700503a0903402107d255450351282c484403c681c840b004c0d000d0003406903082160201d00e91800c138640340d02c40e0919a50b0316040d41e540e071a964000c0303152045d0503010726945024201c42103003090014005100191408180c400b03201052000300c400300c1b0850545a00700840b0a48d04040c2101120200ca0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 440859838 1250 440858588 440858591
    0x607030806220b0901060201020406050414120706021605041e241206050a0c2f03070309080d0e01080c0721020604031e050d1a0d050705042d 62
    0x1038600c1d020802c0b2010581c2c21086582c8411401c905240c020b40080020250070754068515990f107800c10f82c02d034091030190001150050105204c8400681b4001d041d0780c00040616441c03c40c100441c0b07040640b02d03081607006130040040700d41001004140007008103000d0f50200b05c06500b40030902d880d0203207c850ba1440c9078a5120305c8040002c02000f813401003400702030351300c100790703840180b28144030000c0021100d1908003800540050264440c0c82c401d046580c846401d140200590b1403e1420484180d580000f11810b0318119040100040c0c82e01c0ca10a4a404000906103034201d86040319000035201040307000c581d40012668028100e54010340d44010707098a800461403e662886000711400381040301c00058404610760009205001d03600075120503c801040c00b10710700e108540340005502040081003111712114031940061003160100403031002910902e00010312200c40030205843e1a8401c50381444a482d062184402c100c1c0031403541070740c001c403010f084419030406903542d00055 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 440861088 1250 440859838 440859841
    0xe0108070302030c0712030b01030c18061b0b0c03040201090b0a021203090f0604081809010e01030f080f07060603110303091302030a0b120708010b09090615031e060f060103050606070308 82
    0x1000311310141d0303610780d502c140f0006c12289041c40c02001043e5422002e40003138201003501c500c1c0d40c020301c0c6040b0892142c02c004410141024403c0e41e480e0a04510070740c03900b012040c2c64002c5140d9081d8640500c2182c2040d954904180c000141035070682d4201c141e58031020842101116000a002518441c81005c071b0798899440d03240880c2031011300700541001e801079100b000f0400c20340348000e010480840f446030400310341c4070082c80035060f001d018401020219000620100f401c1c002118540d5100e81c0030149040030310801311762250488a01254105d0b140c0300c0a00030050740800c202260384c010b900443c00d102041300029000000d40013812196a030001c04507400996a80000c1c0c0c1c1060080c140c0100342d00000c58184d5900400d104001030344d440d0070200180340c6004403506001d5828103004081c640c4480d0811300d90144204401941441050b41041030910340c03a131507500c440301110240209203030884200440b400020071a42c105403401041000702d5a44c1d40c29900c8440c1c05250100e0305 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 440862338 1250 440861088 440861101
    0x50106080a0b0f0d0506061f02070e0c0412150f02091003020f0c01230a06061d010e0a060f08060f061608070b040c05120c030606102c030601060e010807030203 70
    0x9805000c0f40407500940420710030414044000384450281c1019610b5200100340071100c00d1014020402d070380c0060b0401c0b001044204802400950040c0710b02c0829882c3c19541e0004440340054074204407031901181ba014518624548626a05c0e9061000c0540c503019101c000a100420701c3d000000615a001c2500d0304001400b405031a14081001c000b003000b0b1001c452008500c0f116990a0042e070740b00350001482800403805940b0440d0000c1d01d0340c2403c2062614104a140d408034610383c1080b04150140c1510790312016900c00508060f00c484691341081d0200030010b042c001c0000740030302404002e0b141c146c0c07a2202101c401e01003501031406203140b5440c2445207880b40300e20250409003540c0c140320030712100246410072176104851111480701c0410185495031000c103155035154001c040094070342c1c1401c06d80f401204102c0c2c5400100c03016240488001c03444502044011000c512107242000e0804001182c094802814072050304041a00020407000b80101240708054010004c9200d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 440863588 1250 440862338 440862349
    0x80405060c1b0f010b032e0e030d0609050910060b030103240203010b040f0617011403011103040501060f171f1e0f050a0207020f0f190303080403080109050106080a0b 73
    0x70062004003d59140784510300c0928081c3c810849014072034010407006034481a41e450905040f6900d440103020303c4200c5940000062107140d8400c0b0035030008010401c51310340248103601c06461111000501414182081c038a0074070a01d00030000b03240f030905d0a00290710301e00c3c04d50781100d41c8034011400000c1d180070024002078401203072400c400e00100001c030b85804202c2c040d005036403075444110401540c0b440c00b01c442c520f1081514461001010050061200c2803480005d8410040c2c004a6406202152404142c1c411075064039182d65805050084144c645211402050303903145842040c010368181c16203a02c60141d191034400c4502c50150904061500b04418110000d10043c10607510a1101009003c07810680e40060346054002462134aa5109075040140c020703058540c4185200144078290481c0a9070741d03480031030015034110b40c0d880c20f43c0d188003841c800d03600c8c0003083c01d081c50098a2814181c028000742e82c10400140a0325612003c126400039803644003058814603113000c9203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 440864838 1250 440863588 440863627
    0xb0904060806010605121021061b0c0510290328030f0206011406070503091c031b1a071e05131505090618060711040c080405060c 57
    0x240c0c1c5014081c00002c4064208020b0003482d428a2440e00c81591a2048602c0004c82070040d03215803841c003030309010411040806065602c1c404c610008034890092489414044010000800104841c0d14041080010301c4510f81c00762103030000340102500001e10b00c440300c80c51031840b07001003108170140348107950401500c2401c1600c01502888203019246030020200ea0751420340c04110518020314a0134030001d60305040361070510040784401c080e5410890240e0140e00151480e10091002d841c2d0b5642d5100e2250070300c0c0300380b44a50200003e41c500502482e40c84240e00700911020640d40c0c0214950b100c40400104000051b00701550300e1400541c0c1c1c81d0000707404000307404000c000302d0600300c0e040700081c003040e01c821407842c19065072445900b00d0700c44c0c8801c14800107001880390b0402800c0100281c1038148980508281c6042100c0200e44c841d08420001d03125110b071361007005014106889000300b400c0d001c0c98192098940b40d01c5055a9090191103100d4101c070015040140c2e1a040703a803013 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 440866088 1250 440864838 440864849
    0x906130c050a030629090a1a10090303020f150612010f1103091506061e04030f0c0906090209030601180b090f0912070b01060c02040216050105101e0b090406 69
    0x2c4541580b01c0c2400c4e001014905888403d80c2d4054000e562204440b0058504000001380540360543c0d40c0700c29400a0456a0440124001e5040340c0c3c0207540d45a1518400e02c200340d50314000d03240d255050007071402501025029040d0840882d00d0180044050069070184007615100000000c0034620360040045070306030301c4c00f14901200c6081c0c00c1d410fa00110701a042c08030444088914404210710300752410f0340c0c151760103501040011002031040e51044130150300d002420f800c040e540e4542c0b11400c017031640c0440301001075120a1004000360b10409c030152086040c11414103103030f500444d80e598018040d03030817003012090003004504180d400402c0c04400103040d41026040c0031481002e88801514090051300592021601c112510815207a01e40d400c2456010541d103040d509a90002580d54140e801907003c200c201040c01c40b4445081d0201d01c60400007030646004080c0f0f0900c2d0f0f50315001041d80482c6180e42d503000070440803101c2c040e203103d14074440d500e01074031002400038480c6a224 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 440867338 1250 440866088 440866099
    0x1303030e1309111504061b0f0b0a0504061103010510140f07080c01060b1606050601021518060a0b030a020402091c150c09210c080f0102090103140906130c05 69
    0x4070410095050000f5980f200c0c140c03003940e0714070720f40302d990000c0d8081e80c022000040d01c880c805096104401070b6004c044d83c000d0400998880c1c01d903c03444001e400c11151042c40c0e580f40c0d0288000c0017010b06c0b0b0701c40402c080313030300c59402c5504050014070102c9084020700c1c1001a0b2102c1c0e81035a965050032074924140071001a6a80d22481c54099501d8012585099a55213001800034034490444e046071054070071f414030881e2000d15170365248010b2101038001411407140481c0b213502c0d41d0300341c00c0990254030364020782c00b00c01c0e0411540c1351030b00b10014102e4000d40e04150b841e00c0703240c400107100d04445074121009600c446600c5c021807010f40e1401c918001c9005c150301da40061081c46103a261207641140828480040c2d0f0000545415965105148841d020303454030750030072000c60070343c8082d192282d0a05c8072500c0d0b507005800c0c5403288210000c00c20365030005111340c2568061080d00050504001d0074001480d001c83d83c00e45803203009002081c07035045040601e0800464040440241000401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 440868588 1250 440867338 440867351
    0x50a0f0e010902010207121a04150903031416120f0209061305031902100c0f0218100e0103081e040f0605040501111914010b0a080c151303030e13 64
    0x180e074007070300c5002c1c020303805030007440000701b80d410341003a41d8801c158005004101180300500320303c811900c0113205959541e04006020507031200ea010300e0150381d00075034004c9101940600d9840000a02078030f420550401c20b4140c52143d81c020b18014003e8890b420005135444c0941c5440004c0d101d00000b059210b04002142c064404951450f80c094400550481da0302c196072541c9000c01d001c5064019603c69200040d13400d07489d104480034501d5520400d4070768414441c50b40400c1080d2020f004030948000032034100f01300c808105d4507950052040c003001d45590751440c0c4a41c4424400c507034034080c503c203042548401003021a4100c030007c00300e400d040705e521640c400c00206103070028002c13980007549004480c0c4085000141410740c0e01d07010500c0519126241d0b84017074100d0504000c03c0040d540324904c1011aa540284c5c4e43c1c000c03e080c10103030090900301802c01444012007413030740d80040700c18001c090340d0822440c225001d891340342c28103a000c000760100084c0c19100400d81d000500b07041c0710 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 440869838 1250 440868588 440868611
    0x5060d08040e0a05010807060915140304050606030c0d02011d120607090f06030606020d030504030e040216050c010f081506070c14100806060904090c031202060403180308090103050a0f 81
    0x203030700b80d2298030003900c2000140d0300d610500341c0b10200c910403d030004e11701ea1001d204070010b042c40d10440c1c94141c180080400300c4000c4440b05500116006d80d50385d005041003225905052000f401c1a403401c0381e1a03010f01000d0b90011b0f020003804490615070f9071001803040c141340c82c3c41c41007100c0032030681d040f40c0e1503103400d9600420180403030040544401c0c900b8000203403d4003034002c0605880d1960060a03014245200031001000020025001c2040641e0401c074281c881d480102845c2c041c2101c030003000450380c10300500d4150a00b0000341000f007541c449401e6241d02403081c5030080b10880f0215180349030480083c01031300403908040c0018117000d5002588030244d00c04060880015110304400e840e16150a881c21003013125900d4100e802001213001c18945a449141e01601c1103955400c116141e484e45444640d05036090005a40701c10240710500d034118211040a941902c0d00031903050459a41e1111350050080f02c2d41415100c2c0040360001c50342d0b800ca0800d13451061420005809043c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 440871088 1250 440869838 440869859
    0x80c03030403090803030c04030305130510020c010e0a0e04080315101e0824060f12060910180216140c010909051005061b01020301030303050402180702060a05060d0804 74
    0x1540d04a0224044083c002002c2c40d002c816a441411340c40c1c80b1500307042c6151015201607004a50203c0380240c2054045803940c1e84480004491503958000c06501185600140480351460352103486401c1480382000840030400d0079691055000f6003090302ca0f1590740c00080054407039450194032001c9511240141e0b507004144504508880302894500c1310040c10990703420100303880c46014803070400e041c6001c403160840000c03030b02807010b007000307160228000800440d500007804016600311030340c0a100261a1151189400144e0703651030702c030340c1c0d4a00311202075003c5442c40c0441245401007503040c0c0c6040012001d6540681211013603401c0da025203031300d82d110031020390b540740411001c410100301200c892250398800c058041f810010b9900308400c20000e60448039903982900400826440428401c0c0013460082d8800d44000c569401c082c41007020120b186031005121805250030421344035400941e45800114003000081d8644039500418a0314400300d00c05420304000203400505507518 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 440872338 1250 440871088 440871091
    0x80f160b010e0405070e1b28050c0a0303050c0d0e010b040e0f19020409081602040b0402030f130804090c0804050c030f070b0a0216080c01030b0105032a07080c0303 72
    0x210108510350381c0751488020450390585020f4919030000304144a4450165445500104120030a08000603070002190346544800c52881c4c0510407100001040c4840c0d2264000074130890900d982400c0910012030f030b5480d88040003408050720b460110740141c07090421100c0120745008240b001860481c0c00e28043e01b0b588070320758080ca160003880c0d01c640d100480e45003040c06991026000c0d01421503180a003000c03c1e210180c0c2d0050356860700030009500f9000409408082981c1908544031500401080b11f80d002030050180380104104a0b00400c0e103035109600a1700f00f0100c1e009032445042580180c00303541c124040c1107240c00e100201103500711040720700c1988a60100d680d80d01c2a1000d064482d0001e4192480f198842c080038010403a410001e06001e41c10303481250a0f9480f6150100c0151225a01520054101d512403c40c0781d40d060203800811442801e0052440c01e04902d000c600004259520f189415100740302800088030358121110340750007607403580c0c483c840a44e8141e00e9510 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 440873588 1250 440872338 440872343
    0xc130b0408150105041505060915030708160504060e010c0c0905010b0909090304060e1e0405070f110c01080105100504032a14060f090f150a0e012109080f16 69
    0x8024000083c05d1920f8020030025034400480d81340002e2034001030041503000040681d510400c0254030303501c0b050a00d00558881d42c0655111a81c50901c1c801101c1c5414207919041c0401c40204010f0007000d40164019a43c3c00c020703e000c3c4820314141c10054225246d540150001500b01400080d4140d007110180110620441b04510740391603001c00d40d41d4034421841a103003c583c166024089920b0000707aa94449001143c041d054014002c000030103e410407110b170004580212941c403640c6d50b0142480a0801c00d42c40204050654140003800d0104140b1440740b05030031005444c01a1807059060710002d60b4020350a0941072031071180145105507450501030340704000f64000514600d039003000e44034000094075492038401d1058000a03194801144160403510900300041251214500c078102c542c04070070710070f4685042d50001410565000d81c5941000a410508542005107101d291840419040000f82e4614140b030705040c180100101202c000b86d0218480035400319000035100441d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 440874838 1250 440873588 440873623
    0xd03080601020d05040503060f19020a080118090309030b100f1403150f0a0902060c101a0118120501060e01060906030c05070f1b0b0a03151406030c130b0408 69
    0xf842240d0445070b41c000c03849103e62580c44140880c400d08214030b61190080c0c224036040100790001811141032764000c450183c0050b0407880108464110012540c12100710441d05000344011a10300900c04100740c000541440d90710000700340030341d1042c0d0301f8030010910600203000041d5103c00d040e504a440fa0543c9020703014902c1502302895404ca941ca208400c1c5025214490319034011a100a0a481c20101c2e000729080016420700f80c801c02c40307404003214072040481c81c980362032090000c201e803da00540c180508003805200c1c80c0310b0318580e24140e03842e88502e850f0070340680c181103014205507405800042040800800d650758050101d0742511031580b02440915101c05003181d950ac00d400001d041202034900c02c00004182c950745104208051403c48101c2da154584a146548180010703004255500781c2c104050f45204207100c02494118107452044900101081c145c0c80300030981c181c8010300180105d004400043d01a000e400404200350b280d5031500403065407140c010390400c0220 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 440876088 1250 440874838 440874853
    0x703360c050402070c120809060f030415061404320a0e03040b030c0a0e09011e0902030126120406080106080a090206182b0b0903030403020c01080606090d0308060102 73
    0xb402c06000310744803c1c1c0c0c8802d485003943e142110800f9103204501003161104010081100d41d580c83c0740142210070300000c40c082e60ba00706403504e040c0f06090102d050350000c0c18542c0800c041040c0344d455001e222826240896100041100070000c0c00e00303c10542c0304035001c6601c1501c0058503040c841c2c8148085541080350084440300555a8015071003090b4030080200002000700c0b00c00b80161240b0311850138031684064480001440c54074090b0070500601118004030000c049200b5000c20007003400c07000c00c40c40c0d54108501d4880da911510440140e44814404043e89644100241c00745010604021511207444d003000070b002103028414140014946070110f01e1100c01446a19241580244441d00d440e441c054490280c00c1d21654450340600885055900003441e400185401601d8221960706043d0500c0c0080209001030700700c40241d8402d108210000f030b0009205c1e02102401d0a221038a0394483d40003070b110344950000c198100c00d508840004041e04461041c0c0170340c90913001d46456 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 440877338 1250 440876088 440876099
    0x30c0201170108060103020609180108010203190603050606060c03040305010501150908010b22060f03050c011115060f0a030206071209140105030a05180f1507050f030703360c 77
    0x2824803e0040d00c0542c1c010304010001071078514018118010090507000408003020040b024001099104280300d940000c200301406801034880001080c0d98001007004500395140d05540f1400141014062400001c2580b96518200180c4009540c040005e200c00e40e16010a00c0384681002c0421021402110001c603544c0010f0140d1000498007030f2511480450b100408a81c0c241d2442078507113031075074420012a0382a40e0041c15805140598028480400503c000401003400d1020f07003125600515918854074092110150700f200f8100d9407000101440e40010b00c0c0365000303501c0207500c1100081c0040800c11188102c0d41002c8954442440d5540d58243c0980c5107c0c681403540e0020f40100001100c200003584901c1d0803003c41c0d02c0c5010300e8031907c625507207000809003e24660343d0050340242020000e10700c00c598045c8040c03800c182442142d140745009804007030f203020180768659502000c40d45800c0116060071000481c844240d00000c02031818103484414150341030810380740045074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 440878588 1250 440877338 440877377
    0x406140301030f0605070513060504080d0e01020601030f03030b1e1915120603080f03041e03050a03091a150909010507080402190b07030306080616081b0412030c0201 73
    0x40740d821403540e82034860f8644e6140300811000f0105030a2140500540200c1454110018003400c1e150315059034660410120510349504c40183da02044103810642045990105125046a41c0000cac0083d442101c0c0c60290054401e0b015041c0c0c200c1c190740c01c1c0181c002c07007030b0301d03000124681034550008940345400b40c0000411103019009507060b2080e20406160b100b2075010046a050880c0064000d032030f50741e81400744c1e00c02030f055100a1400704c20300c0140000d1030003056003921001100f411100003564080c040707029040c688400d0540d071341c010400b030104082d000444202030080d081c0f000c0ca03040320003f001c0c40d030008950340503ca60000103101c00c1c40522580d4080d040701c0e141c00c4a40d503103e50030082507030f08113207001028681e41d007030004115058202410300b00d03120341c60106038135060000c118a031074001000110014030a003030102c28180c00180068010440760b40303a9036029505d408400076840f40b54462500050303030880340018154040c00c80191540300341d9494608a050128a08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 440879838 1250 440878588 440878591
    0x24030b03070302150c0106090905060609070c1e060b030d030f061208300901060611061003110609150d0506090c2d070b0115020115210b04060204061403 67
    0x79008900c1355224201603600304040c000c5254802e00210b000e540340c030707604001e4503400c0034102d541c0c3d4801c1c1c06210003441c18180b05a8040702034a0080585d1010b07490310000300c421300074038150440880c0c0c0448103011403a0000b1030301c05c501408a40800c010b0490082c001c00316141048601d038901040030a6a800644000400c990006803041c1840c0011000400820398080c0402d8540882c200000c0030310140141c1e24824004440001344040c9044c40c081c00ca003800c05d4091455410480400902c41041c03450700c82529006100480c50351500400300f21baa10a100000c6c0d84240c50400925500c03007024020561190458000d116545131130b0180b1040300403c2d117448020400c2400b180381c40c40c03a405280311508650f401d80301e024200c44135a40206134040b035420f4981c008480014845801000780c800692003140c8020000c580407540d50000076001806040d40c20780400c19151001003030300d0710380b01015070171000c3c0010740e0030b00d4a0400b0082d40540b1803000411400105544104210020340713 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 440881088 1250 440879838 440879843
    0x2c010e03090616050a08070c0510051206011110020711060304171c050408090103050c09030a0f0f2103061202090a15320406030c170724030b030703 65
    0xd5080a01d000100151500414082c030031050954a1000200781d04010004000d4050b00c2c1c0ca5545011906040289600310342005004042101c02d210503960b0001c11a184980c1c048032410068075010f004903045440b03428031040507c04c4c1007031400c2c601140c0d030042c103010344500141030b0700e03500c0f140c00d00105000c2210094840c0760400e011405d100004401002d508082005200c1c03001c201c0b050300da080352400e6600fa6441d1502050000a0756050f200d2140c000e8030001c401c80c180343c2c0303c000299507140200300090562060131a40f02c04c1040060901609541c0408100240c202c810458016041c1b864401400241001c0d40041c4010064204c580d969401404281d02555001040d80c0940a21210000030046d0f42c0310014055079601d11080c0859821080780290010001c82101d20402540b182f070302c214609042040007981d20b001400480e58150380c200c01401c0000000c43c00c00a10f940710b081e01a500301c01d8455082c00006441403040d045403802c2048080380010325507900680d0000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 440882338 1250 440881088 440881093
    0xf010e0609071701020c01380a0504020a05210f0f0403021b010e03070f050f06030c030703110c070609030b07020a030e1507060f0605010809030304080d1a042c010e 72
    0x2404188142c1401a015102c0034001600c1c21515000c031a084405550722341289250b0030004000410b040ca011410100c040340001481488100019440f040944501c510039680011041180390141c401d0324100603100d001e00c000083c280454840341c80b022200644503616410004100c4504503000713600031038266000b010b840c030300005401e01039400d00700414184104c02c0d400085c95071302080991b01410000300c100344c0b424903000a1152080018507003030b00c503000520400c0b00500b822800c0e41c0d840507684c90040b9150362410050702092241e81c0d03040d41103000350706000c1501d6800450f28004c072445010945400d558004040341ca4000602005000900c083c11210f138a243c50989101e9546040b034069180a410750b603685c04413103e4114a0103241c1e00c1d80d078201700561b04610f8440c1d000d14000055803171403506655200c180c3c450309a041007843c4d80c1d0340b110340f045881845022540f08002e1320030070480000701c007114910420148248480d9030941c60030400c86106006505448880400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 440883588 1250 440882338 440882353
    0xf0109140904030c020306040507090f0905150c04030f20010305090c100e040e010e060105030a12080703110a021f060f030b0a0f1d0c01081e0604110c0f010e0609 71
    0x401100c4032020344242c3c10000704a40c180b02503174081c00310300c2c01148100000c1c40101d1030843d03003900340c6242d50356000da01c501c0c0041c5400415008646195180d5a50810a1955031142038070355a902582e00080e0400b40889050343c2040b02400c1500c240112242c0a0b0101c03105181c0114161041120041c3c02c58018a4032504642019020000117030035509203c2d60460001c80424110741000c0f2242d205c030307034403000903042000081c0001405000290003801d46000ca41d261149540c203240c04240420600d5000501c1c45813103540f001c604456200c048031394079254900025601e2108510f00c1c4500c001d064010200c49180d4070030300303089900001d15003428518684403520401d000502125200c2e490320501d080144a038401c0c81d00c0714000607500803d4000050b031036071034000b151003001e051094501c2070040c020011690655aa00b4003072550400c0c2c0d883d50081006001c030948040340d126004600d500d055400410515000c0014000800c41c1c00f184012455a40030246e4645015401070349 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 440884838 1250 440883588 440883629
    0x60506180406090e0307140703080403170d0603060905100506030c10030e06040302011b0908070504020f0903060403120e03070b0106080621060609070f080a02090d02150301050f0109 80
    0xc03804686904001c20009201e0755030014002944c041e00e03481c0840350400680d140c100311680004044030700d040c07002040050304580c0e9082c464417aa01018001b40010207403604601c01e401c0c00c642110030440014000e10313030b680c900302028180740d43c0d0480f814060040504e040483d9032058a11030a002001003444c190030b14140b1105c84080a41002050340b145100d0318201000c002407405544640d00004651241002d0603001703d002101510400c5601501040040340014a100a8a000321001039403810024124001881241e5909405000b000c3c02c101c14941c20144000156602100c1408458043c04650340c9a01c00c50304018640c607241001803040d5885442400d6100d1f42c040d01d03054615044a60340107a054078014100d505500c140100223090900b288010b4000c011403e0240090090181c041c1c0f100d880145490a071aa000c07803131a00a075100c60004003d0790f005400780b0a03800307101d214195203900900403640605950240e000b215489180308034100c665211500107000c6100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 440886088 1250 440884838 440884867
    0x906080c0708070b040b09030f030a0c090302130b090a02090102071203030624021b010f0806191715070503070809070323010606020d051b070f06170604060506 70
    0x280205800c690140310300400540100020803680d409445242c1c003a1600d8905041e0340c41005041d051a1b800034885800c0805040d02a01c1d00180340070000300700070803200005c5411140903800658020000f904080344201164010f2688201c1600c0d034002603911001e0142c20391185119443c010b07442135a0800146076003070013074402c0c0341c42450045040c43c0e544813000e10030b11841c0d859010201c2d80c01000710f10107404210342c05244519403010404524100300280140021380e00f200300b403100c51800030382284da40c200652240000100c0c0448a030b41c4613003418000c000044180350741c9206404842c10105918280b0920900b0b1640d1994070310740e00d0740c03c2114021005090305106208000000c07001417080034814010f041d01262104240d68441c502600f59185030303111209640003182c51a0702182d1002c2220040f4211944c4014410307080045c540c40c1505a0340142d450010101010482542c05020b400e035280d074007408811583c80c1c1104101c101c6000c0c1c451541c2c406d004001001403c45c0381e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 440887338 1250 440886088 440886091
    0x90a06020303070c110d2117060a0608090a0203011506080c0712050d020903030304290c030703020a020a060c1e0302040b0403020d06090506040b1f050f0607050a050a0c1410090608 79
    0x181c1b8203007242c001c9a071a406035410081c5c1d000390400508042e0302c4c40b04d500c031340e14506c4400c00e840c1000c070707074102200401c41d2291309005007404c20103c5d100007815010708103c034032001036000d0020044076924603011340e00782c0082e0040d280060003d502280440610000750392015800440310000701030082c1069072280c0c000029680740715020301000c200340d0380c144040c42c0302e14040d903510134813507603440342810a5400c2c0c0c0722101040d50420b028440f040c40000d0541e40e22075468240140d6030002d4070b0082c0d00d4880001802041141081e03028a4625404070135150002201505c92030301044910054050340101d001d401441a0148410030140c9009035152407054002c42d00018000401c0d217416041c0802140e05503240d104400900824441a0704018045c047d458510076000741003400042c0441080001e45101d0203000c40e074001404800d00001d040315501c10106c4182071501e280c04d0640e20094800c0001d8011340246031200c1e4100004021803008043e17132492542414004180c070041070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 440888588 1250 440887338 440887373
    0x103050f01141c0606170a0c14040f020403080403110a03030c02061b0d020c031603020307050405091c0806030d0c03020a0204050702030f0409060806420411090a06020303070c 77
    0xf82c01d0101c81d000f980b00e58048a41d03030040e4030100c0c8031400c0c02c138401c00d0b440d54000000c00f55406801403501040700014441c058070461000e81d880440d82c1c40000c0e0140c6681c00d44029960702c002800000c1064510003402101c0c4a40d0800c10102d010390100900b8148511010300841d40c0c50804c000146060401003002100d06403180c0710070001710014501e00b8042e24008000740c0e004030510380b00ca24040000400d010004202d40021500355404a6100c2c10680304150049403500d02091012109208010300c8407041041c0a921038000c140007880080c098822038041c1c02001582550507201e0b10320440201c0c0c150f001404034141e41e50a010007410010509801c40c0001d010141504101c00001c20007031000000204603c0c0c103018115040050181c1109100d00e0081c29850b134107281650030040481c48141022850b01107101c800240c100c16130409584a8940b8400068642f0204041c3c43c8141090b80c4040985841300001d030707501c1c4400e031444030208040210030800104030340448568000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 440889838 1250 440888588 440888599
    0xc0705070311010c0c030f031205100b07050102090d0507091404020a03110a0801060618150905060a030204050306040f11010905091305150108010e19020d120c150213050103050f0114 80
    0xb0080e4980c5c049003021a041150411200c418034004e0580c407901070702c148040e0348410425030400e0702c03105140000c50b2041c4059060b001c41d180c0c0a1000039816500c4103130001d0150794540c101880d201d52122014000c0905062401030300011101320408214421a4090400501c01e4110f403102c1884610b400075207644440104008961048280680c5c00185225101c48000c4d41c1042040d2090300541d802c80780c5005402c20703c9041c1c60741c3c08120351044420980c0c3c0c19a9030020000c00b20080c0c8034541202c0e402d4403940b014041040303da901242c2c13165001e003030900b41c184450300c01103a00820a10842c4e51002084000c03a030031038240514540d6051080007221048140701c1102035200e00241e11480099550b0208080e08580601c10820100c900b101e111030050000d90000d0701e05840008080d000040030b580c00885d0a00991941c0021034102d64251807400c2e07041c090002039446120360b803901545000c40011954001d00030180200f02c4860304d480f180c2c1c00c0c03502034902e12403925061036000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 440891088 1250 440889838 440889857
    0x120f010810020f181f02010c110c1806010c1703010303030b10141b0109080306010806010809031207110307150608030a12020f0f0d020d060e0435130305060c070507031101 75
    0xd05c20344000341d08070344940011031465a200c5002e483e050002110182581081840300f0311556551404201c8181c3c84c01c07503403159151100100c1d02510070341c60087c05400d003240314212100c9800040c5040b81d00c03d580c148035241c0c058040c41000074102c06110041116040000c01070002400a1720740071100320580442d080c6403402c800d0940e01410400c0d03955800001c280316143d644900401c3d4444000e0800300880e0501400d82c036905e1161982103403c0d0001500403520161144e51005c503040240070880ba1038141070b0600ca201050340c10361420b1050b18000e000100c001c404000c0d42c0712400d26445a041190340d035580700c1c002c1d501000c104851b0410410200841911a41c0034016400207101c005071600f0101100300704503084e940260841540400c01c210000b80480030484030008040d140f282003005802074880c801108000390b561114000c100f042940c1618038041007184e0080b8126401c1e0384030840103015911034100054880d4101c100184041511081903000d4400c0626150319030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 440892338 1250 440891088 440891119
    0x1006060e0f0f0a0f0e010906031a10050a080d17060a030219090203010f0306050603011a01110703080f1c0614091b04120614060102031806120f010810020f18 69
    0x3d50901d8100c0c0c0c140120300b8001740051400d07810b11034003502c040141000481d007152a040d5030f0070b032003440d0b500d002b00c85000041c2c3e102c804005110018540500118884e9072106106034450105560300b00000741c0341ca801c01d07850b020300c540507070050303802400f14100e260440d024000c115100040b664001e0310314038800240103d2910040d03000745510305101c00c0040c00c44c40c181c0705456005d000d01e44240e0400300805240c0d1038024050302004800d003800060042162201410715400364405001c0320b0010841890340160b14005120310103049080d10641f80d8554541c0044030308a016007250010712111071070703450030300c800c0b5030f90060000088241d085a4403080e01e20340354016000500c500d441c228092080080c2402080d081343c0b00031038900038501e000c80c0001c0d030b40e001384001c6100c3d480c0c12088440712030b00c1c1c1d41c0c111944819421802c141034a440c0040000741c2d1002c0c4219a0ba6104254003400250010301c02c0d100d003802c1c211801864001c2c0c9803013403141541c049199039881070541e001e4400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 440893588 1250 440892338 440892349
    0xc030302041805010303091703270d0302010b0420040b07140a050a06050108150606030a0e0a060e160303050a030b01030605040f0b0108070516061109030d020109051006060e0f0f 78
    0x90001c402c01d0119466041d0318000740904480d031300403400203010b040c01c50144440031044c0c0b80802d4150b0f40560307009001100c1099200810401c06411503582e400203000d055042d0080e00414209440034012820300748a01407200400d580c00300644d1400340301c1070105150700002009454000c2080c0311049424644040c01d01e491903004946a07404a4a4041084494019640104140000741c058058116406e40c80d01400a140038440c410001c0040c03031401265001050000f02c030421201b0b0f080003441e0003070080641d000d508446100305070812200c2038420b00380f02d041c0d9900d6996a41440c1c111401074001d418441090350501d9240e540c0400c01c1c0e2501d2044c00f5003040d421101188401d6648005007080002400c94000c118040202550110b40d454070790343c85c81d60000340011001407001c1842904d00442c1c100941c1401540507000e6280e905401c45c41c2200d004009a034001e076855041c031400c8508511640000c566051150402803400011407c140c4c80302031300d62401e0500ca40c00185 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 440894838 1250 440893588 440893619
    0xf030504031416060503010501050901120e031602040f0b010c060c0917210901021f230a0605010305040b0a0504030207350a0506012313061706010e01060c03030204 72
    0xb0196484240300007415102c8a00020080030113003080c6155504140000f0100e00c034035040300f414483d40c072060240101e80d0f42d000c0711000d40032105694581c21580001070210b601303441c06a120394200a1114244180751240440d00c64058554a40c841480c2c0e8800e00600118404003007072204441000540a05d101e200c00d004d0a8810041c00350035032500c40000a900c06420170251030413041c0421078013640c000910040500c0321602c8076411042140920000c2d0014050004c044020460307801c200102d014071031801080103180a108181c1c0350001101240d0b0f0846015080c200d040010a9180c59254881c079040b0340240b058650003900c50780500729600c0c44d4082c2160050b4a0105461202000315010748000d1000740034204030130303040c0c9445039a941d0600804042000c0c0d95508600045400032418903c680981f4081540e50349644400080c0907500c0350568209075030403044501d040100b1894140c802990000a0036420450200c5480381c0e91a0228203159080001048400703980e01da50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 440896088 1250 440894838 440894873
    0x403030309020103050a0510260d0512090a030c02061602040c080108160806040b19060603051b091003020a0215010f051914061e130e010b090d0f03050403 68
    0x803070044024800141202c1d8014401c01c64180b612041c05900411100544200d8000703043d682c1142107024021410b484801d800c0034054410b80e110340d4103698208015003540d01a4401c1c00050f40e1b50320200c242c03160000400200040d04941000c0c0040c41c003c000b81071080c083c1f07030440b414020150f0105045a507020007410221301898010841d07901c0400c0030500601c43c0e0070551204520740130a0f140d48140207080100103450b590000b4840916908030a0041c08108806009055550f00080c004110540c0c1990102a0940300e5401c1c003000c4104440e1554005883d107041440350340402c8000b0341050054000314061100804402c0d240e41003198080e10700201100546480c08007009031180050b040c2d41d035110300c44801000300080300d2030128540c00054a5091b503407c1d000348924180c60680f0102801c0701d0011400d0040d40560308220425980d102034501c80c03d9803180c50000e21400f4011780c0992201004182500142001d41c0045805100b0f09100313040640b00d036600c003003032956092003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 440897338 1250 440896088 440896091
    0x90d0f0602220b07020306042d0b2410030902010905310510360c0f0311090d020d08031612020a0f0e031204121a091f020f04030303 58
    0x2c0e04407140e01040400c0041450614013841d14980740c0c0402c1d00c44000510140010301c00c104040e100c80c2c0c41080140303810030450b4035000e102d030180c544001655402d80e010110040c01c1e5114622088005801c0b82a80400030100611702c2180a0b04401421600d07204038100304120380002200d4840364100c02160210341d001901d0752000442e007402264440303061008003420b20007803047c066080c10800055a404c00200c1a802c40f03080c60b4201d420103803640700f8043c8449440b01441031000c5501c0b0100c4100140e843c81100c444200c802c4050b100200441807480c1001c20000340c182c80c150700040d94051000c0c20300f08a204007501c51a841d074100f15580324090465400708035483c2c1c0d015a28010082c2030b8070381141002c072a19001010b821a607030300341051282c001d4001946035002c0101001800c0594900765443c0d48a8000001c0307248500411a1584514013007003500307a04003102140b14103082c00060005102080402c020300c0311101c040c14241d5820040120301c039291034014030285000c0d490 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 440898588 1250 440897338 440897377
    0x50f010c0c1104060308070b100806190e0a0c0b09150d05071812080d021603110d08090d0302030709090c0203030609160c02130204050d11090c0c03090d0f0602 70
    0x1840c502911030686180e103e0b034500501400001c0010050350000fa8010701c1e8249690358038a00c0d600b540c11150061010b0384200010000d50744801444220701e88002d5005100b020160700711181c1d00d264a50f40180700c105084018000c1381030303805c0940710b1300c40700034881083c0114040503034005901803016036201b5a1580c00f0841c0003608100c0182c00d80b030b2541d50b00002a40b90009109100a001070010b001840000b4200c0903c11240c066a000050500110610149a140140101c2c0f100c0c040400140035030b88000782124010141948221950405003c0321170300d1420460080d4002003002c0d0034004690400700700303521203104180001c5a144c0055640c0c0c03d04804002c00d84400a140e401003010a0303400c0d11946500c040502c100135030565028a401d0f01c808044070203809190030154203c3c1e04041c1040a0085040050b00d042c242235507020043d403600c0504852070320a10811103200d0b0300c104408902030405062081140f8010321000501042c00d40d2041c00313981c8941402c074004400e80c1c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 440899838 1250 440898588 440898593
    0x190318051536090604020f0c1023130201110d090e0c0406051e0c0d170a0b0a0612090b0f040311070501020703080309030f030106050319050c0403060504050f010c0c 72
    0xc2d0b200803800c1c2c0d0414045070076a0003800d0007500707a194500340703801a5000301c08120252181c2e01600d405c101405600d50f2900d00c64000a952030000d4030403001c0d400c0c208240a060040303071140700c5442107031558542c5466510102075605401085200701d0401c9072010700e01e86100800c1c025a40618035507500d43c401d151a05034949a86400a00800e03801e1404110401c485600402100d141d0744240e00301c0110a284400024440c0c011211103000d62301600c00100303412580080441c80c0b10000d00051a09621013030040b20840d805c2c001042e0700181c4404c0240b01c800e029048190701280344c0758000c10011461384e15101c000c3c000341d82c040a0629072909101c00c00d6041034005820320f0701d00d0003c0c08040d14000c0001d40d07600b82c520000c3c1c1640800004070308000003c0c070484900f0182400d10a5803544d40715001440e540c021502c650f81e004403d001d464003240c15015450094510405540c145411034841c1c0c002010040d00488051103114180e0408040c20702035264480103648a00c0d1111a650 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 440901088 1250 440899838 440899867
    0x30803040b04060606020c0105430512250f0f14061e13051204030f0201090902090102031c0b0a0305100c030b09130c0b040915081903180515 62
    0x40d0005c00954100e0030700c0407190b9070b100e403d81e1145c00851131500d440002e00d040c5a210800069181c80305041c40e81c0b186a402814034491144441c4a0005c1720313241c2c9a030f082091550b014424406c0ea409155104400410b400c2a008400300c03401070514100b00c5c1015030391001c075916aa10111b4aa241002100d07890200178041c2c00d62001519982d40500e0000b99082d45070300318020101303d80500c0d08005003040c40001c10040c411141c941c9041a6100d4490402c041921348040c3c0480c0043c544041c082114000d500903181c4014068000358203114160301000301310209542c1003040c1641d9030b00021103581d80c910700d4038015070141d07026001e2142000155000d8484004d0010141030406175104102d0f260401141da1101c64500021040c04c0b0624001d05098180c2d80280d0b078910010901146012241d48080780c0c0150411700c6840c010390b60000d0a403160641e104e010320b2911465440300119005a1802c450f0701d003410426850f40c0d48400000d05010026800c1c0009040d0100380301022000d803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 440902338 1250 440901088 440901101
    0x30b13150315050f0a0c090f030506010e0106050c07090c110a0c0501030e1603080307140406181202030c0f040f1e0c0e03032704020a020c09010e1909050304030803040b0406 76
    0x141c00e020b44c0c81c00141c9034100e010090718210220b541c50b0140c400041c45020703a0b8001d021040241c1c189560341c0d041c0542d4462007030042109104607400001044c6004401304d87c60f03100c40b20301a0031500e250121600c010002c0a9400041c0003040c0d9020880000510840051a01c2274a040e0b801504041c0010304071414041035140f503500c0480100450300c0c801411b0802c4a0780102c0703555880c0c0d0b480f0405c90390000500c801c0808203030041030100c0c01c56084100410030080e20b03520351603540c1c1e548401500c1c00c82004406905070b0030440003503509013802003210055460141c80801c442d048141d51408403140e071245051f51748441807030007407241540e0060103030401c040c4c50031000c01c28000000030b0700c030311440c4200703501ca070307400580c5072442d01803050201b060160003441191686d094910181d2110318100f855031081100c40d0000c1000080c40422600403060748400860308030400f008600208008a0151007500c4103110010014009000a521030b42c0710760002c0d00c5074100b0b486e242c01a2001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 440903588 1250 440902338 440902373
    0x160606050a0b0708030c09040504230304030c05060318160e0c030114010507051009080301030b2a07030215040f150b06070623091f0e070501030b131503 67
    0x44640081102c055501c050303951103508130307000310f03a40c0d1580c0c10a49590303c60200c0e40c2c0d030424200000c000a102010000c0801941c081c1d005403803e4200524041c0c40e407041c0d00004104203003048040c032840c20440e001c2c5a008503039409031051420314107030741c0e440d16034000c0d649a0303000d011401c18000d40384000d1480c0d8005007030680c0c0301e003554103000044004006560089041100225400d4280041044002d8070fa0404603410006003030541082d0703240e68401d0005880301e01e0101e002c242c450005102845101454448480740c000002d940d088441c2d03c0010280c0451261284e0040c0c0f10440c11880c0d4040c40c03040b0301c1404c01501d00c0c500510150001a074407007049181007005122522468200c0310106d601817000680403d070042d484401446041404101d40311150400c03140d0440001c82620f80664070155072a0040342001d40c005032800051054540e400102c41005954003035007051410450081501c04038030190070082c021568a00d001e40d440d07106215040051081c0007401c00c00c40803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 440904838 1250 440903588 440903599
    0x50a030507230a1d102f0c010e0105070209072303090d09060207060f08041514060a09110d110f0703090302090703050f0f06040b06270f030d050a02011116060605 71
    0x4984000129071805c040071200074060586840340d0550410304250304120f0b2480c0349000c800c0189101c0d503a0351205040203502007280c00f0b520050960168095500059005045030000d0f6580383c0220f943c8054014111800d078800c2c816940e100c811074014510885144c002041c01e00481d000040c402c040650020066401c0013030140b10241e07003c1d41501079070b01c050609140f5611280741c21303100c2011341001600030034507202000042000919155000700340c200c41c407801007919402210300f100c2d541002114451010041100c151013250091700d564000d0242039400c00c410900c09101540c4495000c40025464480038011442c2105096800034a940b07400c101a15041c0340014298001034031b46560020450b00003000e941e82c40c0c00074424640e01504143e03d070325038595500c00c101184815450056862105049a820108400003020200400030054400f4405040d0b80c65448111602c0441d500e03410342c80003100644006003401c1c80f9140a034000804641041070444845421092089 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 440906088 1250 440904838 440904887
    0xc24071b0618211208041a1314030417030d0f021201050d05011104091d0c010c0213090203061602060a0c1d0a0504060b090a080d050a030507230a 64
    0x4407100c1040b064400390002140c0c000c580d039002c000d100b241e04400a0040c3c541e107544c0c440c8964003590b414000c9204910681081d11008100103212008036030508032a0005003500000c21018119000c03440c02010030740380307841d0729010525101c00c0c0d00104604158000560407050f0f0600c0d00c42c0d16030000c0e07003e00c01c6040c00c40d07031800319060440620403240300c1d10300075815805019080d40000100340b01203004d26611a601c401d504080d006c1311500074010b401c600c00d01002d070346010642e1803007100140d4810103130441a03804c210440c1c0031050424080c903520b0640c1d1006032030410400d03000e1181620300c81042810010002d242480041004000c0c5003019207500f9003d40190401d2030080703069440c0080028103101140c0322490340d81c80141c2c45803c0c5880000c500e00c0100050028403025a2184441611011459510811210803500040742040880340c00c030312907071040f03030440c40c585804c40000c5484000c180c120043d002e100c0004090008503011402d8000800540c100011600b01044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 440907338 1250 440906088 440906117
    0x705061b03091c050c07060e030c030613020121020304061401060e0a0501080c090a030809010201060b03010e1504060b1210060c03021506031606020607080a0902030c24071b06 77
    0x1903c010180b992601002c1c0f9864400960003002a43c4103040c900d41150200d61350340c04014030302100855458001d01940c01c206c111420042100340c881d40005a00c007103001c500358011510f81030784c0362100071418107501309204002c060b80002d5005038068800858a455550410441d001e0180c1c0703d503040c0003201034040c0e80c54980c1003003241101c1c03090805103117680c0e42210740d622030b00c5084c0140d0b070b118400e10800320030042070001520300001c0a80c0200b2110340c030340c1092a2240700c00c1c00783c00d0a0049070b00010384032440f0824a100d00c00c00141c40495029a24803032654103402c40207031146550081010001501000d00200d0000d116915000c50f85420640f8040d4035220713a402090002d00c640350015003d80c808000050300c0c10b0142d642c0c079004a0361004005e40741d90058495034000384403840401e11003c447c3c0a22a203240d002000785c07e0380080b400400c040c40602d500c0d6249038069030074a0f0500320300e861006d080218000c0c0140c404001c0318450802403a89075401000c00e1207102a0a01507 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 440908588 1250 440907338 440907343
    0x3110a0503060708100504090c080f0c01050d0b06120a0b1f0f030e120c0706030609090c0509040203010609180204050f040b040308070c02130608060717070f0905060705061b0309 78
    0x3008070003804c2a40b05034840409881d401c500641000c1c1e04682007000d074100300000c0c4010780e0211b4810100f80c0394501015200baa0303c0e40f805e03041a600281091200d242040c3c0e05600c0030780f20000040000b4a09281140c07030b440d6650045032541d445d180d0760058000745040585d112904c80c2c00f0042c011320952094000a0180c001c482980001c1642e901c01e242c50258040210082c0c2920700460262503800420803d65540410700841c4d00090610200161032565070103180200b580c0710783d41c580c68504103801d004141100501c1603925649452000036040d21910960325041a81e620641b100003050040c081581c0020381540e8943e001c80f01007001148800c91004e41165151408071100d40390144201d03000a001d07132000c0d40c0b0410304450031038040c00b2a4000d40440340c048040c0c2c0d09030f40c1c500400380c0e240d01c10b500c00c040202000d0b0f000246180d1049190680000e01410207044c45616540402c0320b5402800e41200c550380054103110b5521400c00420107580136201100e03181d4a030011030240c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 440909838 1250 440908588 440908591
    0x180603240b04210209042a030f03050c03220f05090f0406090c0b0c03040510050909041104090c0b040501230901050307120504060b10030908340c03110a050306 70
    0x4205030800d07409401c0d0650500c0a14003015002804a40c546c20a410a000701d41030b4814480d40302c9221146042c03240c4ca1407002c03003003141d03040400714803010a19181900c85034845020030195001c10840204040900d00695801c00d41101c800008242044540c0d8508800d0760029403150b5140801c07c0121001c1c40085030340310f43d10000224069105180002220402e40c008090f44a004161420440e00010103070088a00c02c558129400c061035000351464402d281c8145d40241051000a004c03031a0b42144111105002c2d10000d00c11400e512084030699043d00f140c0c4050800280401480d80d105441c030324061145c1c58090040d0300820002c49007032080d444504e05003c008000907050714080d20600300c2c0a220070f5414006450513181c00c000038284100c4031441140031004e100e20b4144a417040354962a031002c0b03518503001d10b40606c4441c124080e00501349541d02c4030408161070b01c1211115110074410325140f24031a05524003e00030350030803030300a40109441081080071b0390300050103e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 440911088 1250 440909838 440909849
    0x24230d0f1502270402040305030d0e060705030915060f030a030306031a130f020102070e0f04050d1d240720031203061e040e030a0806030a0f030f180603240b04 70
    0x80c0d14803c000340210300030b40100d92010340603001c04101100b01600640055100103ca51706541d4940e40e12441942c1c0b600041d0b070402c2442d40210500f92621001c44071454208070010195000500070b60002494209030240440c0007a44500d410010040c0324402003401f000e036101550a980b0308142c0e4041500103121001d0031039000e402500b019a4000e0190002038540c422103030421f807402c10840b401e595029a01252140b00d0000d600c100741e41300f0507210149640212005014140e10003c110354003104900202c4e030039081e0700d04100d404050340c009250151061a502002c0603008500c1c500c007080c0c40d1400c40c0650001c4d0020b144403161081101d0b405041103890761507010780c0811403044aa03219142c1d941180c6004d140e81c20b1000b000000e4000c1c0d40d0345548421003683d03090181521b9544070312008084510030244031002078010cc4100b400c40d0454030f4841c0e1a1040c0c0742e100490041c3c1d5174021400301c1d94800c8070710000d02c50552a0a546000c900c0e6809003d840d000d42540a0310861040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 440912338 1250 440911088 440911147
    0x5011a120f0c28060327030e130605030a030c050f03070b0c03070309020a0e061905100e01020a15270b070f02071d0a24230d0f1502 58
    0x1480c85280e00c00e807031100320f5110f162440e0a51508800740050052180c80c01e065283ca42c2c100c82c142d1084003038008502d9040da1202c0b4040402c0c411301c8400d020b50344c504c188141d15204003003243e031020480e02010390301a0b82c501e02078042c40e04106050001e042c20011542c1c204204c140081360b0000c40554006403184600f580c0c030b03550358004500525400744000e504c6003101300700040c1300055600203070040c0b404403001d011042c4000c41e12000b81e140740c440c20b600400c015103c8201540248181c00c0c182c10107005032402c512155582d10070b403490343c90540050503a40c0d600c403055520b00840000098045091800c800602c0d91550542c1031001170646080000701c0c000400858400d0004100400c0120303004031544003032146040621070100c0c2c40d440550304e0302c5050007e03031001200740c158400710303402c06015480c20700300301284d9030b00d510ba030014444262403012901e580f9102c03641c0303840038020220444015001d00d000c3e816440c0c040100c5041074014021104802440900c9500301141100c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 440913588 1250 440912338 440912359
    0x10b0a050a110609010e01050603011a0411120103140d1b02040c110a0506060310060302060409050406090c09090210051e0306030f3003100b090d05011a120f0c 70
    0x104030381440e0302e10a406514000c03101803200c00d00c1c1c150031526140c0e9600000384102e95401c01810b007241d034403840c48181122604480e101c2030510f64480c0c0443c5049450192410074810081ca002e080700380d200f1a03028004e0401110a10302c00c0c004050824101d10b041c46442a03200c078121010030b41e840c030203440307190b40d40c0c1480300040c081c0d82c030013008200000680c1c90281483c100241c64140c100c41c03881c00780c06030481c1030000140c00d01c1400c1c1a00c0d401401941402c2c01e00c08004010100107004840c1c5a607164845400300c1e502500d0b40004000c079850204034045c5501c103110f2414020103100d01403000620170350070f03070700400384e640b05103281c04845036a1650b54280010745417074107000b2269035900030004040c0900c9900007a1a40c80b0a80c41c0b003144143c5110324508400f0721044920313011a95100409006190480008003a0070000815540c0d5000c4141c40c2c0c02e0840344480f10782010246100c004041c02d00304484500d40909080d03001d803030140315000c105500d5008000c00544180c85118 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 440914838 1250 440913588 440913607
    0x61e05090703031b15180b07020a20060f1303051603051506150705030d0212160810050f03010f06080c0406080a26160309090f0507090603150b0f12010e010b0a05 71
    0x3840401d030b1b141c1041c01c004039400c1c1560302a45855032003500f0f41d010540410702000c0c4d426180d0040a42c1c41002e80201d2900140d03d8000c04030307800000074032140401d184400400324200b0007140c1328100d04030f441c0c840c00918510b0200e00e4810101010044c280042040003030740d0390358520821a240d040c003c16540c42c0150314026045104011400380440e20100b280b0300841c4200c82460b00c02c64507007061001e4000d09500960f00600e0803034024403041d5428800f03000754141030700308510000c0060004100c0005c440b8180c801d81c2e200340c222a03a01c2d488940380c01d50516043c0281d10007002d1f24805070101c0326194640c02801e4034516141407268045a00e1030841480500444100d503000380d40e009000500d03460006c040c04c1d40c2e4843c035100d060804095000307155051007100d004401c00e0b111410801d2401c83d09401a24101c3c00c0403040311412500040c03520404401051042414400705070348a411000482403190181c101501100b00440144000c202d5071044528071001c07428a5515640e010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 440916088 1250 440914838 440914871
    0x90b030907030803011404060501020f0c0f0d151b0309020609040c0e061c0c03140402121609090c1502030406030b0402070c1508070e01020703061e05090703031b15 72
    0x42c0d200611210300000005034806840050480e402803c031818031201d540d4600490381c1d95070005003078540c0d420900c1e40981c2882c00841000e50350001801861000f203040c1c8801031441c0352700400340c5c000764452907408040003410b0000f4001e04030b941001c0048034026000309074240101150380c2d00690343c13070803a4582a40542c21618018070000c0032a50b6a51109011541ca0103010040c1401b0070b0034980c2404049010740980b4842401a5103c150b103035440d1f408204a64440010501280c000c0803403003250640c012100d640981240503021650000c985080054010341e5800200d00c4a4402c211581d048e9010089400700d80795460b0100b1008a42070008000f880760501c002c082d9110800006075413500840940c01d140d00940b180201c0c0e56034400140d6141041503101c074016008200d0910004280354810740e00c03444a9581c08656400001d040340803144141c1300d68485521406040042560114062030b04181c1b002080351000400c3d507640c074240b46040800741e180d54a640802c007070b41289 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 440917338 1250 440916088 440916103
    0xa0906180f060504060206130b04030c020f09010f05010809070305030301060c2907180e011a0c060403020601080609070506070311030d1515050c100513140616030c090b0309 76
    0x64240504560340d814040c205600511451001d80503081c00540100c2c07000720308d88401e640007004490b40380d03610b03641128180c86422040747d1180725040c1040f895200c042c0013601070407943c202c90703100a081c08005081c1841c02029070002e984406003c1c40051404001d5a0441c0d1036402c0141d8241200c1c5807c034180700030b00c251440c0e0300c041002d4080507203040c01c895900031403441c0c0780d40d0024030141510400e420301a0280070510800640104001035141400d481044458000541040060b042c014100441504e05400680c04000107100800c8244100c1d07400080001c000c100503071420011030028091100d02400340481c1c0c00b1114851f14080c4100e8601d00e00c0702200f0000313a00320b4040b12201919a010350030042c000c14120740001e50085044a620840342402810484074914034003018020040102100b00540204e400014003241c031940d207036030001005041689010002282035024803220a03080504200d13500f28401c1c2c0260340803040d10a07860040b0340d030b903560324080380c9060710 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 440918588 1250 440917338 440917349
    0x16030b150a02030909010605070b0103080d110412050607020303010e0f06041d070807090c12020906130b070302010b0108041509081c0603061407121a040e010203060a05060a090618 79
    0x10001d0600200350b8088020942840c040b5122075290762240400c80b1640102c0380014101c4030002c0c018804258543c0281400340c0c0c1c0803a000c250100012904035550300300340c1c003565100e5002c4616201300401404404e60000c8584002c0d4119854161009600758010785520581160310010900c2600e540d00032056420103440e000115414404049a60b4031680c4039411041c003841102081e80c1415004d12589200d05941d080781c000e40c6841c10304001e40c0f00544069008004011507880c0d00d08225081c002840000c502c00d4440420342070180c20360303010441441c1044a901d040000099001002441ca60344601001522500c640b070880424400d451001a4001c3c007201440c1c4400800c0e0008010f4a2259205002d01050070030122140003081e2903d1703001c190721200f10724103d103080c0d001d10081c1c1d8600b00314007210705007140414111228401046903e0350000304214007410880c40300710080405440162800701850402490a800e41c05810204400ca584100c01ca14554607804003824 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 440919838 1250 440918588 440918629
    0x80a050d1b02060702100e0c1903020d0503030f01090603080327010608030c0714060418020f03041a060d0213090f05031201170304121101170a0203090c0916030b 71
    0x748103500195507048101c1e4510010321441e9050310201c142d500507002c4440c03402c0000d040000c1c00300c04100b060359403498082e880c440c00301da001001d41d0320080040c180501480c09541d8900700b0b4504942c02d036805801c440700b1541802e900304006200041100e0b4400700c006034455074400c01e84110a91040100500b011543c200000428004400310052422200805c00c9610607903481c0005015000e075001c405a200000340400c03c4008001140d110091039043d10040c64200704a0455075207401c241c03010b68140c3c82200d00c90204c40302c0310f058140c0281d81220020b5400c1c00550009540c0c00c080c2d00701a621549410f0080104640e100c8600c04081d0310000766a140c000548180e10f10078000d103e000c0700100b4000d999030102e10003000300e4007900da91610300b113443c2025448100001c1a0442c0303850400c24280488011450080012406410782c12005a602c3c01c02d0050380e841c0549481240703105c2c1503541c1c2070003800e000419004617250f54a00300800d506c1e80e40c00014484007040d0701d0880102 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 440921088 1250 440919838 440919881
    0x15151b0f060118060e0c071b080610080303041515030204050103140d080108070504020310090f090302010b04140402150f0d06060f171b0906070b16030207080a050d 72
    0x341008142203040e2202c09101c40030b203902051600c03041d200281308130380c055400000481c500c0b0b0441d100802515003e41000540648140545022420240d10640e019041003045c0845001041440c000400c103507c01941181481d44500c50702c00758040401080aa88012880314031009003600801160020810013042d1394070b0a02c001c3e81402105100c400b40203101001c40c0080c002e04c071681c145e0320100020061981080240310017544080c0095806010891001600c9c11a50003080242e84c491000461110541d1601a00b0748281d1000c03039106134100900030040c907010707442d000e80c000c0d0101c9540000740320181c5003004520030306201d04035030000002c00ca550f6548a42050781100c11907560013202c82d545d5603040381d07400500d404195049080d1000b141c1c540c40d44403130000d0b500340100e244601d010074100006155a100c2041114100d086008111100001c2400203c1000031703402d09514080c0141c0c0d134210544100100c40d4107203d400b003118041140d2030343c8040310752080d0400000c1203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 440922338 1250 440921088 440921113
    0x30c0207150203041a0f0d0b030106051f110c0f011211031014090705030c1e160309050f0307051009090906020909090f030915090402030703050f15151b 67
    0x880c0c4c06401841040001007000c0c007014420081106d04c01000c0c5121903040811300340d512005410514001a030664075030801241c00d0340d600c0480602d0400000002c540c0b190001c10203880707503c030340ca0303228000c5d0401625a20075441c1c48445080041091070400700e0150f501c40310400410319403903482d070340044c08020480c00300052004841550b02801c403400c07000c006403003004171020045480c00c1c0020010f0001c960302e94040c1000d00002490a440010151110340d03401c551600000d0404085076401e20040e412300d900403100c070b0090201550140d03650701e20740c00460365484c8984251409618050382d8640e003e482004420050000c0c03060601c0021481c3c02c00d00b0194000e5140340c3d10950710300c0c0100318114000200150a0a00782014500304a00b4204200c0358031a8403012500d0004e04005005482d07a5074401944034000546000500f424086c5c1e0030301e00040c00401103030310b0103080e0b00b12544640c1c0d510700c42d000c0440d080b0561660350030510708514060380c4816843c03079607100d803c3d4a00603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 440923588 1250 440922338 440922343
    0x1509020c070b040605040302131d01050618090a080c1203090d110615060a09051305091603051515030f07030219050609060901020114040b01030312050115030c02071502 74
    0x216030380ca0300c00700c9146503254140030040d032040d4803464010440c01c00081005007440c4c2c40603c1d00c0c40f00d050000078120030340480d01180c0a20f04051100a0b507403403081002d285802080298080d10180c0074660510707045451030f540c0c031503c0c08050320820000ca00792100e80410002e0703001034400406242d85900b0105261583c0c0c034940d0200c00d001c103039030340030781405190700040d524800c0300c000c9400d520142c2c48a062080301d92100c00c2250810240c3c0102090310380343c0c0e14030000248403560b0300040c2403500b0402c42d03007810003040c541c030155440702e40d0410100710009040c515a046840090b14035407604001101c0c080041c400440d01805a52162004c00174081443c40c1220300030b940c0020700c4806444c1c5800201406d0291030350150044c024101242080d00140c41000810300000613003800c02c2004818080040710100c80c1e10321500010700402d6880300804a100c0ea44100074860395040c403081c6800494481080000c040c0d40e03070400c0300c0d264401c1003204018607111000c00250307103e2040003074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 440924838 1250 440923588 440923597
    0x5180415120b0c03070f03090602090d030c150c1409030c0a090c03050f09030406030515120a11010215071b1b0501020106050a1202060a030e0601062105042301150902 73
    0x7902e0003100b0000401069603c011070780f240e2030070b50743c4200f41c0300c0c485800d40041c42d03000425034266500b40107120b03190301d1f17006084c101b8601a88444004c0b25803460680084902c101a980074603003840c0001c0d60032500180c00c8200120204041d50725030131042c2c042481c000e144460719601400e800c01c001502c101a0f4416000480c265400788541e688078403000070810300903aa400000d03481040704001c010321035449a60010340205002928580c20400203607000e482281143c0c580e0402865981005a805100c81e0040300c20b00150000f85184103020b074a51100400f003006020011403546007085100c0036010740594800c403144030216000c0382c404101c0c402d50190310301642c0303007110205051801450500032900a40800201c1c413256909104250308141c25100a054a407803a061800206000c514040c001c1561081d0600101c468841d034001741451112800c54900414440400c400180d240100d0160010004009a90b0204180184810103080c021360100b40e0000c18190140e40052 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 440926088 1250 440924838 440924843
    0x9050714130b090703110405150c15060a090b0609041514221512081201140307150c020d060b090f0712090303060503060f06090a0209010518041512 65
    0x300284850304501c01294100220300d50302012040009108510a4001c0c0344009416220a8101030355540440d012403d075811150440074041400701035032800b0041285030003100e40700b0108a09049000c500310781e5450042058582c0c81d05481d954603164103086401094000c0c104120083d41e500714540180340074080c651080b071080540001c1031420781800401e00744541660700400a0b032502c140c008001204201c09212040c10700020407007041c03a010007016020310000ca0f40c0e0340d4481b05241000344140c120440f0b10b601c405035100d20307480024890040d18007039640b07100600310340c100c10780e0140e100381002540000708060840070018150081d088044094075501c8054035500e04110030101c040301c00d940000c0001001c140030601c01c2e0000058503009040c005280c0f07488101090400204449540d903082981e8248203581c2007074642158441d05444c0114100100d40e00020134920501804203110004120186403560350756004030a1801d0006565040c44e542d4075404000381c2600405 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 440927338 1250 440926088 440926099
    0xd0219030b1212091c020a03060608061012020103090501110408010228020303070e1f11071e05041a211902010807110708030a02030903070b090319050109050714 71
    0x9a00141d1001074011520704a014500c0e040000400500040b1071700000300b0f580c0a461400e8100240e00c80c02003241c051805004007107000740c14501d0991406001a24001c001d00041000f00b054011061001c0000f6909103808510744565080403800b40200260324140000c00040003e03030200154001e080007140a0a602e981c0010a00c240f521844c01006441c0985c10420019903818801d140400101400030b020340741030000f1616000f050f04811010801098018091030000c2604000000c000c1c01541c0b625165910040d1b407014030f0b080700e44a003501983c1c8030600548040500540181031041c050000700d80c2680040750040520402c140390304d1203000304010440075a295604541c01c10b074068543d02050340300c00303000701c845a04019401d1101d0080600c0410045c1c0b0500c000c08219070a1303802103840d0412001018100a083c3d03000a003880800c00c01c2d600f550b200412043ea28989949265106510a04009015014840300100a03000754a401f0982900b040489655401b0594070b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 440928588 1250 440927338 440927359
    0xb040c1e080c0409081204080c1002090301180c14040b04140628051318030e010e0d1a0402030f0106060c060f0c020c0906130501080a061b080c0d0219030b 68
    0x81c84100c940484000c3c5c5008020040c10400103550080c0030380041c03103407014928010305803140c2c1e820207240402e0080d2054000419030f540349001d0082d01c20080d1044200146181680d40c9d407604000940300b43c00750f40002c50381c184000e135140d40c071071a0868009402804060104d56660364048402c80c2d010348a00c0490858211110900c0d183d40c1c0c10661800032603504a0810b402c101e2800c6040f10344a2890303880d10807001d05030780e003c140384030380030701ca0307100c11542d8804c0400260030507110080050003401c440003031401080321103c801042130b9a243c646025074503940003180c01c2407020f003103410b459800c01000040e01c652024100c60824001e4004002841c80d4000080a8509803100c01005070f0040344200100d1070894119508000001c0c66403000084003002542a120240c2c030040054000458003014005d003070003002c1891564641c00c1c44203070032520f40501007a40140c2444504480411401c10041e03851b811600010521112528008141d9100502920721030b8207150040e42c2c04075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 440929838 1250 440928588 440928613
    0xc0703030c050a0f1b140601050f06090d0204240605030108011b02031c0e0f061e0f0103120c080c100f0c02070b09190303020f0105070206130b040c1e08 67
    0x3d40302c442c480c6684402843c03c1d41c0c501110280f00f001c00210780d0050552030000010500001c009065801c00050305442d1b1510040015904400145500402c000c11170540b5540c0e9403508040007540c112000150340c0504040c00b1400b450014080c01441d40450700410042d4210010354120761800009200020490010541c046107010015025038018441c020300b0860004a440a00e100c0700c10000d04414005045490410078050721030050b0005c3d0309112680c8105d81141c105c1503055055040103061018500c20f40b62014800580490314054041558610424898040c503030861010754541d240c13084241d03280c1039940310426107180380240c070508115040c0100b1204000b6500503180c818504503c080581c2e0181290a034042600510943d0350307040306000101a50183c0d0040c01d082100d0405036007192000b5082a00755030011080005903003c607003a41039031603403050244e40c0755100c40c0740051400489810100031341c261014084e131441050b244290450309014115080e20340e160 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 440931088 1250 440929838 440929847
    0x90e07031b03020a09020319020d060608010e0408091011010204091e110a05070302073b010b031302041508101103090304120f0602180f010e01020d030c020c06030c0703030c 76
    0xb0b02c030094021035443e0042108001c168080e41e8011031104c1c2d4518800081c0c50000308036031102d0007103450307260364032401c0c802c242d40140700c0d80c050100121607080b030f41050345400c5000e00803428603601c5805190b100c42c416a10485a401c030700205a4025901d540d191104c00003d0910795448103483d05031180b00040e8440740703000d000c120b00440c202140c07a10512080c00c03140ca41c81110180c0552090080c002000004104014140c0700b40704100c05002c2110030610852000300b860140700800908010300c094458081103035080000d1906210b0300b0081440410058541072442d04c10850308024000b400440200d030403100c400c2a148104004c2413944840301f994001601d0050b4258405d0000380724800360704490f080380c0b5005502c2c01c1041c41141d6035000070fa91000c031500078a15603035038018003282001b01c4c1c200507181c0b00b424068640c404000000b9039510626032010105034a404448652a00901421021b24400ba1210750b032071500c404c8411203030348079407000c50001c2e24228902d03d61501c02c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 440932338 1250 440931088 440931143
    0x3030d0b2101090b0c03040b01060e0d0203030f0a031104030809061b06160822082a0115090b0108040b04060f0c020303041109010806040b04030905040507021b06032707090e0703 78
    0x211238a507001d0b90a01108840400000c130040d50081a040e0310f00c00580e0701000034001c482d8560a08640d25402c050b030080507204207006041031100c0038481480001c81400686011440079a0550b0306c908071001c03405602c800306200c84640740100014080b01c1202141450100b1860b0b031070b080155120304010350302d1260600110504081c5213015100043c5081000785600e8022800c0d04415441020382031030040c05000c40c0560584d510721410401103441c00382d01000f88141c502c108828617a160010348580c400820080841c00780400007810403809030310500d4074041d14042000000070501029580340c1c419202a9080c40360f081355482e043c40d007100140d05856940d0040c0c10a511580d68049200e140548200e040c0600403030040743c69101d501c20f40d4855806a40106802c803480b6107042d9214050300c2540d40543d10420400030418a07881044104420820102d840d0008108001d42002d0240e0800e43d142814100c0030615202c0000382e07507090700c0c02007040d00794002032898a6202801c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 440933588 1250 440932338 440932343
    0x6070e12030d09140f1c05190507030c060204080106050a08010c020a020d0501061a041e15110a0b0703020310060302071101080402030a0f0309140f03030d0b2101090b0c0304 76
    0x41008206105154000010300791042c0106080f000c52880040d00300303c9001544517143c1c0c010980e410120084010304503100456040042c540701d842d00c220ba500c85907551042c000e100c030000c0c2181c2010b10890700c0440c4203800a00454840f501c400580d4082d0006124051084c504801c002c6103404042c401c840c5503004a40051482c04442d07401d002d41800c120780107480b503542c5c600d0000359119072800c140c1040040011480d58850902404000d03110310303140c66880300711f4599400d200306821000c0b000c00c0d100c064204040028207c0034660319040580c01d0040001d54410705000708a0340640255001e09000d1047e145e41075113440c03048040303000d03102015185c0b00c0742100620455000e803c0d801d401500244c140c4026072582d4039950450042c8803811000100c0350042004403542100061451400c100d884c8920800b00d080000d6480c022500d0340103982e5503c00000b607065840091920035260346d0f04850882400c001512802059482405e50b007401d580c500041d00070b0136100c00c6078032459 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 440934838 1250 440933588 440933593
    0x3110c0105090306040209130b0106020a120e091909060e010203010302030c01110d0c020402120f060f01030606120c0203090d1209090506010818120d05040c0b03010509150d080c06070e12 82
    0x1742e030b40c0c0170081280009031901c040961844420400b1400f81700c0c1245c013a0901e03400070803904115207000036000101c13808207010069401d410507004d43d15213a5030794125810780c150320710b52613624408034010000c5283c010151854034200700d44900040d00070310b040f24000c03810740d0100d400c144019111100c0d81c107000d0440785c01c4002035441c507074010401a42d8260002c1e0006083c4180003005c0030500d070094844111036201042080213a18280c075a90513103580c2880c06008040c941000900403c5462100044442d152001c0c00d0a0034820020384031600c400901d00c0625030340d1070501d12028000c02e191000012465540843d5508079801803c1c000e00c010380d03070902580c0e03461200744058414508400c1c61401540000c100c4080310001400d1610a01c803070000e01e50420303103000c0c8190b908a034061a10300800b400108400da50342d904007948182c1d1185403071461400c00d40007c03441020443c00400040f4003142a61181000081041c401d100d40d4944441c0c078021041004400042545802d0599 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 440936088 1250 440934838 440934841
    0xa020312090c101205010918061107051e060a330b21090703120807020c030313090f290102032515050c120c1603110c0105090306 57
    0x411412090691214454058030360404010001601a42e100302400c00050380101c02901c044d1214854940100740c22401007200f14659055450060724840024100569500c4240d01d10704100d4100d5a601d07a000c401d444e44100c40d00681c0d4181da038540942d038418402c0100158030544984540c54240c0e1110444504010400c005058802e0129440c80a1300b01d1040380000d04c0f540301c20181c01101c01d0808503030403d21843c1a503c2d40301400078218011640110000c0001c5149101040f00d148010329016156903035225090707240c5140401403d0b010320002910960141072500350b481a25013030201400f80140d0a805501640c89601714160b81611807a500500d11040c1403000e9190081801903d0501c9121200d5a08499a070005090300300c0403164003904104005410350780c000c000010400140c280a00802001d02841140290340011507011859075140c69058544002c050f4500c88100200e40c0f40040c00b441d00c6112101140c440c8460341d4250798000c1095036001c040203001404107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 440937338 1250 440936088 440936107
    0x60f010b0904090b1612140601180b1801030b010e01020c01050307030605040e030d060510050403080d1d1c1b3201060302090a02250303021c140108030a0203 69
    0x103503801071004640c420703607600f94640040c03011289148180301080c0200c6080c680c5400150201582e1441011150f00d0480440250840303010307425080142842c149095088203040c140500d042a0400d900e5640c000c12000d407000080c0d41380700e003915020390703080c00250081001500c0160401070101d0240c2c011090321169540302c1d50203540d1142d05850081203d51b902c1300401c0803176504011899054200050390040d16016000780c0000300001c4c0e40c40c0080004a24000385140118000201500d800240c40c11780711429401001c55840000c000340075070324103088031a542c0c201c03031410014040d041403012483d15005007101341107810449031781541000540d484403464400d0402010000e0340901c3c0384104201070102c610312614042000181341411801000180c3c10b00802c0c1d2880d0500403c038450039600d9201b040c80000c00003450741e003003041540c581038020340100400c140314210710202c46117120540c0e411140054021020000e916600c0300c080036201d106101004015078000c01c640710a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 440938588 1250 440937338 440937359
    0xf0b040606170309040c0e0d030503010302031e06041415010e0603060c04300f080c0601080703030905040203100513090611191107030c0905061306050901060f090b03010608090d02060f01 82
    0x50301b1814070300026011400310001d100001541c0064000950110050046007000c01000350025068048112482143d11b0090b0782d44200910090000401062907030700800c0800400c0c00e00340703111400c4c4032a503848828a81000c0011101c8520901c6107102185c0caa41e060000c4030300b03132903190034888900c1d94055040401c20301c401a28601745201c05c0450f0000c07805070880700100074030130034044e5078404c0c5043c001407801f601078111124640201c3c81c10000603801c00c5804c0c04a44050710050380b80e03610740b01c2c0c07100080e000f640229000f607540f02c03007405503100650050b40c0c514400e940800c04c1000d10007085041d03002c1e82004030b02a10000052009070f901809102e000f0000c50390803524026141da82d082e25950b0194001810551628244611482c0107140c200c00e06030b0703c540410000d450a4006072813443e042c41940b091003044030039218a42c0c4100302d21400703000441c0c6001d5403941d6512000b801d03070304129038038042401480c058104041c800318800340608410340c5e110f02a40d080005090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 440939838 1250 440938588 440938601
    0xc03241d06180307060c020d020d090b030f04060b130605120307081e07080d150e07140a02010e070f140a0e0c1b0a0501051008030f0d020a0201090f0b04060617030904 73
    0xb030305100c01e101c01c4000072918010060b8400300c1f90301405480701003990191808511070300c55024000710b28001d0040074113031020303640c0c0b0154284000001d900d440c14400002c0c107045000c1e41e084402000c0117103506499410070b1301199800e407a0707100c81052035007500e0744030b000e107140040220f40304025000400003952100c0c40c44404e0488601c0c0390405560715142603503c2000c3d20482c080d112100b0341e00c80c106006500e0018400c00c4400042c42c0b80a0400038044040c03000d040e00305007000b00b0b1713a0a415100b5405550542d0039001220400c0f91116580b1420001c02c0c40380141c03510a08030131101c14240100a0710456101c00341c10b04182d1101c80b101c0c6500d410120540d00c9a030460700440c01419010013000c02141d00440001809040007190480451425001409958810440a00859003540c00c86500080c40000180c4034400e224089001d046c241d44043c14602c3d5464001c014880030101c44c0b40114421102000780e84c0d568024000615108810308155070018803404115003065009503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 440941088 1250 440939838 440939881
    0xf0f080103021212030a0911060403110d1b03030216080c06040612020d1b022e15090905030a030f060b0301030f030c1b03030e04140105010c0c03241d06 67
    0x20340b03400b5400240420715400445100580a4446115505202030004091500c000c2aa880c60ad0241142c6a00301a142d1520586015856008400b014041c03d0090041c20103104840b4801c0c40d59281002945e800c252007010f001b0400482001803002400200e000307403488054505c5007018175000b0241c0e0400c10304c0060030740d00b507002c20000003200007920450240c4160900301d9801c012007404006d14200e120003845448a1800480d200c00c0682c841e071161011503944008103045540d28400c01c290001c5134010240303e800c203014941005000300140c6100384a41c0e800700b21900f40502c06806444062258202c080c000300011300c0455040c2c851122114002c6c10000a2210103a890000e504060304a60b07044070000311040c0704069022216a0784103000302c6081c807846002910400340401c06200c2d86042c801908000c0d410004081d9150004542000790354001a802100203e82d00b03e442c1c00d191100c501c1c144c5070f080703505640f015100041007224000d20071a5507101c0c22103000e04080044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 440942338 1250 440941088 440941093
    0x616141c020f0703020606010906081302010c050a0305040602060907050109092d0e07050f0a0e1b131701050420120a080d0501050607150207060e0a0c060f0f0801030212 74
    0x20300e141034050000b0280880003206550b601c03030303280c240281000300150519041202ea0041002003a500a2445811003000e0f000917500b6401440180d604010280b0001d10318064120380d40d090540040152040720300741e80a651a42d9a040301e010b460b5440c80c05402d0106412403003e01601c0040c0c0c1c4070115100b030a051140c403500c0040308040d40355048a800007061500e17842c000c1d08004080c00210001c000c155071f00d03140d0019003400100c0e14a5680180d1680000540000700181c810200d441c401401495413580c1e01d2411180a07003410350faa00802950952140c00304030348800501c110362040d50403007184101301c00701d04003601084403540d00785c6038090811400303041c040c40f090007180601840380d89010b5650850401120545605900c9148078120500c00340010800440c9502025803030464010b80c1c40ea01c030301e0000d004143c00d0070f105105119592701c030000c2040303900d20017040c0c41450301c4041d000c8031402011120106c001c402c2800081a8074010001402c110301e510750400c18402c107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 440943588 1250 440942338 440942377
    0xc0b100512010608101808160803010902040305120a02100e2401050907030905060a0209040f14040515060f060c0f030c03030a1104050a050f04140a0b03061614 70
    0x38405101c5090501d0340d9966030041004200d004110b01d02c40c041700b05505202c180903190603d4411a0803600c058186040083e200420110102d10010382552100206403656110b4031240f000790094081180c40c2d100f10107103407040f0031030901a03842001043d4010841172245170303402e101a0a51590043c0380c1c0c0b0607c400010081006201e00c010603c1e4032744446015031510703007007040e80000a0316140c107161a0601500124402050b8903522040b1054056174618040c0c010400604064042506462600c911422420403940031280154011801c880c4c04445400d10390103508400c1d1029540300140300c0c10614a400d018000d8501e030175072a41541c9401d82480241070a40d40400306058454000004001070718105214110009003000c03240780c1041d0900021810000560055500c214007102100111380c0d602d400200a0400f03120b41d0030083d0030719800c0d20016100c603845d868401e0040c3c100003108080d0071a5030368241c800c0c50340d0701c2c01514810244014175512055000003460003150f03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 440944838 1250 440943588 440943599
    0xa0b01091a0a09140105030c1605010c0527031f02070b10030203190c0612020d15061101090f0303150329180c01050c0a0b01090501030501060e070c0b10 67
    0x711144050008029102c0d62800c000c0b078010321621098000800440e800c860030306560340c0c03010076a40c1c41505210016a584540400c002c02d160305980010700c203600302040304c0342c07596004010707140c58003020544040141c0c1c0c0400c0604403180e2400150381640c0140a01c2034101032011a10711500d004130f4006290000380d0301c60040781d640031250540780b2401c4260030021410308000750f80402d103811540d000f030705000f540e410a01d00e105110f000c04100c100d500b55071986140303034100c0d60711b02e04188042144e60a90f0032000c00d0391003680301c5c0380007007000403001d0703800001d041c01200c000f50b601102289801b00c1595060f030040001ca0180201c0608941d80400001d80c28225002210404407145030000315500d4a20300c1c05900909200c4c08040c43c20000030040c1001500d402d201009017403064581d904462001d207000d6890401400c4030f60381d03400004c1e02056903408541601d004600078002e0795122581a507034001d0554000000515811002c0081680c000ca215045501d4030f019128003687c84 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 440946088 1250 440944838 440944859
    0x20411090613140d0b1b1603080603011104081002250c03061d0a0f02040f1802040c020c010207060e0a030b090312010f0b0d0f0b040203041b050a05090a0b0109 70
    0x1030b940c68400c1c05040c01c1c01c1c40342c14602241c16005040072600d0350100800c1c1c1d510110344507005821806410300c010240c54a801010303080d114120914054849185558107004050a0007582d07582d0185d468561010715542d00349040b501602c0d0094001c2c141076080400c0701000754042e050f80d4a8401c030141412100c002c200c08c90b01d00131802042c88501a41c01c604010701103500031200d07680802a44203100d00c500b01e002c1149826143c00520550080f8920300114000c0c00b1003412054a141c43c007540c0300b100c09043c0e00703541009402a40c0800181961040c261b03a14850019181e0141e48603540802c14184140317455902034078003a10611089940b03070348000e50510142c408410a4201040d101c0304074018224050051507800f40914002c0e01d0646001c280e0b10400f00c488807841d880e03402c10451603031260041b0341d181c240038008541d2032402d42480460700031802c1005502e9021040c00240900c1e0414003801591801010340d2a01e46403c062a402044201045411310030141400910060b04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 440947338 1250 440946088 440946097
    0x2031b01020d2d2d0e03130623031906091b11121902030408060108061006030b0603070c06091a0a0c11030d020a020708060405160b090d0204110906 65
    0xd000074030080851041c1c00354040d407150324205049031806095044481d030b08200c01e00d800184e100c80709641d2400c4200000500860314840c0042d120000308000d50003011a44201250035580c0c2c0c0010302c141704c1d5080e1000c0406c0c410550005c100c2840404d00110200d00c002080300c075505800503000381c1d605420000d07502100c044211040d440039582044c2c5810084001c200b141030400342c0411418400380c441140542c01500c9103244010740d58403401e42c02007046070050f02e94081241c2d015a9514002c0c0c1c3c0e5800b085600c0448603840a40000342e89000e8001c99032000c0c030040c4940c2c1035a4a250088500b00c04c00740302a034469495140030004103070710b800307213410240003000016080e00d007030100f031029607000d441b00008001140007030241d00d603c044140c82080f44001c1015a0318500c0c444100d02e8003a494100150f14011007050008000001981542000d00c44e00b400c1b1401c0d55481042c40c840c020401c5c1c40350054030700c002d6400145480c0c4d002c480c0e80300c09100294100310b000d0002c10004e401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 440948588 1250 440947338 440947361
    0x703050106090626151e0c0406020d082809060e0c040b01020a150908041a0c0c120c0904030302040801020c0a05010e0604020d06090203100207060b040c02070602031b01020d 76
    0x1603403038007409130aa00d038511400c252844044045815072981d000ca580d00350842000c10b0281d9244041946a42613101c00740000c02c60203807100007420b001100351400e611500c035240c054032609203664080380c06000700911901da480d81140621015409046101381400d2441c40744682c4c41d444c4100150707c611540503040ca83c0c0005254a260a0041c80125840081c0950540d40004444000a0007400d860113403c2d100c0540401c08051610304020039008940001c550520750450700341120345e68401910180c0e441c0b00844025610382418041c0c0241c1c0d68040b02d0081d0031200e08054a4242300041e503402c18403a10700140342c144d65104460881c0c00c02200c03805243c22884024007803050034050300400c46113220240c040c5042c16400101040742884000b808540c0301d0050f5825542e00780728594000242c14020f640c1d4903028941880204048031360340e0700c11440d01c94244412840014510213039012a0010b500d8440d480d18201075900019060b24074540d000c0200e01103010250007010941403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 440949838 1250 440948588 440948591
    0x1506210f021801140102070e01080d140d06060512060915010f0e1c05010f020f03070f0912030806040507020106050f01050d061d01030c0902210a1d1c08041a0702070305010609 77
    0x10004c4000900317140c3c060303000000b07104c48900140200f007000f103400c01081c200340c1490441c0203081e410104aa0103070240044200b07260800c00140d4a4001d0010705c81c002050f03180406c03669900341002070002040d6050161600001003003800355000c0d02c3d22940d8052241401044500114001a18004200b0169040c0c5a4501125040100c24055040d000e04030007815401c10481103000c136020300005008000b08005008a00070044c06460300d071004c0c01421000000c0b141960a010b0640c940940c0c1e0240104d15200008080d14418862041070f04e00c010261a00342c9000b80044415400000b4111211540c580c0001080c4064012100d9090340d907140305500e66242d070405810001059000c20140d41c010407900d8004c8107500d110b03541c504c012003018015070f1a144a800c005294115507000881c070000003100c107125000401212030825890002106800c0403012a0f8070300c029100107104018000c0e0000c90000440165a03000035207104485c13940381d40c0c0d05d400f0300352442c03a88003d0415 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 440951088 1250 440949838 440949869
    0x1806031829190b04050f060f0a0e0f15030a0b07030b040e0a05010f0c0206150d15090c1e0f1a160f1101050a02060f090f01091506210f021801 62
    0x700e8280c00f580058990071501044140340801c10000700810041ca480d10400300e00c204502c55680f600340d210003518810415a0081c07a21110355840718105070f51078480003c9160131000303280303400512034002c60342c001c8400550f903c1d59074069014000342e01d12994800d803150800c80d02800100400312859001d1400401c1840100122002302c4030182d80c03100454000c84208411003d007140110080202030381c0c5c5030700d21141c0d0f00b86080010301101485007600d06203c03070f810900515880300420b490401542580c04561b02884c001001c8251113071000f240c100013420402d41074082d4107a601311100f01000c51800314015581d41c40c41d407001104036030a110400c905000c0c44005019200888404e09005181500e01440650f444100400f00d54682c4002130000350b41c62028041c29140e1461400203026850403440c0544200500c1c100140f05039180080c0001c0c1d9040ca0381150311030700e03032141455000c072206844880d0180f551541c140d81000c0c5e9141403d2005c00300084180c001e004508030207800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 440952338 1250 440951088 440951131
    0x2190509090f0402010c030f0512012418050402070c03050706090815060f090709181d070b09060f12100914040b061215071806031829 59
    0x206400600415020002c0804000c0140d805c8211003034015050309102000f8540501708a13803c0c418520080c0b580c140010001030144541980290012400d004840c0615001401103a41407640240340d400c00c16402010006410030f540100342841c043c2e2fa403000d4060712900c50074a00005c0d544174500064607190304008114061100d001c01000b04214881582801000989030f140012020b500c241141d2b000714410500403e1808000c118901040b541c10a91b51000401040c0c8544c00740304038448030031040008a0b01003114002da83c1c080c41d016090400850500c1a1074101e0b40501c07022040420103e51072400074042d1a2203420034296a01e80d031800c2040100541d00c80103030018055100909000004427803055480e807141003665002d1030071605846051038005030105010540d4410024405020f80c0994451130441d4042078001031941c0d141740032000c54403070354003000b21810145c05210001d102550352884409074a040149400e100e18180000034078259188001c1500303c4003210701 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 440953588 1250 440952338 440952349
    0x509180106050a18050109090b061c020a030b0f090703020307051204050a020a080105060a1e091812140a080705040503011e0c17042a030b060901090207030f08090102190509 76
    0x4d01030320619800d01189084000381803040c203802980b194589841542182da102c40042c0c40406030120810950b2621180c900c100035404030340d07a800045d003403d14800b42401c2c4000788440645000d448030705240c0e2a40001c80c000d400c003034114400c02404102461665a8511840340964021300143c00044da4038410820204295071060b403069041a081080b075075194042d140c221800038150228800402d02d14815010a9402c030500151400d2a00c50140b4005003049515920402c3302d01d040c0180f9000585201a155061b0614818208202001c280c4a035880542101d458148507081075290320029080d54180c032140300206455000707980c0c16980500030902c90550031304200380c848100c2c01c00305800704001880907040d030b040b032405000aa03507600c001520000c00311448034519030f260314003841e03d000c0c26501e0503c540c828800100b407152107071089990301c82d8940c40d08500600b802c40c058842c200010300101c00c40d5428402900c11042e2074030301d0034101106075a8542d40d540301004224 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 440954838 1250 440953588 440953607
    0x12010902090c1207110c120c0402040b0d0b040e06041412030f0907060e010f0c23032d07110d021320040617040f021305040209060405070f0509180106050a 68
    0x381085074014005c0c5a2400210700303245020000c1ea102008400a2400d662812078055046074102e0710000300000d10a001401030080030b60803a100b40b000d00801c00400080c0c0d40c0109802d0f8054005001041c0014550f0035030852400070300b02610300040f15038038031240a410450301f520b0014004001c01c80029428003000014140e40d061648130301211034002445a0b0702900386a0900c80882c3c501390902040d0340001c00040e001144032241c88103401d02ca00d03107076000554481400d2032100004e15104c160303000d9000400010615140c109991a22803200310440301a1780c9402c8503500116401507100c810300c4500e44807852102203000260919060380001200060251050040c0700030303c00c4950043d0881c015110410520342ca0707840f9410101350355070701d00e800250700100e40c504075080044607820851183c0d000f00d45100b00c90340d07807405010642c0c1040701d0050003d990b00d000302c103074a80034502030a098400907200149074070201800c52403840c1e00780c00c41d20101d400481c1d1443d450764004e0485 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 440956088 1250 440954838 440954851
    0x70b040b07110c0126040f1a04020616030c02040c0522050d110a0b040810051807030308090c03030706480302090301020a03050105011d09010512010902090c12 70
    0x10918005003806890f211074400074400c0c100704580b040502040090414916403044011410080303080c0b9182410b51101c0701b4404030b80b20401d20302d6206103640400040e134802d81d000790000e0300d04204401d03000d0b5480202034040341440b04410380e0b03c01585852080340f41c060a03e8444555841c0804544000842407480300c0710441c2c1e41c484140103544170202180b1500b9072251115144900400c002800e41c0810b0300b000814400119000503900070010f620403681000c0502000700343c4400180740b1400c1c0e1010b1100d45035500400c0c00304002407050000a40c0501008143d8101021000010f0b045a01842003500c410751100255000c9401c01162170b545011140a0628491525002c40c6a8013940d10442d164240000c074804090b5070094040324201d46004008655038520741c1c2001c0c005240030f0140d6400903210001c0d00034207400c04100304082e100024000e0500c0c1c3e00c1c00d070030000c1d103545c0128003280d555203c00b049801078803000d0b181c0303000b030b0100300035907032a5000c1d000420100c0300b000700310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 440957338 1250 440956088 440956097
    0x60f0a08010f171207020a08060c0a080106030207021e010509041416020a020a060f1b05010203070e060a0e1309020301060e04300e030a150c030f0e060106110111070b040b07 76
    0x155440c45800103240754248130302c80c00080c0c0390b00c1d0a000150b030100e415400708410380900c07010800024102c4004103580a4240c54545039642c0300d80080302240181c4000a41018a059103507052941000d142c040d041c205142c41441c017142107003c501a04c2e00c50070142c04520b800b4041c041d1102c400d101001d0845c0281c03000b460244d2540d000101400c80030710448050010340624441e0491241c0000365004502c09002d041e0000140b078564000d5000700e0701c07000041c980003019001850314108403540404940e4031000c4080c581c030100020310151001d000e110035543e90101005803000e003d16001071504c40c01003460b601d07050410610140007a03255560552061310100249080c0b0005844406107510b4002c000c6070411000c6481c2032003140c0040d03c0004100300506190005801058030350318a59020701c2212442440031041c1d5041003440400b5400c40b50042c000d0622039201e0301101d000110000c9102102a03a1818199102c188260b905600a0301007205100c0e50035241504482d17039140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 440958588 1250 440957338 440957369
    0x1d03090105030c0a1205150f090405060c0906070501060308071203021201090207020316091506050c190c180504020f06160b070c061b180e070e060f0a08010f 69
    0xc200e8800104900361045000c03c03440c0100340f050a000c105803945003000c02050807c00081d00105603140d210074450401c0e01369246950401d0900e060095500038020301c02900c40f03440d110100d401c5004015000001071010001141d8240200340085014000e0195030b6501c50806860868840b01b00205240c010419071402444010500d4115160400300580b1021140300080c00c0900d122205148090349440100725082d40d0741c404031109851002d03c5080954561041e0303801d0041046200064101c102c2d58125000d00c1300802ea512445050724448854540e4034414840640c00740440565039a074040104600f0444e06c0141c00e88400c0324200d080c003045480b911041181c0c0e042c014003504281002c14000c0b40903221001da0a0760003901440303d4100140940d01c3d6944034012140041c00d1040c0b082c0c9103959018031300f0140c44050300b100c007180e0356108003914142c0c48440440d0300503800300102000c4030f0f100406088640e040390340c3c07404075503d00541c0b0202c16003241c000d5140003200c41c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 440959838 1250 440958588 440958607
    0x80a1404030f0803150918010513080d0b0a1502010e0c010912030e0a0510120c180b0c07090515010f2f0703050303040f1a010f0306051005040e011d03 66
    0x202c003680d12503070025800ba66179540001105001c40b884d1401604504208140844000d41c0d0050018128942d002000b6a6030b03900d10f0440e404220aa018140c600100710180085038142c100a540c032201034030441c96a1390701c0e500ba15a6410110515005075920b030311505450000b0301c95881c1003802440c0c104200da0805000b0604203101c08001802c1c1700b2004500e1460303444803840280140720080144c9400c0b100c0b41c1001c0c0420015070801c00090f49004115007403980100c83c14640f4142c1d50082c41c030020b0378124030780d5203a0b005401c020758078030a20f40c0003e81d105040c050184220300031030161242944501c005480ca0701c010412006001201803003c002801e959820706c180c401c082c0b08003520104010943c1e00700302d40780c0c101402c41d02001041006000038400d94210051052080c10180c2d09440075440d50200207000b07400e4840c485c0c0320204046401ca401c0a90406418000c80001a60702c10001c2c0403030306403d001c0c0415946608a80300d614002100c0015042c010038091480c0001c1038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 440961088 1250 440959838 440959853
    0xc0906090603150f080115120c120f020406120b13031d041401080607181503050a0b040c020c030106080105161b0609030c060501091e0522080a140403 66
    0x40c096031081640e5158000c08000408407940000d0144000041065442d03180d0349011f00441801d4071031814070704000290031b140d000c01507451142c1041d5080c907517504001e00c4003081e104400c8140c1c0c203820069240f10159441c0e01c1490002c04860b0310750350b1141150714084030150401881c0303040306a4504900408241c11141d807903210a0541c841802120303c00b0001001400307060340e92840c00e40704030004250f00c000040d8144c002e21040d01e44145100443e688000409918001c008407010f0450b00c44000798000d030030140c0c101c0c0d481d560109032614500040b4080700c4c180840c103401a0300100440360182001c2c03040340040c00c203402c02841249898004000c10400d01040c650400030408010f03c9542c42c41c900185210307a0114040c42083c201c0c0c28010302e08103956000b611914035000001558140034490090880c0381408464021500000c4c80c40013040c0c01080c0014642851400c0c0002d10325005441150380c0c4240c1916890382c0e0241c0005060b54030000d8031000044c001c000c1800821f41d403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 440962338 1250 440961088 440961107
    0x10050c0a0f08040f1212110a0908030a021f061e0504050604090f110406081b1f08070e0310060909050114010302010804060e0c0d05030703020606040213050402030408041203020d02010c0906 83
    0x1c01400894400201c0e002c0f0360420038143c0d80c411051030444107520359084400104040945942c03909d004a0310f600301e00d1740300c0c410603802030050385c072002d420341c0b0f10101100c0d01d01e0614110b0034000f400994500038880e60310f00000c0142800305250f2820710451516100e0310390000000d0b501042121511341c0e540051403a085009000203001030303101c1d002c3d83da554010901030401c403030980c0d21005010150004088a003002c051140c6281c0008000340012100c454a0710f9085030383c0c0c8412921400816120120300c2280306030540200f00505840640d03501442c0c000303100d28140041c4a25150801328211a0151310300c451140a00c001000982e0340081c0141c0c0194100000180f94021280050301e0460040810f03a00900921040024044040060a80107020307400b074610070b0743c44004200492007a030303004a030342c0c1004080c02e01a60915601841d8040d1180032b0b0346242640710b509001206990350700440069011a940c11040fa9085c09020b44441040c14480340305400c10740040c020001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 440963588 1250 440962338 440962343
    0x20624010302074e0f05090f0603070207050f0a05012307061a030f0f120a020705181017060c0a2303101406070803040510050c0a0f08040f 61
    0x70040348103000d100d101951035409011510301c407039003501d9105141e901c0c4c001e0300c65030807001c0852104064003c080340003038604c0d6040e9a9030f65030000030440400c0d14150070000c1b507140c22072411448040030381c8400c401103000c3c40c120b40060000b98a4030080000d03926450312124003403030046c0410455039070820900b1644240c000d03885440c060b260310f040d003814001c041005e00f0791420001038100600c000000075412190071303810b40d00001d2100064a039a80c010fa07040c10000d500202903090707844000e401801c4500b45070310582c0c1550741c1d0f40c800640e1308185208a241c542e1002c0c01800485034036541000d00401004c0204110030841c52070140d140c4000030300c0d100b0707030341e10000ba10042c0900c0303588000011628201200f0340b03281003a005c02c002d80c0080780c102c9101c40c0d102a000c0317400f800e4058000c0c50480000d2800d850703c0c03050703995210a034201500846070341c0f1810b400c03d0204031090150502c29180101c1c9582c480101030720040010000708195018001d4610611020982d8002509449074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 440964838 1250 440963588 440963591
    0x207080910050c0604030c290106050a18090501050a060f02070504020304080c061305100b0307030f170d0c0f0e0d12020c030d02061806010f060807020309040e01020a0206240103 78
    0x1c0782a01c4512030800103800300e0180c101040105030300460010305050181002c104450030714044078502081e04084c4818100c01200100a124411001010702842c00e2901c540c19501c0941101401c8030290055108030351220011f01042c1032410a01c0002c192500c0d1003141030740c0200300651696058007449028540000c0041c0900c6811002c440c07200b07001d602141c0891401003160281b40052690440e00c03030041d04480041c0c00c449008000c132921008003e440103a141d6a40c2d42c0200035642d004030b0300c02522820f01208142010050700004140882c003240c07121541c44000c10300d81c03d01c50150244040340c058058503803941200c0c1032140c0d611464414091920b0139042e460019505c02036907061140c00b401d9140c29034086400e50103110303800980061a88002a0140c540d0024004c148070001c0c0403104009440c4106181500040b560060b01d151171900c00c003090545442c20611282e0341c2d000a1003151307042e4100400c99000c1c0c41c4640c0b20601d0940b03220b03480d0250b8058071401c1d0425 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 440966088 1250 440964838 440964859
    0x6040e070303171e010b091903060b15030702071806050306100614040614071401180501140c0f0a271d070219020f0604090905100902061b0a02090f01090f02070809 72
    0x42c0c80708c540c2d64100c1c0001c010013204045e5030f0b2810001801000c10b0f00d501a842c404105141010781800b668020350300d03500607205903401c1101c040603903810080a0300c1e86075124000015281c034240129070140c030542d0f107034021581c00d090005d410f8034005944182c00704003c010070040643e114400f05280c414210007141c0c0d40e0040d052115043c124845413150b15480e1440c0724030b0403100614140076103407240000780b04445600304018103000e0220307004800c0720b40c00c11040c00311841280c0200000c110b20700308071004100000080c45040c0012000d0002101c5141c8180004107408113000008800c1e2410f41801b880c0c090030080d04c0380b08140d042181c140380d0305034031300842d581c1440d10b5405217806001c0340d4946965100742e0020388103034103007610503004154528001514900410a2240d0003814003403401d000c181e84941e844440361003443d03560103080405001607844011040c060101c0540c20061035043c8201007049540403a0450400e40c4108131a9000881000c207403608608122100301c1078 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 440967338 1250 440966088 440966107
    0x150301060815130e060a0b01050708070201031e090b040303180f020103110d020304050a0b06011d1903060c0201050106023a020a150207060501050a0302061206040e070303171e010b 79
    0x2901224280010f0660510541866420000444501c1042c1c80740c03007481440703410001500c031071080301c6021342590400c010500140d40250828200041070b0340c5428512030714110304108669100c28121a8103020109003c18154140036180c000d08040440b807e454805075036003002480035550007814180c54840d0103000b1090901500c030003078519901556603241c0b51400c0b580300c014441c0115036100c0c80001180701d6501c41c01c1100608024130705181e04a02c840410441170f170f84440ca80c01642c000b40c040100c0003909500030341d11044000d40001c550343d4140007010707007082c00685d00e503030f04094020b45055003140001c0d030307010b43e03042c0090701510300d00d22044049090590424018101460410708910744c031983d03500910615024203030402069032164200080c10405102c040d501070414440ba540c4034050140c501d1700000010000521400071074411410800355074401c0c1c0103d01d1000040c007282956802091303200303070180964880190070900600c500441030007904004da03030220380d1410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 440968588 1250 440967338 440967349
    0x3030b0f1908060c0f0f0d0204030204020a180e06061c090b04050a03140304080712030b090a02120a020f12070203120a0605040c020c090c07080d05010303030b150301060815 76
    0x5880301911800c418118050041030181075441082c00501c24000064004194103081e25504001ca803151840c00ca151081c00150350460082628469401c02000005075124401080622895200c0705911100c40c00c2c040b82420382c5500003050030400500300030440c1d0310714003216100240000345441443c0d2012a400c000c3c100d8480c020484a408024003050140c0043d144402901c603544085403035902c10141078260000350340040c8a103200740320040005540c6c03d02601d0350130103850006510440200051a0994150303010301045500250200c0c420802404096200300059015407410302ca000024085200704000404240303518808503402d1131080c0308403112030a4a554440c941e0400400e030300001c040c2840307018852481e140300c01000034008100b40300d1300f80004001a03010365a040c00d19042ea444118101d0312000c04001e41200300d1300c0c41c031034a4082c46c040e940c000f0f4056520400e2000c0c001a0505003844814188010014560700450643e4001d850400002030b256150300801d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 440969838 1250 440968588 440968609
    0xa0501030f060f140a090908190e03060123090c16080c150a0b0907080a0c0e1203040614071502090d060e01090b0106090e0a090c050306090a0c1d0403030b 68
    0x1e0060381c003001c0005590b0101c2200c4498130404035800300b22140e1320f0100104072098194010201c0109000121103440018a04000000642040184040560002418804241c0192100d4a0b890090084405c465034640b21940000d5400075503609281851014034000c00900b01d00c1e442c0c0c4030b01c6103800c1042d44005d80d0041a0040200c940c4413a0038103c580c00302101311001c2c0d00d070340d00e00301541c000d40c5001042c0c01c2c0203101c991106511034482c02048001b43c5a80e07480d03141841401c11001845c1d444903207500720002000005191268140f6000420180d01030380700340354081050102c5030100e690010550004001c1c1d500040c1e0320241c25021030007140d054140900220329010340c0c41c407a44410340001680600c6161003044582c1c80d040141d0340541a805180c9000f40c00e40c0009600c0f000503881100301e24003d0244a00499a071800249800001c0b07640c95055003100402e0004c025203141b000001e4003440111a0700100041e0507806000c400908c0941010b49407148006191201101403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 440971088 1250 440969838 440969849
    0x60f14150c1605030c06071505060f100206041412180d0212010b030d03020a020d031a10090e0109140a05190e030a110120030403091d240a0501030f06 66
    0x1c0b05255005921100408a60310605019010f8000c11810340e192030b4045135943c82c1d00c203032020030150950b100c031f5006280060103940c0205503031513409215039482205031410103d55008002500d818601a92031540005010f116a48002094072640e10b480003615003503c0c0042c0b82c00c0014034030100140640c2a40d540113900600c4445c00c0603807410042d08a98081403050301120303203144a8420440c101d01ca180c801500681102d030350402074511982103010040440c0d002c004034042c40307000045460b0f03a05481c48010451344503080003080b008100c003d005111130780003000001e6082114002007200100350034581ca5941c40041e42290b03c04102ca0b140d070104c02010000300c28015440d5941c2e91041d01407402103005a2010b4955100500820303218004d0f800040655519043d540d0b01c16800c094412000e002d845900800c1e0038854800c0707074007404101034203200d05051110404022241c00c40d110300c01c10500c0c090901c2240ca803084200200c503000c1c40c00082c8050480350759001041d854114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 440972338 1250 440971088 440971093
    0x10f060c1b0f080615010503060409080c01110301030b133c080405041419020c0307120206060a08151801020d0f0b1804120806062209060f14150c 64
    0x11030b4450250744070384292014a400c986007a151484100d01c00b170240101d00e4005003003040040c980d1b051940100480a1084460605080c4406421800e440c0100084240b81b01c001c401001031011800308590001440261908001096150b9107601804c001080403a1000040800c3c01c4451100008110140f6200c00305642007188c600423003558810701c0b40500c41c4d070404011105031a015080d19000d5070600020440c21405146101c0103904081170003a0a8003040c002d000100300118096451a05150f000d81103e10b008010080c111416812085155000c150403d0707030030442c0149030b40c02800742c000a00301200c2c4010050301901c04d401d40c200007d0704000d490040d03620b150f0000001c4500807956804290909600c603194024201c42c00f40c105000000028011030103451001d4104001500071031400d010300b02003486146d002034181040c00b140d2035003000100c2e024411040507145601c1c0a441d40c61410b104540a50380e02d4030324a1180b01480c1c2500c10101c00202251598080b4109 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 440973588 1250 440972338 440972393
    0x2106050711030a090807050415090e16090510150e09061f200c0108010b2a0307021002010e151015020607030c0201140c07060b0303181206010f060c 65
    0x14020224081e91164641300d12032683d010507e4074041c00348034401c03204000541c40540c54500e90320090141c8914407000340c080c482c0d005c245d1200b40c2c0500c0018050070b601c003050904000460b88044801607020103005c200e013104d01c81d103056100510400781b040032990702d150f640300c0d040024003015210881c002400220149503203440d801c2441d280f0070039807840c0160003440d1000c4003951200c2c14849881e0004036444018007054400b44040c1c402606030040145914662110307168150f04200406036051f800491300c98214a428002000c0e1404e1a10003800340200d0148100d43d14140803030201320301c40d074a4000405070f203600000c0c100108a03140501c1c0d8051000200a901d03204240c2c2c44c440040d04010300c030b0070040d005000c0c1e00905281445000c0f8540c8d24850350300c40075082032504840d91a150903030366520755400c00140c6444440107641011106000c02000b800301007503502c0c06400d41280004014400380c840000c0100e0300305080600406d01ca40c644254411911140d01c03403410042070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 440974838 1250 440973588 440973607
    0xe07080102130e010b07020102060103080d0e01020409091506050a06121e090c0909050c04020a05070b0702031b07030c0e1f030b10080c0a05010521010e060307210605071103 76
    0x404000310740f400203244641d44d807644000740880c0b0421070080d0160740070a00400004124100512541200c0c420010712202c0504200382607901540c040b0403900d8032004a001845581c0101030b0103048441d0080042d10301e4800810852006440f61000b44042d569000680e0b50240d0402169400c0f480300072801d110040000e1001070145480c10b40f1900c403001008143c1d0030b031034801c0b00401c0c2e80020003032861144200400c070203540800c0418041003028443c4900040c00300700b405008912940145441c1c0041e00550714501c00142148031866000000401c00304811a060f0b40c03d035201c02e1040c2c41255503111803584000056030175092000400e0200100307102e940c40e40340e4016803445144130703141941d07042001e0b510601484c0c00c540c00f070005402080a9801100100180700c1350001058055010301088032045009134424855240c00340104160780ca001d001040c0506112040d18000307562085102d0304d44110103000030080c039610307800f003046035000d8865510002d2030142102d55400405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 440976088 1250 440974838 440974867
    0x71403070303050609070509040c050f0a03050f3301090314010506100804021e13061e05090121050109020d1505070e060927011d130c03060e07080102 66
    0xd1500740e000a203403801098941c6050198103005920b10fa44541c10804060304000082c10508000001d00004200030f6418103007000203800120f2a030786000800340303000c000c0c1180c00c0400400fa0107403407040300106c0340403810a000d08090031401588540200c5001d20040e0380740b448541015001c0240008910140c040c1508810b101b04020740d001141505100026280c01e041603070001d50050304500d10b0b110307402c40042420a901401401c44c04d0b010000d10b84007045030103a0300700400485d01030f41f00c40d00000711615020000d00064a400c540c56151440d84c0c15005900b9040b200270b10812140c2c501880425000051600c0c0c0080c4280030880d801c0ca081c91550340409203182155041c800060740090090700901c440c52005000e02e440e22034130b041041403a00c400894420340e000700d0380c0d40c0d0002c07040444016018114101514808100d08040d02280752402840013800d8102d1142100000f160520407000f00d07030740301070041176144d50003240d00e0424045030401c801d190700c041403416400040303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 440977338 1250 440976088 440976097
    0x20304031716050604030f0e090a0c202103040819020c06030c030601110c011b020315041a09010204052b061514030106050306130f0b0c0a17150405060105071403 71
    0xa52203c0c9000928008103a680720b00892626520800303120010b48500b4541e0050340f8010841d103046616969200e14207100c1c0710548400c8000ccc0c1d407100c0e190300100402540d5540c1040036009009080d80f0b81070742d0b100400c0c8201c0d00d0009242e11081800c1d140f6600030400c60001c004000c210760b40724a4918418405600210b032a5800030729802180f681041d00860411080700c01039442e400c000221440e064443c0411b8241242c261003640b0b41040c1c48180c03150b0142c02980702e01003601403061010780e03c280450700607064481507441000100080d40e40c035a2107000b400c0c00000d21030400040a001e10a0401350128043c0145081c41c103500001d44a440704402991107a06444180d51314400034942241d8441c020241c040d0b00000214000d01c1400c1e4a00d0186072045030340310100c80442e03a8078080d41c0815030792219550380204007440007035001140c2103000310440517150a0351411401d8100243c0100300c005016079510408205e1301c3c2d12030001c88a101e5080b0303050107004802c0b0610287d60360300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 440978588 1250 440977338 440977343
    0x140f01050a15090c020c090621070603050606040806130204020705030a08010f090b06120402030f0a05010509010b010c21020f0a0c08010c0e06040902030c04030f111f020304031716050604 82
    0x184403101040484032031085082d074130b6080c3c0c01005080c07005c400b400144c40d4041c0c0302c554070025045220809101d201041c00c5140542c0020b490380310b1424801609440000c0c0c155441624280f10500148078001a200d6003c0380c10042c845d02c0004c580081802403203001d001624a000000c2d11843c100c1d0041e20050407601d90340f031804e100b5541c518010040702c082d5082c4980c054800c0080140099401d40f2040c1c20078001000c0e50343e0349000001040c035090820000b22060f944400402c001220217126803c0400801c1c00e00d00700240180d96441c40c0e110300c0c0d40d094400c424982a90b54000e910802001c1540035941080f1030301c0c5055400e2811b00c4036a540304101c500d609140d850340415108040d440c00d1010041c0c100c5003010300703255466000c0c0d0001400c0b070f071304140d0511002000c5501e0010002d046030080d0700e9002800d40c490140030404c2048041c0c07540300400c4440c0f401240342d001044408503034004005140005804018a9040c031031241d046034103248a00428090280c040360341800f552 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 440979838 1250 440978588 440978621
    0x70819020607020715110106092d06030f080c0a021005070c080d0c120c0204020d050f06011e030b03010b1002151023010c2a080a050a140f01050a 64
    0x50b580b0a003281e0f69113103401202010030036288441d9820f40200c210340508095040045815030b101c005040031640300f84882ca405052040c002e03002035903141082c0f03020a488010601540b0704585807c00d01301c0402d40001c0c80030340c0c000b44840280c40c0901500b026250300a20300105d40311301c0400100507404c0b6050950307044850980004401d0000582c0c50710403030060b103e10885107000e0f103e046a104404182c00d00b40001041804016030b6039100416641c2148000021310341800d00d00e02d840008018011414403e0720310082800d03040e0808821180d02031454003007044190741c00800d02500b000400d141e000040d40b5900e030140b503008555906954942d4040100742d60324001410380a00c00c0b480380c0c08024085c100b0f2080507a03001d402055031030b14113042a40200a461b07503059104071126009030348000185030070500494244006800420100c0d00034480b0901a4541549412440f01c004080f99a41d119064221600703010031110080c604008228a1400074001c501500d4060b01c07051501 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 440981088 1250 440979838 440979841
    0x904050f010c020a1110170916062f030405030601032d030c08030a02041707080607030902060f070f0f1104050f010305030d0c050c071e090209150f0708190206 70
    0x142c0c0f0005144071480c3e00005030f03d10a00070001031104c00c180b0080442c0c10803540d200400d24041c04014114080c80c1c502009001c1034140690f02000208e036900f03c2c9041000395078030003844c0f800051180b446081c11f01c408400f00c1040c204100d195101e2940115010300940000006001d440f01d6080e1140300c0211b500c1411211101d00344151240d1a580200801c2100740d181c808a003d907805560301c80f1071000c00601d0503842e070000315440a591800100654403d09060040c41810b001150700440c6604080c44502d06540c0082d865000709000c9842d040c1c4041250005d2040305c03100a26a1a009441540e0708006824440146040b1507603050013141007101241c810403007100710504030ba801101850401c0042c0c2c007a0b41c050300210700124104402840300301d00014040c0309000007040f880d689040c910300c0b403005500ca80c2680d50f10901c000d03031040c01b00310340c01e840b04901c0c0c44100c86400c1c0910f50f1140c034400750040034014000c0141c800c0002041101144020f0071001d01091680d170215040c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 440982338 1250 440981088 440981111
    0x130812034606032a030f06060306050f04050f010204050d0807020324010801050708040b06010c030212031f090213030321060b03010608061207062609150c09030a031202090904050f01 80
    0x42490382d0450340784107a0303c20005c00204402c010003014243c4941000303d5016500d88441c4103581c1c0580b08040c5500001090004002c402c1044800e600541c00095007810300c2c040005400207030820b0003800504c400a0303188110340e02402804440b6008045080355440d070a0204903d10000b402003945d00d601c1e010100c0d5150f4004c0c41c0e09807007503500090600c803968070100115910171442c54220103511492300b01130b203000030580185100b0070b011001c00e03003031030001c440305001d50906502117400140704020b4003002800e81806d60b029280c0504000700c0c01c00300709080b422021034103092a03102e20301e440000b04a034070508004504940185e0b03030700281911504100440c040c0c41412440c500c0d03100740d0b02002143d0040b10070a40c42c10319044084c1c80c100340080000c00d0030004840501b010b0f008402c450260460041030f207908201c526880c18109030301300002c2683d5124024024003801180c0ca0090b001c0c50b40b580440398000702c007070002070090605190660780c1c4e0840000c0140d165090032000380384c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 440983588 1250 440982338 440982383
    0xa0b01020f060f071b0b18150c12040c0f09060302120309010e0f0111100c110a03020307110a030f030207030501181505040206090613081203460603 65
    0x291001040f01c9000d494040c000e41362a905400c1050440d903060f460303007001c591028661840388002c5a01003803100072078415903041030031810480320000351a0013449000c01d61842618264042420304040a80b0f80c0c2c200840103c0b51503105500080c05042e02040c2c0f42c2031070f0060b4080340d10964191003200041020b481c1c503800b58442e0705000542c1140404110720f010000d50748038020605146207011030380c640c0c0900700143c400da441040b5442e84401071a0310f030700c074211880542c0c80e500075103540030165400945a00c11880b010703060a440c80c07200341c0a03a807a800d404009540c400550508450079107000394881407944801c0e1010752800180c403014124401d1000305280d4843c00000c50040460105c10080ca0013400a0b6000b82d0184401843c54407032070004d0603152055049454030754038084038145015130029410700c00140920a10191101c0740016070f1030b043c055409210780300a81000c1d81101485412082c036000340b8442c217080b034a2601d07880001500e01170000303802c070140500715061 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 440984838 1250 440983588 440983591
    0x9090a02130c0e040911040609020705060108070518061801170f01050714030408040302040608030408070b0f0706090201020c090a020901030e0d020a03082d06010f030b031903030e060a0b01020f06 86
    0xc0814120164210b484c6041da01c826a07043c42920300c450900440f5010808071034441e000151100d44c005420700502c041007010b58010054403005260081c14540400c0d1055107107030711035031445c085102241c0d81e6a00c01d06d071004188114a80780075103694038007410340c0d078100d441d40750341140c0282410003600820600605100e101203407216060f02031a000d9155140d80014015969583d0500000c8016680c80c020300d00285444001940c0311801c24449070704240c543c2e40030700f80d20030f030800c40c402c0044411000d4640441c1c0020000170f5400c3e007800141e0601841c0510b159200d00042c08020743c6400350b5024101070b5000b07a80400100c1003600e00715a64601c04258403000d0b030301c80d81d00c1c140000d120f924502e070b01200c4500c6926030442c4481141ca00d42c0700d030582c5140d81180040800c411560301c01d00004081030207103400d02100608202003a15401884040e2010740050965a014180240c011140818a44007203a040380742c0f11311a200204841005240113016407090b0000301c800c0040d0b510b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 440986088 1250 440984838 440984861
    0xa0917071a07140c01110c010b1815040c110d080106140f0d020901050c030f07200906010f02010b031605030f0d05030105100306030818040e16030b09070509090a0213 73
    0x100c0c1d075003043e9202078900b504800c0400302c00359228a120031312035007a2030140003805124070000c201e004403102045200600915000c20f55607807842001505854500c1440250000340c500180d0039050150480302030303200141d4105541310b101c804030341d02540700c17416074105c076165a103c2c011707a00c610075440040d20482c0501c03080380e80103108819000d01158020820325005042c19803500c200c901c491411500403954a80881d080403804200b44400440719049401e9825400410308041c0c00029800110180c405810025200e400c401401d0003540308884265008084a046074012080d4150280e410300803d406801225241504514009042040d01c0703030a03165682103a08150a104041c0304a1070090101600e82e100080440c010900800c1114030701400c001d481422403052106994200b0340031f4030305038050480132141500c003100403000d80e1b9002e0781446094035141c01c09032414030140c00890303100b01013205004a050002908800041c405d54a0500265410240000b111241201e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 440987338 1250 440986088 440986097
    0x31c0804021e03070e0103110901030201170a1d06090c09091506060d092604050d1509050105010803040833061807020120040803120a0917071a07 64
    0x4900140381c84030302030202c08107551400e4908400400000d00d801090742c0300c08408440c000041c814440c241400402c001c00c01c4d5010903080d491680004e0903000c1803200906128101000300b107035401325800100c0c614003030071500212418044452504d503102980c17011980d100343d03d400c1205003004142c3ca880345045030060500c450040c403440c00c07a0701d001040b0580c003c00030000404d000d5203510803018054012081101600046200c8071002103000a58854000c01407008000c242d9805600001142d400b4211603288142868031001a1106020040c4507509100010480c0c82000010f0300840d002c103400c0f5040d100d01e14090080c17501c1620540c00c842c0001ca190001c2c0e03000b4256050360405005010300c0001c40c074001100c080c5010030303920314006035140d6600f600e070004101000b494554803808294074151134198a50f50b2446610802c521404e1002d00040c00110b4590201c64035503046003100c681010b00102d224655480001c08036850301c42c01441c94850052100c0003441002281c84 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 440988588 1250 440987338 440987341
    0x40c0c020907171815010e0a0e19050c092d0601271401110c280e0402040518061801020706060e0106030c0212090f0f040911031c08 58
    0x91059104005003a5028030400000b4850f6100f03100d988984150a0941d1401000c080000303c1401c0000c40341c013074881c02084600502032074402651140d0080c08018000455034103256889041205216841003d0342ca007485501c14040003240c1c0c0c03481d20f1400ca0341c0070180e0303482117000034184a003124030212400510303d440198501e02107185810070414140028032103024000030707a00e1240091120420b1007a06001c01c000342c1040c40d1008001000d09000180f00d00d4070320620380c1d0b6400100524072517403402d28400741c465000300c3c0b180442041042580a0140c4642070a40c00290036501203001d14604000a03840c806210080c1a805095102070121030321042c2c180803c13503c0044124802303550030440f40c03000540398860704004080202c00d2821640c582311010303048074a03282007403065400045003014000451422113510309400c550a81e044a6076001181515513480c01181e00540340140f10014400c2241d00c2c0c45114108030207c0e88074104411030f84458480b01180d00c2c020600700d10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 440989838 1250 440988588 440988593
    0x2031503190b04080d090c050f01260606040308040e0105011b0206030402010f0905030d230316051c050a09060c051309020d0902090115020f1b010809160b18040c0c 72
    0x803240c0b40c1041c040c180482c28003c11317100300411200360040484115004101c200b02c3c600700b10401c00e0080d0001d090042da542c0650701f441c0d44403015864040d4020301c601e0002109507072180240c0f8051600b02442940b102d403203861640e0948800c0c05094042020312016141011a55a51902a55003d00210300f5511194010741c1e0344401103410340d040c81452000490707541c40400c101c0030182c03a15a504800840a0314851420f0717418691901c1c1c981208004000b00c0e0f042c18005141c8405c102e01d065030381c40b0007204442901c03050810101c6012030401080c01384003c100d8001d900b07107900450003008a415182e00689480c4181c02d40c07005100c3c03840c8820040340700f1582c0074144509500c400480e03c03442c9540004d401c034009030040d544c04041c02c001c941c0d4090f410005842c4601540000b414095844c458160392107000d0f47d502070400c44004d000406010090200c14181c2d0001200c0e0b80c00f0b0b0740c1b207030708020041e00080c0d002a81d86a1700b02040c0d0701494180100150a001ba071035498001e4150b4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 440991088 1250 440989838 440989853
    0xf0f0306030a0503160303050a05010b040b03040317250206090616030e010c093f030c0209150103140c03040f05150123040902030c10020109050f010203150319 70
    0x100190341c1401805980804114244001c1544901080402d0340c442007074070b005022500f000d0308018003d440c10303006111015100d011036056440051015481f655140b90403600c881034641241400711a0301c0c144110308500c1c820007541c0540380031442c0e4030608404d404030303560310003203a90041c07ea1205000c00c446030b1400700100d4031310a003482d0100e04d4520040c90103003524548041c40b000070b03c00c5c030320401c0036000350400f00303520702010050048086184040194541e541015450b01210300220000c00c25000340d040000c020750140801e50706162080700c0f196004990b0000d5408a400c2c41c2c1480e1103106051071483c420301c0000d811701c0c00c5464a46420749103064400c1c04445038820300c01030170342040310304040d54028030741100000500400c01c180a0f230781885d58880c15020b103090411590040e6000310f0200864541500d19003407070b4203c62000c83c013400d11000301070f00030f0180300500c0b8811901900103610404883c07008191102400e4141079907006c00e241c4a450380070001c8202000034400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 440992338 1250 440991088 440991091
    0x20310060e03030f191107030c06030b0d0f1101110705011709010212010902030a06051206190f111206031507080403170a090203010b09070e0f0a030b07020618030f0f03 74
    0x24007180e0609a0860301c1c092140d0164003522803a9034000140d915495001000c40c103d90440340287c42e0131851591075500800071401950181915040651801e40716000380311401904680c1c0e030b500c01017203230810300e90300580c0030845400164204600c42810b0030000e1001308564040e924205c2032807108000350340f61000985094036654081054241900c07e14071618042c0810b0f600050b5241044019001140c20b642c0c021802410107211041c0100f901003101036101a03001143c058882d404801080180008841c3c00a4549081842d03185008510050514602c03081c400030250344828080681e100d00d800415580b429001001911051085241d0b94115209040211342d115141c241c148400d00115080b02e60660342d80c070300c0402d519090089511302403050307603c60aa414004070003003a107001c55103814010342a9400200c265280ca0045800450700300040003401e0a01e860000e460750003e50725201d03d010b005407a00034000e8044222131202c109070703503014a0030707141c840c808520750070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 440993588 1250 440992338 440992367
    0x30708010f1523121801090b06060a03110315090a0e0a0f030504030519051e030a0518090c040f0b090f10021903030c0f0903110609060f04120b0105030102031006 71
    0x10040145942c0752046026190310200201c048013649028840c0080032515809400c0c40e90381010f05c0000810208400700b41c111005851980c0d48540c0310106034090500c00000035003040d8000204140404001d41c50369008000b00c60b5804c4a4440702100c009607601c0804005460700b03c41c2c00d0380002031001d600c801c07000b031007400c12600b0580e4903141d040c18032080c085007040041d1242d43c10010000d09108100041040b040d010b04400307800c004442d96406014500000e200000452807400106040003048a4030002d00c207804902d00ba61346007485401c548250000300b44100000b01d02401400c065030b04c40ca8000e000d115060000b1410071a0440c1240f680b1402d50142100d100c00580d004201010100e00070740b004202003039a08001801c5201130108041040007802042c800200300c50002c003401c00c0201c403221f1f01c07a050140054018440c10040d803109440000b400160b00403003516081c501c90040301030f42440d0782d86000f890700380e11088a14409803d10b0000502500740110003040d144034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 440994838 1250 440993588 440993627
    0x3020a09031203020d111608090a08030f07060b061c0203060d02090a0c1209020a15200f01050105041a0928021b0c10030f090611030708010f15 63
    0x9690b03840e0481841405824103000a800181c4503000091038012207407034030421034115180c00303600403041c01d990102040c020010326001882940796a00c1d522080c015081e1002620390b140c801d03544803415980541011500301c0c0c14403000a4191420303000703441000801d1040c1002c0c42190290b80c0700290f000a0042e54010145000e000141e2203550b941c52240d1b0040c080001c01d949802405020b0b0b43c0d030220141c00e428107020500c0c0058544000c402d04a03601181000d143d1400c220007030ba0020390940190000006100450b02d4001001611603e00380c1c2050003000140d8075641030000f992904d0480050310480641c0f010307150b0600ba08480d42c03042a441171502c0c01200490b80c3c0c00f8a0100744006946250003043c8c07000c90301105240c0c03958245045000b401d81800034408030f44a010424400c800b450b64a03200841c2c0c0310305da40c014100c40c035441007042000140340c100354032240d0019035203200025481d50000c5241081c103401c483c00e641c219641d030400e10b12a14800c0f0380505003c2501001715 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 440996088 1250 440994838 440994857
    0x609010e0f0c19122405090c070219060311160f26040306050a05220501110403080c1c0203090609010c080304050312160905040506010e1002010605030d0903021003020a 74
    0x4000c0344886a20003210782c0d0300c4030044004c1107401019112403400c03d0401d612030075804d14481c0d01026803c2d0480c0c030242c0da202d040307540c0c6401d00003440c055030801940101074841c2040d00400b90a01250036204552410000d058945c2000585c9000b00c0400001c018048800200400d0b03600711072140c400d102e040d030b500ca900d042e44002d54038070140b6a4a4031440002081c1031003000f030345020380340d40300f11a140d04118074a41000d40800d480c0541c003032125241b04c1c840990013844021340110b00b01c2c540c128980c903683c540d03d1409004990040a000419000700200340300d011040c2d080d0340751010703110350003942080c005208000b8a9401490240d05000b207101800c3e001880704405184a02c1c0500041d43e204d40071410302000c9000000c01800e01490b0420312400001e411545100c250b0760b069030001100d554100040e500d50503644440303030307102d1048825420860340c1500428290744040c0c060f144000c0d04580292000e407810700000f9801141d161300786031018800d5001d0080044107240480d41d8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 440997338 1250 440996088 440996107
    0x60118020d0e0105011703070f0b0402150f0d060e090a0b09030d060f06091a0301090f0209030a0506070f050f0403150209060406030605030c1c03120e0f150609010e0f0c 74
    0x102ca005a00540003a51550f004000c010a901100c1c0910031903030b0090343c075060b055911020540309812000700201001c101081c2507460b108140604038020f544c485540c0c4000119800e802d40142208810003810050013040c03009001c1c4d80c15018001000080074a07602c20364038500361190042c56002c0030300c400d101c4c4c2c09a0719201d01409006280301c0e400b084000c2e041c880024143c200980046020340e10084860f90361041c40d1003142c0c11580c000c000060700d03865a410900280c0f052001c01c580c184600040d0409000f000705001d400781c00c40b44c59005c00078940b0302d8251640d00515001420f02002800b003080401c0d40c0307007103d151124a4000c018609103402c2c00150b1103400035004540081d41e202c006000b00d00f41004480c025000440e154104072260a80b00004162004001010000e904854116022094100401d03005241c015504000080044c0b2a030369a51040400c840303a912002142060a041e040c19041e6560040aa0b1950313481c100c050142c00c0020741000f04115007003000902 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 440998588 1250 440997338 440997341
    0x30c04060b030108162402070b0a03051f06050906031308030c0c150c04030602180a090c1202031012030504050a0b0c0607090828020303070f03080f040203060118020d 73
    0xa003061810701038881d41400d4405103003502c1c109100e11913070815a0148038007114030070032030f00b9107144844c00c200c2e00040000407820900300380d0107000c1442010808541480e01500880d206001400409980031421505614150301c01d01c284800303c0c0d010842e0520341d0400f440250350020300000c00750701c0240103542d400040d038401c485004803118049001c403044074061021031030008035a41e0140c3c55080c42442d4211070320030751100911850b030000c0c90150a21b80e18500801202004048070001552021290068000c2c490f941e800640208803900801d10345100360380c050b0910495100016007020150f00c804540c601c419003d000c0240400182551011203c0d40901000d150294984001412041c07034800098035030010b01039554018082c4031800107050160001a1801740100f0041782200034202071710720f40181d00750100050a5090004504007070070402d02c03d540e040c0c06035480209400100b40c0943d4025070641042c00104261603004407401e0440c030002c80700610f4010b0202502c0b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 440999838 1250 440998588 440998601
    0xc1c020c0303070e09070206011422050702070815131115070309090b2e110f0606030d0903080f0d0f05071e090f0509070c050303070201141503030d0902030c04 70
    0xf000158003400c60301c01401c01d52100d94010f210b900040c80ca5504010440c1003c01c44601d0003030040c1c4044080b1510180d0900e10918040c801400c03c2100381090305c4c1c02511005240651070182c81504009c103000701c0a101b040e4400e02034a0700c1441ca040c0703156149a10044000310f4690710640c014200003010000c07130000e0050500c607807140390011703103000043c030300ba6980030010a00c614840036040400d49009a619812680e10a01400c0c1903a21031f0300550703059582d49024604c0b4825458a5204108001031681c01170800320220340301e4410340201120008042c0c00010f00b004820701c400e0030000c81d41405000030020610f4041240050305405008450b401c4801d40009100b82da070482000340c1040c480544000750780b508080580c28401c0040f070700011841010b02801095001590391442002c41101e86a0301400780c0307030b4034140080700078060000814119115100d48012400c02c0e1b846040000032514050042d500340040c075600c15008110644059805000308158520595a1441080b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 441001088 1250 440999838 440999851
    0x6060a090803040f030c090903020307140708120309190521040e040b040b060306061e0d06020324040b01140702040b0603310c030f061103070c14060c1c020c0303 71
    0x80c0c1d5052546c10320114032000c030f038404a178203841c1407100400f00307901208540c0070702d400001d810040d400e1030035072910f00309190b031000c0e01e2400740f070401c40035007460040210300440900302150040440c4284000c08503000d4080100f203588030700c5121181800103043c052109000c03282c4613007099510801010000b9080341c048580c01c0d080c4003041308000014890540004044d0001c054600d012404a6601c0da800201640b0084a00d001c0c11640d40e82d40440e81f4810b50b00c50025500c908201188a01e02164003103041d40c1181035849007101c505261042d021443c078140c1d2808504c0440c6d41300c0070459030143c0400e0342c02c90345440f81d00c0e915480342d00085008403880c01d15554503000440d0440c440090360b0407060504c03a40310300c100340403481b1034001c241a41e2700007807400390b582010728000c80180360702c01013881c010402004007c011608050030401c454000c591401d40c08882c040301944450080741e83c0c107031252040c4010310923400310354602c201c41c1040d0200140750010300b007102840c6400032240d6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 441002338 1250 441001088 441001109
    0x110d201c030b01120c08060607060608010c05130e06060d0507180305061f0e0c0a1209061a0603191a03030403060c1701030809010c080405180402120d020606060a09080304 75
    0x1c060965030b01215050188003140410880c661740c460004100e03903405003800d44902008200d44042c403203550700c0300004280036002003007000c0c26500d000e0881e41100c1c0e40d41e860640f103007a000600c2100d40c000103100d544000d10041c40c1c024140c8207040205030107403001c0204103a440d41c3e000721121200094004c1c42c0203000512103840c02007000404c0420040b5a0701640310a40402c00100303960014076a00900640e104603240e002ea42c00c11a141c20100c19031210690820320400107102d042e620600e0008400071400520303103840410b0081d148810748070480a006501400d001d8281141d00c0070302c00711503590109614140004c002491600f00760429204180d41d10110404940c00040b01c0c140680a0b40d00c0042c07541c03558540e10940c0c025069018140000c0075030010801900c44100c0c1c024010044c03d042030210040d00806480034201c40032401a20a01100c00601e40c000417403550454150b030040503a9510501403020030340000344006c0c180250110081200b85060001d0800f508442e4030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 441003588 1250 441002338 441002351
    0x4030807110d0801150c05120703210f0b09041a1b0c010e010f112d0415030e07080a0318030c0e150105030402130b0a09021603110d201c03 61
    0x29030750017696035041d03d501032009010020b0006403020070b51a4002141120703441d1105420309046e10062240214008185030082c1c1040e00c1c01e006900c04080a42002010401d4507812024082240340645001c0c10300c00c08069410100300c007401c0c1040d0b120750320315440300c01d1071401d01c9c40b10825008000c03000307035a9441b03c02a181608091045201c3e402d032099003805400e90b8000048006e02c9007407905c110191021440c9410101007240c0c0c90040c0a000103d0740d0b0b11a0f8031041a003038040003042403030010b8207040002d141c41100107641c0e81540d110b01c000d0911040c03503a46c01e99504210140d50400002823141c004089a80300042e81c3c02001d01c0d00c4071424518000d50f0f090034081d01503a009040c0a41070040c0000750f1075017020580301c000c211a0001318503120100165001086601c048507807070000480c0d815071016404c56010310380c40794540c802140301c00315040b81c4889940141a0000722100800c40541641e50050903141d00d17448141c8902c42115502e0741e10000f508544080802d49407030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 441004838 1250 441003588 441003599
    0x1504060810151202040302220b150318010902030607030603050609010c080609040510090c09060801020c060601030504140d0509150901140c0705031014070206090604030807110d0801 80
    0x604007544907031101c0070050032030300b0854004048801884250100320560005420f400000e6044601841e00103100a0361991042004207218a41c4098440c405060168030886401c20302c0703460030000012090282195107410b101100c281d0500310300d100540d203890304400541c40c01e210b0a030289000e81e6000c1640390450421510b4490007070150300c0e05a2408081c141c1040e4011a1a85c002c60b08a989100940311400c10901d800d5558040944091030403084030100b216071102c2500316050b42d90107218190740e0301c1d0024201e02800941b001b45401c200c0c0000c0c5250311079400268028032039403503120b900d0032099100d89055400c5401c440410b000040e2a41640344c40c419400310050324003102881c21002ca40002c2480c0e105076400d615508004c039449502c08801d1090034003034400a42250f0101501014032009081c50000e0000003029200225034514400302d001c81c8a000b5030001041141c440741d030201e44000000700101c0411028118504c0c8003401402000c240b0303801703513440680f03650518 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 441006088 1250 441004838 441004847
    0x705010327020f06210613090302100c090e040c05090a05091c051b030418050f01031b0b0403030c050706030c02121b0307081e0414060a0905150406 65
    0xc00001020781d006480049103034081e0300c0200d02541e0668000c000515800040780c00b90048403049a0b0000580300400c40715841c0700c89803485048101ca030448400e50241c0150200d031031802000c1d0041c0c01c0040d1402018003560041100c009079480c1c826841e0f90740c0c000b00c805480c01610300300c81c120b01d01d0b0b03c100850b02e0103205850300310340a10b00811403821720001160791841c0202d86000c0300c1810540e040c0e9594000c10603580000d05240c00003903100f4008100726260f900c00c1c002c000112800062200c541c00043c440c20344240341d8030307102c4030b40c43c0d00351346550300c04031680f02008809003c040004900001d006000d04002c40c071a45403000600d0041c41d02c1d50401d08250419410103150103050034005600099940c1a040c840d01899904c0003112030030980a04217844a00c101d1100007190402c1090b4003004111540e10348041106108010001c00b2540c45140305820610714809810100c0f0b1034208020184c10900f400c04100300c56031600440c44800701400e48191301c5201150400019400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 441007194 1106 441006088 441006101
    0xb1e0108061203160b0112120815040606122d09030201020705010c08040b0f01050f010f0519050417012016210f0309030c020909030708070507050103 66
    0x10b02d801141c081c0c100b40d80c21900c0c1c60221000050802240d05111f0b09035a002412103508405410700700c03907851000d44040420050391201d80d00d82c0d50b41d4424540106440d449030324002d408000341404995110003001d05140b500884000c080840c015044020061118009085100d504049009002e8513900034100d611f051180f4504541080e210392046109004944060b50b07580c90401124000303203d0190009060140000c4640c010071442e050b000c1d5610b04103050069502c81c5c0c842002c000002c0c40045200001d080c800ca0030701e205054540c01c0c04c200240501d10751483c02220400503080305200044003c5600034481d401e4003460503007580c00c00c0740181075803101902c4e52040d030500302490b07021801000f03500a4060182c00b03130b491050340507180d400201074141c00f84010920010f24484903800f04024070400182c182c406000494000c2c001020b01e24106000502158031 = true := by decide +kernel

theorem cover : BRFrame.Cov 440827338 441007194 := by
  have h0 := BRFrame.cov_init 440827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 440827338 ≤ n) (h2 : n < 441007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
