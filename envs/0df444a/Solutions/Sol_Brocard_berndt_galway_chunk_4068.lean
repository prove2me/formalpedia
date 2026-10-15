-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4068
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:29:02.181035+00:00
-- url     : https://prove2.me/submissions/ceed9a83-ffd0-4954-a273-7cafca6ea97d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 731474820 ≤ n < 731654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 731476070 1250 731474820 731474831
    0x3031809060f0a12151e0911150d0f0204080312040512190f030c050d022506020301080708060717060310060906090f1e0203100e010906170a02030705060a03 69
    0xc00503c000b1890741c000c4052001d002c100704208200d0780c0f2200c01c1c64000002c1031100640890220b268200040403c49446a507460050305200200c80010b4111001803c0e0f05070b4481c03483c41da1091640010000e0360340174200f60980210076680d04c00c540403122203030061800c14401584807180b03030202900a40b05485501b40d22000016420024030701160340c40254690f880030307104080c14917540d004140062518045650007102d4000080b2102603a0040005070b0340c1002042142d2071018081c2c9d01c624a080005034102080f4442e401141a41c0c040800c40710050f50340e0380c00036600c0c002228100006541e0048bc40204202480c426030400402002ea446112039140000f044814070b50000104588030681000800402c0c4216000407080b901e0178051141a18194440c0c00180d45152402c5540000055407040094519901902c400e542100d075a5a5441c0401e01914113401141841d0a12410050415a0014900b0007aa5028000c0c010441c6444100549608201110400e058454 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 731477320 1250 731476070 731476099
    0x7020127170c01020a020a03030b030f06010621020409150b031e07090b0313030f0f02070b090d020a0621090f030c0809060a030e070b030127150b12060303180906 71
    0xa001174001403050364002c0803040c01d1406c0c010250b40610b804140290407803e07030a0105c40b0003040c60345c15a1001d04004003074480c809405298540a9194144500e03c00724000c07500548a4100c0300da01c0c20002c3c211205030740c4807280f196403440241c0d51000c1c05140400b02d100312004100181d80d009080317082102941350703190401c1c0300136070080300c84e0034200c540d4001c1a010540c12400031744045030186001d204031454000d0196407480c09002e00e0a103080d02003183c1d10241c0e100c103c0d100701c4a07400303032100c52000d5507018080c01d4140c2c1c8800740469200740000454000e140c034801d107800c2940203030710408a2452501c0549010801a0066600c10300c10095500651030f0500100101145668001070030128104864100b280030342090784a51000c000410401c2010101e07103e2500c40c0080d400c2020041c03a4040000b0401000c032a80001f0040320006142c1070528042c00001c881c03048045031039560003040580302d11a0f0005030003ca0521740801030342d42044005c0540c40700c80540703000b8174110301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 731478570 1250 731477320 731477323
    0x3030f07030305060406090c0507020f0f030a030503071e0c0b100306020310141905190f14010f090e07030207030320091306050108040809011e0807020127170c 70
    0x2056050700429156418421181042d10a074801049440410031001c0d0404900a00d03c0c0b14500c0d001c1d114500c002078100840da229004202d000340e000341211881009031401800c25042162020003069403400788403501500d0420060f5540e1881d520518070b128a6a603888002c02d02400c04000105010004000605244011401504011a006406460b0035011041040001e0310070340900c0040814480032107075691854152042150224907014007104482720b00784455100e040c005682c8040000c040c0075840038040498000c0e40d80f1082c0d0170410780103480c0304003144504030704007404a0015040303c1c4a0341c050300880d44a86030208640c0c0c1003101050303030001c03042c00c9600d02690000e80082c01d440e11a8101200c40022103040c08090300e0800080c140490091014009090020b0901c0301a8400e0789a88600c40ea50820100c0c240c960103001840c8000031030b0003034050743c600660640d04801c04040c000c210540c9800c03c413490840ba903102a80c41c03030403403009810007806110100d0030140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 731479820 1250 731478570 731478577
    0x5100504030516080d0b0d0b01211209030b0f04031d030a020409060c03181101080411060d1b1418060f0c01050717190b0609040c020708060f0601020a030c0203030f 72
    0x30303298141c0c80e0500c421021741280c0e007800110348540101c4003c0741c0014000703880c0341d046665010405000340d0a000340c240c11000521402003d10300d07680700d0700c042d56030407011a03802d41e030007a00003003516510703000c1c070444e4480251000340104c1d6580c81081c1680028a2019804000140c1614030641d40f130350110f416075031441002c032003068480c0d80280c06c0ca0b52512603482c804103500c0f03003203003005031580b9610314100c1000310060410668200060900900ea1030408614501030700640d80d50400103074110040c4440b1a020040310303004000000314a1248404d14035949141036001e18015815002c40c00e5140c02c00c040c56004401840031040c00c0700088050312095400d01c4c00410b061800000090070380038141c8000305100f440605003c140d0303112020211140142c3d050010b00c588900c1e0004003117000d0010404c0c0e002d82004c69444c4820381c0461480100e451000403100a9210140003025030141241c4c2e850050740580085030102e0700c24440510300c18000340503a8680b080c2054910000da0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 731481070 1250 731479820 731479823
    0x40f15060503011707050a12030201020f0f0304020901081b010c0c1a0a0306240e0a050901080a14030a0e13110f07140601031101030915050f040b0f010305100504030516 74
    0xc0d008001080085140040032030204d4000000d4100340c3e0a01c07002951001407409140441c095a90ba0141010f00035070440350103070f03010214079403201c4d242c0b40300e9606ca41c02150101c2c01600c0800001807800c0c400070784108480b00c1c11111940d00c1285030011140c0c20070b945001c0e54940c0d0f00d0000040c03d003011a03103802d04002400c0301207598074102c200240c251445a40400503695501c40e5100c401c1d80c55800c00c108444c8549081d030800d03215800054098000e44d04001e0348050308000001e02e0b03003000120070070510712810f007000c0c604900d80c007c0c41c2c513405100501c90119209031a00021842c0c03900d02001c142d0151117002880f5070b070b14041ca0040e80c10050a03a2920f00300000c565061252041d903240c041580100101910760640d03507140b6078580b0340e0389054181a129118030b02003209030b250400c400e50300c0313403070810031403800c1400c80b42600c2055074165880c10051003c560020160403243c0d060f2a00321004118151680c03460a0040200800541c204130003400301c1212901500e03090568035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 731482320 1250 731481070 731481077
    0x2400f15090909210903020a1502160605091509030714010c290f1005090c070501091b1505390601030c0b0405090a0b0a0513061401030c020c040f1506 66
    0x42138140b000300d615655030700b1014002403860800c01680ca440003501541c030400510810048071b00c40c2a46801525a29002d00f804103010100c1c016602030302801d04032100b111708580040c03205140680a01c201e5014a815400c21b42061000541e0286480c0c420306062412400710a07047c0c460914007078a105071910351900201442030810010b445468006115044585441c28905002e8012440300c0c801c40e0b0091840100040100407401d0031740d012242c03c00c0c000c0c0808a810f24040a12248142c225071750050407032030200e00d69000d03848000d01840c003034890301e1601031046802171013101c18400c00c0160110405020b410081c80c0241c0280c1c40c0940002045194194542410707840d1468000d81c5010364240030800880ea5500d03c07003a0084810303d03000030031901e910b01007a0406071542140360811482000184c440e801c540c44903040b5030a0008642e110084100110240c1c0c00d200950320040c3d019041c01041840d0030391150701c8d82090850700007003d500d41251050604000d50011020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 731483570 1250 731482320 731482343
    0x50309090a090c140904030f050f0a0206090708150103030c080f180306060316030201050903030c060f070f050a0c060209030a0b27070308031902400f15090909 70
    0x400200c1075560f0082c040013010010309046500100707002000c001e101400b0807071030a9108950398040e4040380c3c07400440000c030340ea0b00c281c40c42c4d02035940d01051701e00e2103181c8111840000c0786d50000c5031100c5601031142c48500396034030f141c074101e1b10b00040c2c85060700c40c8102003080141c10141500145000345540b903064105212410800d410008028400c034020780101512001079501d0745415400e07241d09003011915001c81102003460750144509080180c41404244101c1c9600390f11014400e080759900d0a800c030f01800c004a9480c01440c1511001c50450704d07145d000101242c0281c40360042c090200d036101003281d01c5060202d141541c030503e0980000022541c0c0b141d03104510010710a40c10014034502d4074590b039042d41480002e0003108550405020b2810944440d011528800c20300c0090500724410340300407004000c80781c401d017211140c0143c00c08003201d04407a0140b0403107120450b0020460325044035400d450b0400300c00c050070403100481c0460302541030311134800c1a0f40204030070f010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 731484820 1250 731483570 731483573
    0x3140f0d0603030e1504060c030c0c060206220c060f210c090e0405030301120f06051509180a060b03150a230435070f0b0c04030c0e04050309090a09 65
    0xd4a201390340490061201d40101e0b09290103d00880c0c0072210075282400141b41d060508444050840350300904064513100c1c0012001c0d03002908500070241034100314071000b0001c80c40b06941c039018000900b80d0507503490811226008000b120351201c8035041100c500b002c80c140102d03075040341c0100079014540c6c0300078503d51542c0c0032a0010251003800150302481c107107505d6855490105100d100810040d00052104019940440300c41d0150300002c18400e50603e0090202c041e00f008180a014180c4100010042e119103160950030743d0841d001b900a039441d9445500140c4550410507030584585000d010103031112000e0907101d040a07903030000381d02201c0d03181d54075000e011613070612a42c031452013408046030140001003158000741504410130300c9400ea11a0300c0c2e0002d0741000b0341c410b5011400b141806607808510a00d68030851401d04990307104a07148039940698040074010442c24041880f1b1701c60121034143d0404e0044084900304131f904070004e10f005600321042140161590003400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 731486070 1250 731484820 731484827
    0x60903020706020712050304050607023105070f0c030e0301021903020309010f0501030203150405100203040b04020f041e11090901030c2103050d200327060108060403140f0d060303 79
    0x2805440d550700f1805145c10341d80c0380c5e1941e038040c5008551181c20001451710865465000000d04903015004c000080209404140c10300c09100300f00024031818000024074240c031070100c4040c980d00ca902c94050071001900d003200c0c403541540042e070f01503608100d0b0703504c0202c03059441540002a9680940e60340307001d124040c01d54030a000030070503a034100b0300188010307030340481e41206000904a03040c6041d903440c200149860740790110054058070020070701060114100700c0c24400c600984102c0101d2003400140000c4882d558050580e0b000520000480c00c0082c0d00400703902c1c0b100039101410100c40302c000030904842a8421076807812251010051a1341c01c15054081031000b0703210300d0580c42380b601e01408501c219241110b01c1035441d5021107410002620310708105286006544d200e141880b2558514600c9410700002d24900d1258031300c0000c0c0000b0034034183c2e00311401410b01d40e1075956081d124040301001310b03c5100003d2004468500010b005409002e0090390082081c0d0302e03508025 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 731487320 1250 731486070 731486083
    0x406170f01050c0a08091203070521010f05060903010e070e041407050a06030216050a030504091508100c02071806090c0516140a1a0402030705010516020f06040306090302070602 78
    0x340026410708041095080007102958480202803c0804440d5100d44400d4180007040c480101103d00100a0003685540702c00a401c080090b084180c1c1103c0012042d448101024031507a14120b055460134000b42c101107015000244016001142c02c00040049908200e42a08502c0d060031404040000740500484191341c1e101d201c3c1c3c06040100e0400c808191250a00d0040b0401d01d0380001d607170b001c03c1c40a000b0440d5890b40100030395034000300919008145070301510500c00b441d0709104820640c580d40240e50f070100d51580004144501685080b240038081c864981d070705501848400144841200b0319170285041482c2000070403d05006401c01200c8034440c1e00740401806001c107910840010142a590903002010340144103c5a4139a92815420350710040c4250040f05d44814801d11a0360f00c80e020324800c4082e640c00a846100440e514000c501000c203980c4249050000541000d51048004a07005000c1d14a816200d480d940141c0f03558190403001a80420010004603906101c00d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 731488570 1250 731487320 731487343
    0x1080a1205041a1303050105090a0224030a0b1504060c0c14010e1318060f0c0c08040e040302070302150d0b01090b0d0f0e15010602060717070c050c040617 68
    0x11070900d8108100124008000052090103031000940401300080c6070400f04000c40d400381c0207000e85e180c1021042d172030f0035140c602240a031403e40c540003495491000003002141441d0401415a50f07140d603401c001c1c210181c000d6811024212005402002807001800644916110006000c200307141c61a0401020b80c03002106000300368100860342e0744801015004501202c183c060000118040c40c02010ba042c3c8901d40012583c61000c104042034000c50441104024200406210520240c4502100d603100a00d0880200307c1448150090200360b60018002e02c11200d1403526076020030034000441d00c40100700c01012038002046002c60198000304a020318104054a140c801082c0c12801070740545403915403944142c140c289019031000d0200300010080320f079440191030500508000a000c0c04006014650003c1d5407103000b403102c07500c44540c803000c0300142c2e03481c0b07072080300c402209000488460040310400b540315034480c000c0b407020304000481e81003c00910350b401850021142107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 731489820 1250 731488570 731488577
    0xf06230402040e0f2e03020a091424030a06090204150501050d09031e080108060a0b01140a20030a2606100c05060a0b10180b0f1201080a12 61
    0x3d014000700c040c4080d0700070410002412032510790010742101444188407000d0400c1c8030518a941450784540c0b40d0301228000d070b401e465219114206081900d1801424252008051020850405100001d19189843c4407003998a8000d401c0000b424200c40780004e5481c0c60f218040c039001d40c0340500c40c80080800180001c1855458500060514060301101e0303030b00ba550b00c1000c0400d2500035003d21243c501d1004000d0400d1380100c5024201440a0007180903520401001580000c210301c20095410b0b070584403816025400103003140b2507800481104100180d500a4104000807040d11801e204082800780d521403840041c02005008041c8410b05c814805d4201551010342c2c156840d60011070966928411a000c1d038415541240703100d00041091081da020001024032507401710210000031550940c0e01841610700712804007040c003401c4040c1c03c0c10042001034005210003020007000d44000c050800c4001c225046e0050000d0f0700c4003296405c485c244c24100640003030f40107407150302402d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 731491070 1250 731489820 731489827
    0x3190c0201050f1c0f0506030c0f0f0d140d140f070c09020a0306030303050c1224060d090204060b03010b030a051008030a02010905070605040308161b140315090309060d0f06230402 79
    0x80000d0303440103001c0c0028090049070302c8a40054544030300b003c0396644041e00602c40f100c06032600150a02c008129058107010700c1110b925107510601d00a0003844109000314300780300d25022139800c1d6030311004044884c0841228001084e882074005010240c01c030380c43c001041d5141d0308000d016140000c1c0311001848040118100c500184140fa0350002a184d0080070b10b40b1005006000350f42e91720269a50001010403000701ca1626500006e0f80720b4401d403014418990b5a00d96807107140028040c04034450418030020b03505a48075031020740d000c5609880244060b945a005604503804003100d200103035124411401885810002880140401d02d07003207140c14031716101e078149402000010a49240240010f07414802c41802c001c1d90200b00c0f000281c1195500c1c4541150f013580d00b040306002e8000c1c0707a141c820419010003420301c50300c4d041d400781d803800b400343c2c04212586d48802e185004950740c0c0c1c1140300000c0c065104100190101e0080340c02540002c01005041e884800c0745548181d0042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 731492320 1250 731491070 731491081
    0xc0c0b0f0907082d01061e0801060603140a0b18010b0a08013c0b040b070501140f0a090203031c0203093304030c060e0309011103190c0201050f1c0f05 66
    0x800e891061304a500001d1240d11034096074280500802e52081040c4411a0f07585100c40d01e00710001d00440d1040c0000308006541c50205900b070b2024460700e80042891031001800c1e00d100d58110021f100001800001c00c0b50780321a0780300c0554000c1e04001201d60740403854071101c0e80c2013079403603014184803542000009075000540c03800201d01400761050078808001c1c00001a40c120700000545807101c0d003181c40e0798a804500c1101c3d00102410394156081c03c0b00c9100f82da607402c1065010302c580e0a20050940d481c1680c50014160403030f0100d030180720400042e09501c51001e00c3c0c01515440007000b507501d040c00c0000610308085032800156610780b40000200301d4220018000005a507500115039a80d12414290b92034504104003a00e03860034000810340402d4013000a198440c4242c03160520401e0402002c0c1c0d69010741810304688610040c50f03910010302580150702c9403841450858a4885440084140350304000c07003201c44108a03043d00c04c8501418080c1c0407040845d0f000410652921 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 731493570 1250 731492320 731492353
    0x2701030e061603090510090302010906050a02091f14030f1639080706050a060b0f030402060714100b010813050c0d0303060503251a04090c0c0b0f090708 67
    0x1880b90306143e90f0309414070402409019801040340700c0c0b14100410260f50074064068802c609084400c0c070300e001300041d41501a8403da640d0b07030b40f01401e2400b00852080c0812040440040d2910900c184020407040100101d00214400c07440844411041d0420843e0b011080710700388d0040b42840310650b081c00c40d0040841078000718000b038444201c90074003265441040d50b001240080c103144800100300041c00242d4100c2801080041c0d81081215514030319800240540c41c40c030040003104002040142c074000300607006a0b1300404183da9603020200d40d02e842c01000c030458241413900c40d11140304a68104801583c084481076000c04151610358815850340740300d040c250311a0000d070b040c8400345846584484041c001c094121550222007a01131452b0101080c210f00054402050206144011803200c01e00d224405009508150400d0004005040c02d491418204482c2c1d20307208001c107031502002070041081d0f1843c1c61141c1084600b040c1090781a400003112680001000041d1606 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 731494820 1250 731493570 731493601
    0x40c02061b0d1d15011a040504020315040212070215160c030e030f0309031921030207050304060f120501050901120f060f051008070602212701030e06 66
    0x5200041c140c0da080921501001011003080c40070020450741e000d1000c681d8001942c46141101c00c1d40c0c10356680e80e8440e1150000380c00e00fa01e90030124203020030466401d06402940d0409842440c441c142c60074031011a049800c08540550070b80394802c1808400d0b41c042c8030f40c010180c07850801c003145240c1555101d44886480f86c2050401000c2c40000b4207041c410001002440c90060a40780c0011008817035a41c1e1780c000da071000d8828010700200c076640d803200050b0280e0503603101107095030440c000060310400c44003900e441c10501d80c003040410b0008405200800140165450b14880b0300d004603c020b024040408070030080c0c03032501005000395522656030904440d0503101e2001e4a8400b45010380846030b0508004020604101c01c4a01d02003054000318840e0004000c00310485d5a64400d041e500c080600c60a40035800c401d0062070207505201160304051300c8112a01c0c50211280c3e049058102c0ca0390060340b001c8a0001301040d02e680c1402601d40100c480d0006000398184410f0419803090f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 731496070 1250 731494820 731494861
    0x6070e1e040c05090a08120711040212100f0512070b0a20061b070b06151201260a03050315010302040512061f0f050906040e06040807020a2103030e0309030307060605040c0206 77
    0x7009c1000c440c0360740e80d494040341e00c01c8295480c0d000b035a05246001c05940195400360041a003107012000c501400c5c428880003240b41d040008000641c908451a0701a0344a4a001d0701000000d40c07840c440240c640c0c00922081c0801401070903d0303d4070441c42d00031340049a07040c0300301540070070a2402007071001c00910b0704800d0458084081d140300681d00c804510803107070458682c007880c8000080d03e0011500080b00c1c0700b0f814441c0a400e01e80c425600b61038515044008000c9031092010134034414410040e00c1440364181030043c5440c6d200c02c0014039000c40c07184804680c0d441301d0308000030391441c1d54a20402800c00b28a44400c113003800740408c45080d2600071a801038000500060701c0d90ba6540201440e0b8005a081d1441303404d180c1030244030703940300340d900f1703409110b8031040001e1034045142000e100c40144094008000c0150b581240038050294208449200902202020703980c24402000c00c42c0c8149400282c461401c01030100b0744040407650010b640081c4100800e05070b40004022009 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 731497320 1250 731496070 731496083
    0x308040305060a061521060f090c03050603070303141b03090109060302041518090216030206100e06190e0a0b0f06030c0304021c23060906070e1e040c05090a081207 72
    0x6d040040307131b07140d0f070324183c03607140c140e2508041000a0300c0e40400c4021042e034000d00c10522000200300d60542c1503890a48245030980d000300c5c030030004a4421096003100781142c041c840d141c0b807040d0605641119103481c5a20298100003a108010368000326010700511103824207500f4140340505400c420514017071746400307010840410110000120450300b0141030001411525003103070554034a8940007140b4103d000d40b094502280c840c503070584040040741c010100001e2265508802d01c000c0d404003012110701d010800c03001144506921a03264828151040c00040403101c034010000700d81d041c0504a40120410024495200d000c2d40c03c980c0c0c4682c040c2c4102068040d50640707150f00480a01c0c0180202e90710030f1034003118038844480c5200d1400039800316103a540300c640b041d6803201d03019104003001c80e0344a04404241e08081c0405202c42c9042a02444022071804c0850255115070040100050340007a25204501d4044007034406031684000510368105001c800040f44e00c20245c000d04107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 731498570 1250 731497320 731497337
    0xb180a0b04020c0f071508060913050a0506070f121509020f04080a0b040309080f0a020405100f030507060801061b060b060903010915050a0209090a0e07050a0308040305060a0615 78
    0x30741c5a030340448082c0300401c004c4403500c2c0500f58041d40c54500078060b290301d42c041008656841807140451900400700104800c400b5142c40d0400514203094103011286070140004043c00b04205000c0c1300e01c110500e459a03900000b060100510407010f40f080c0c91881d42c5040415603891403107440950659468071401a074a00003034649030040d01440d402001c2902c2034800e004100509142c489009a00c40d40780c01803070310b8907415126210203010f17428112940c410340c030420152a19400843c1c0040031825040c01c60750711a04140ea88080d00c0c4c000744d43c40c3d03100d0041041280c0c3d100300740c9401080e0602d440400540074202c042d82c110ac602e5000f5044680318040658607079291001c03100c1065005000304140141807404002c43d04a422407208650300e40320004900c07100341c0c001c94401c040010400f03030031030391749042d0301c0010441c3c015010341c0743c1b2440703102060075120511610080c41c0208840d540315440c40c0750603898070ba0010600703d541810038030208890040c100700ca516060041c1440b080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 731499820 1250 731498570 731498591
    0x20a020918060106051e042306040b0f19091a030c041d0a0b120d0c0501090b010e0f06040902010906121104060c0b0a0527030909070504090b180a 64
    0x40c84500340740a10601d006440001807880d40060003881200000302841c2003c0340b80d010302039030a0160344203007000400740c031680940c68829170b45d221103001c0c00140401d04050b16000030001940140449420168002510009421420785450b44510381c1d072420740c4501e0306180e5214841c401e81d4500a00030f440c0840407812070700b01c1000b80d40292941000c00b02100d0600c84441d04410760940d40078219615001030361659003011ba80c019441022032000340b0080c40c1006044610388000402680c441d5a03818945001a464010b03190003015100440081d03800e00082414012002078401032055107030005200050b6000b0754050100e400c1303820810b0300607a2030807040c4040d041080001d44102c00001300401d025402090300104140501f0500c000396903a00803201c01c030390041d6103100b8991040600c5905123401c5403043c9100703820394415a41071500803070115458140c1a00c00c50049540418248180c0c0c1d42071080611110040382d0203075100c8600c100d07603c0803100240104031420744072000c505 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 731501070 1250 731499820 731499841
    0x110c0102090a05040b18192c07030b060618180118060806012106240803040b03011505120c07140c0d0204270804030c06080114091b130f0b0a020a0209 66
    0xb41f044124105019594903010644a10b500c2c0d94071600c00000a000040700480000508005682e0300001c41c0b2050b0711580100f224a4011120f0384c1e00c030f0400d0301c8089180d03440d0002d8003111454800140f02301c039418101d095640b000450f10850880c0c1c03400b0404c104040d0009141d904507008002404c03c080700e501000d0646043e05440500418103044182e486444281600e515040416414081c410348601c921a2a44240e10030901a402e060006101000780d0391500350f6000d0060420a140500c0d03090100c40d018021103d0204030032010410a040c0a1000a020030402404024040c05005200001e10704814940040e00456540811001c01d40c0d11361902034407030108010a41e105000e528203d201540203020481d4034000c2c41000080c1d06001d108058140d0b890703e0081d65201c519041400748000c40100051400302580c50480d40e0100c0b00e0f002081c8040d00d0601d5401c1a60070a080b40284a0f510341c007030344400c0004c0106546c0c455010403154119a0304580e00140b46d2608103000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 731502320 1250 731501070 731501101
    0xc060118061d040506070309022407050708030702030c0609010c0f061e0515091b0304110907030902040509030a1715040509070e090a0c03060f110c0102090a05040b18 73
    0x403044240d07030b1070128401000e14401c43c0320324410001c4810325038809100b01c0543e204000c00940081c0324154134001041d80030390080181090010300c0b41848002e8581510f0050690700c1001540c10008000c025403c05010030350340104103030382c0640346c0010003000030b0002d044640041c0000302c0c91241d0004100003508400668505c041801700c4550546802d0740041006603240d204200038103041000f00e0400c0c45007a0300c030303400d9406d00060440442401040960005004480713410742024580c071142d0f201c49805008040c6580e0000e403403c030754818002101c001a101100c158802c0c840304202e20ba00040060304107000d89201343c199202c0c0c1a0401070b08101001443c2d00500b03000c108900030000082503c11142034602c41c0240e80c540384102c0d070b107400d4801320203051440101700034800300304c2a80009204000c546ca00240d0f0102000c100f05060300121138000e040d940004210885140c42c640307010103090110340400481020740001041c04101042c0b04080140c94400590000c58186d2403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 731503570 1250 731502320 731502329
    0xe1006140a0c060f0c030209010816050910020106271d250b0f071e0809101b030f02011a030d0c02030a06020c0a1e020a030615030213061403030c06011806 68
    0x70300c411076000c0001b0b4065013008513014002581c000010b03400800c004284210282242c0713969140c680e1803000d016140880010030300540d900c0380c1001402d1180036040e0708801018541c031105034882c0c0a4040142d40c02040c01894020100448001c1c5c0f010208246d4211401c0e06524282e00001074080a80240342e640001a92000400e424510791026402412000d00c81c6200040c10b10380c1c090640c004642c43d01018111000510114040d82040480c1c001e101e8080d0910800c0d04040d4051407507001314a180c100d00090038242081c90081e024011154407810b1420007482d0313900c13600d0109980b212599009002c108200f94100705649081c40204440c0c0d82102055554025070001d59540c0c0326000c40072142c441500300c007080c03041944401c040051b80e0003401d0f007100c646191510000b506400601c1d5010038003c0d0740000059840c0c259004030034020100114a140c50140010b00514141c07044a010f07070000c00c035880400ea00800d825049d15a51030010030950089000a001004607400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 731504820 1250 731503570 731503601
    0x10e0d080f040302030f12040b092e1101140a0504080910110d0306060c0213061203020a060b0312030a0f020f07030201020306102a05160e1006140a0c06 67
    0x280c4034036610001c001001034078001e80440d6107140c0824080f039524980648600100e00041c0310170b100b031528880c010202004020b007a00d8410b00501512000600031001c0240ca6649041640305895000701c1640500e07100a8003c104c008170444a0b4508258010407001640e6076460002d4100105602076441242020f0040406030a03d1203000d0580f008bc16a490000e105aa01d8501c0607882030244d0811707a0a9941c80d4040500c070f6600348940480d1800c00c02d6401c3c1d481c2c0c24081409041c0108400005000c3d0f030050003603120f0307030401d0320842c1ca86c01001800303a040320b23281100f40e160013012a500321001540010340c100d00d51400000074042c864041600b018000b802609156054010b18010141100c4000c000030880030103440e00003541c96405184c07400048404001d0541a038600038003406101603c5c684003000902d41c9545e005d580084500031449810701c04500040c000c11030280070303241031007a030000402e4002110350284c0c94580d07040180007800d040400084d9003125403400c42155 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 731506070 1250 731504820 731504827
    0x181206010f06030f050c040302120a17120f16120902030a03120506030105101a090a151b0209041101020c090c030105100c170304170301030302030406080c09010e010e0d08 75
    0x8624000d6540c0030321415001130b013004034039180302d000d80c4500e9000d208580000c0345498a180c0c00c2c07240c89581c003848080e0f0f5010704103103080800c9848a12503104400310f00c850740d548003285e5691890210182986c1c02c6078031303603208101c1003c003000a07a4804402c50f0928441c0ca10710250301030083c0002d40700007034050142035006020560441c10380d5400c500e0211041c4507036500ca02c1130508a800444405085180041c3c0070810000d00d81e0428461102100c642443c0901402c081454514a0b600000d410b03502e400382c01c0801c0d54001c2084044140030a40c101d1a82110303000030703010380760140c00a016030004c00300c2e07844141c1c002c1200008044024020150714a00003c0ba60f030389400c244a100d000b4510f41506080107071040d10b01e0451f556110010182e42d070201520300581d82c000420480709071070184a110501d00b61000914000d5120f03600a40d0340b0750400600805c40000584616030081090100c803c280c2e8000c5070020802d04e00703207000000c12003e50700150003170040c518040c04200000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 731507320 1250 731506070 731506079
    0x2010209100c0b060603070306050a1d01080303070903080d14041406090708030d1d160603111815090a0608060a060908190c031401090303060b04060518120601 70
    0x1900a0086580201c0340311040301c22490042d02c681040300001040d200700d510024009103000700c007071500010986400203a803070b1950040f800c00041904208046270f142020083c9503599814014090302c0000e001c3c5081d03040ca0003014020174074602000301100d0703020440d9524603072154448a540b16000c0014003450401c1c0c10081c0c1400701400c1d002c400390080d5400160f1345840012010100e88015006515007804103040c10700400003807500e10060b10200702108810f000400c044010788008030980d41a180c5406e41c040c080b0b9402e02c0d11320041210070300042860300a0303203441104000fc00e8070401492040c4440010113071107114045a88448404004a40c940d40044068801c450940c1c04042d070701c1d242d245c00d0300c1e451501e1061001950000c4d00410030b50710f4600e082103405108002d20340f003003602c3c1ea4541c035074201920820b000e0381c0c0d981c40d0450141507060080100a11001c40c09500c1d003401e19030000e295100304888038800340c00800806d002030b26510302d844d030403003000000d41b041075844 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 731508570 1250 731507320 731507323
    0x1202040b180907230f03010b09101809020f040b1302130302120303090c2101060308031f06080c070c050612010614161103010e0610050a06020a0809090907090c02 71
    0x1512040340b503118040010520f0031010140c411102100803e25100036021001c2104018014010301e400d55240d0f2030186d0a504d030106903c0c0600f0070900710341e00903800d00a109181c10426050303540e03560308005005000d03885d03021b40e9828258044c0c402107031076484540402d4444080d440828034562000824036002c00f0161564001c1d280700b1207014410f2030914220313907031364001514104c0340d82c0c11010004c581d510380803001c110000f42030440c0e41d4007464400c80c00d6085070300a900c15203081e100001048242034071b03658400b86000600c02110401030800303800401a280080c0f2928008500150380303800d21882286040c0144001401c1c240d8031460345881d0f04044100303115403000b14034202000701e44800410140c48180da8405641c0f14a01605d8691900070403c41c60696003555803001a260302e03040c144403042c0b00700f50f41281c04112514040502c040000c05604c400115000b00340080c00041d800070885502c0d0004954600140c0c480203409818a2041da00c0041428076180d01c510010781c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 731509820 1250 731508570 731508619
    0x31206050f04050c0c0f46020325030b01050924060723060c04080d0e120105090c010e2b020609030307120801090c0f120e1b031c091202040b 62
    0x1074040c012101c007800500403003016181001d047c0c404000402482c5640c1c1c481072004402c45000500300c803100c080c500340300b8112181020903462100f040f084140103021050416a006000564602c070300342c40c08455000a0709440710b003030154a2040c02460500795100419140c040d5001110881c0b44c08882004450440c85009100128040e04c0d00017140c3c81409800e440454606001a1812242c0b5503412581541c45070b410a502081d682c1000011040900c25176111b078210b10024210b28000900250180d030322100c0c0030b0302c0341440175841c03d120002e0400f000c1d8040014136040071001d401c3d1000840a0242c02d09180d01880003007805800c2c8140381440c450f0b140c8050b284c80000b030362900354400c00e80e9134081f442400310350102c008001080c881d82d0501e0000110700340018100f40c0000220f801c1050300b0b000c400004604880000c0c41e0310341840344001d0120400030b0825040b106030000742005042d4410300d19011101501c44055480e030341c0003103d04580c0248905a0401c2e0803641200148 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 731511070 1250 731509820 731509843
    0x30e1005010302150c10091103011415270403350f04060b100e1806180406060b1303120804030e060c0304030f030507031206050f04050c0c0f 62
    0x415a040244080194403440741030700d4025040300182090580003280907800021581110f114030481a003180e20140b241001180c4120989030070080c85004050a45c4c0c807820000c08040c402c3c0090100e00b0030201240046060165601d00c0c8804803051400a03684110130314084503030340103040208050b88120220300c0d01c1850b480300c00790080c600001032860003c004560001d240c07040045264049900351095105105d0040401c110040d80082060700060f42100c10208001e1000240305103060010307422001001e00c18400c05142c2000000d21b040d80d4039984000303110102e8041000e014942c1c008901a0a5400ca0113a0340c043c0040010b60030045840240d82008415042d005124071400e205c50003140c155481d500e500c2604800c006c0c1c00d500140d4134081a1008202c0040044c8082d854100e6080c082c4c0c541940740c00c03003030a02406001d100060021072901d80b5000340a03d540354441907034601c02c1a280010107030b03a5024440324910462500d100e03035116070455154074035000501b002414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 731512320 1250 731511070 731511073
    0x5101401030b0f062110061403150f0f040201020307080403050c150a270f09021b0303010317030403120e06241c29150a0806070e030f0706030e 63
    0x540d54442c0d208207240003522003903400b0311540080e440c0207801440b01d5048503004016110280078520030041101d09550080c001c0d442d006808c0f50240c581800501c9403100500c0b41c0011903c0c141d900b031031404d080101003180c845e1341940445c00b9a4420010388a07055031000e9904e954980324200340b60342d406801501c0340b04100c100c0c03c3c0d00510301440c0544810404541750850040718480c012a400082c084c20240e0000c2011380c00600e0190707019456000b040c460800598903024400051340601c900f051a941c039a0003040108001000726000b003950f11683c1c0403c50b2a81c8451404482035818050340c0c048490421000120b5aa00410114000c01d0000c0b29000000000030b00460741219090156078010032001448083c000d0180d000000300303125400002c500000815504102032010003071214010344d81040000682c42c00415244c41c450880e82c0c0803407145403d040703a944101c0103060b182044002d4103903a600e500c040261041c0040c0c254260384005071510b1005005000d044900e20bc903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 731513570 1250 731512320 731512343
    0xd081207030b01050a0f12140612010c02121e030a0c020c09070f0e18130606080313120f020307080a060b0a050109060807170a090b0901270510140103 66
    0x4030780a84140ca03030011041e100d20341002e0790804241e55248022000405000e807041c0350184d441000e108481c0440c1c1c44401c044000d08020003402640c01c900c2c1d201111981c54010b042800b0b9400196240020100200e855603c03004d007000642c0d25011040d5220219801000784100400d05811802034080b040c0e00707c0b1010003840707041241070081500d848000c10748440844281500c1444c10340c60064024142452803c1d009031100710480341140c40c0740c03402c040140300e0070401005000320002400c8030402507040036410b4643c0d80c2c1101032441803005800901c1d1900b000c01408180030080603030000c0076101d00950b05c2600546400a4420455200385490900700103403400202203c01c3c1c81d01030f07544030b80040c280041a00d039480050840c2044c494460719042c009800c88020741c0c8130f810720748800328510b0800e00c0c1240c200c820140c0303001c42d242d040880d100201c134080010b42105115036220500c0717941903414028204508082c0300b072402e5080c4070301c414410740f0410b095412644901d056122 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 731514820 1250 731513570 731513581
    0x522030c030606060e1e0123030108150f04150507020109050601090618020c0303010306020a020f120d0f0509120d0e06011e05012102090a0b0d0525022a0d0812 70
    0x108038070f1040c1d01c0c00b01c0c100000c9001e40c10754401c11400212034005804262023244120603100e86402c26401812a82c0c070880190080707444541506410039100000307407c15050944e514902118281540d1400e556518001008c4038405d410045100d07030000162800e40d40c540320488042c0055008140000c0c0c001800d20404001901c00ca17001e450640c4090350440e4203540d540701c080d42c400c00c43d1804503c11291142e131400301c01cbc042568400016402c0590380c800104010007503800588a000c240c52900b010001c2c0303a680410f554114040e00d8194a50385da4400b03d01030010b04114528185502c40c820000c1100499039285900c042c44503030413911560f0340d07500111010400741220041036510150b220740008440e030003810324020014843c041c00e5845448034281900320400d40c0c08801c3c2c0f5441402401241120084a8080590040418400c041e00041d544a02860842d601c1c19041401b03252050600c0d050006040700040a00e510403800381070106031a0404480b854250849201180 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 731516070 1250 731514820 731514829
    0x311030c10271b0b0f03130813180c0f0e0d2a08190c06030e0c0909031314060f0c01060f1211010221070c031403120603060103030522030c030606060e 66
    0x801105c4440d4806146607106084615249400d0000300e940c0342040c40742098a000d40b043c81c0002c0c04450000101c142c211801903010341301c01030125003d004100b030719850210740c441080a100309061702c424a160890346000106030044002c60102c000500201014a160701c0030b508044031103100032249030100b00030403020718500d01d0701d000303101c2080f8100401c207503030081e000100e0162500c0300307540b00d003102d0790082403e15404895031056600300050b500200a60458001e02a14140031f100d0200312166022600911402e00c200320b283c14046404141401c003508081c1c00b80c01c040d140c07004141d0303483c04800300a103580b0004031200c2d00c00000140e02544001040709005441100341c00c40c41d118603214000d2a4000c0074103681940f0800c0c0301001151000030074100b98903c0b10001c1d070391803c4c042c18000308108090541c51003a088880100046548071058484038105461203201221410b040e00108082a40c030083c07080300d402800106210349988280c00721000b9440b901d14100e072400412 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 731517320 1250 731516070 731516077
    0x902150426010605040c050a08090f1207020d0c03110a080303090303040809040b0918010605030c2115041518120807030b090c04030311030c10271b0b 66
    0x921861040d0180040c444001d000075205180154000090807521500400c003541c01c003820325030100710000b4082c0091030388050710a6025107181c000d00381071902036107900e4940740000f102142500001c10304209665414215103003003940404020720f050740da0b26000d00820580c941503446058000b100003004080401200e200d0484907002e10301e0355566a40300c2410ba04031110b200c1d0170a039502d0b10044187c5503240e607140a0131a00c00020989a07000c2074841c21343d200340e0492802600025075003480d07a1280c06100702242c0044000e8103000030440130b45460207915105110000860340309000038032041040d000e00025918030309105009040114180850060f40c00418222001c005501483d10a03680319810407010710700421303a034403480c0016101c0501035031140b4682d480000d0030420141c0080d006a040d11002d00a0343c00c03c031840b201d039500d482d000c2c0382c14051140ca990702406107003038a4400c0401c10f222032100c50855449070400c408078003072400d141185c2c0d003030f440d80102c0c5448540094 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 731518570 1250 731517320 731517329
    0xc1c030513030c170f03180d030c0c260d02070b180316030908010c18060f09090203040807080706230105030721060204030f050c182202100309021504 66
    0x840b510303030603a03135034800130f0303030142c80c105100c088050040d042450844c800070740c001c480f015000f00104420140c1613080c180103034401c10600d45400c460740e08007504802440342c500e4000008040d170f07000b441040d4070004500408081c00c0c000006142403000380c02e40c00303000340a0203100d55616035940c0d0012a0340071000100d02c0840d80c0c1c002c2c0801415404030030b40d0207004500c20f05e8400b000304e54840c209800e440c4402e075200702140300b020b621a8002004c8606100401203840c0445c0e011944e00c10140401c1141d00034800c0030768001002505000d540001c4134021903000000954403002424514004d10f122880401420340604d84d00781000f030a503034900d040ea0402005080c040e4030304602c1c2200106140c46007468000c5400c80d42011520600c09000298020074900b0180387c80d0703107001070030310324101c000030310442141041410303030084060740b290300c241448084025200703400342e408140c05031004021f45c46502024448080c540c96004008210310a940c0713400300307000c00b00c10802d4a0156005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 731519820 1250 731518570 731518577
    0x25060b28080127050c1f030e03091c061407030f0b040b0312090301060b13080607050301060e100201090f0507141e210a03031a010f020c060a050c1c03051303 69
    0x910000c0704614050f8591090b1150046802e1050014080780380810400207100d40d01b518001c1c0981400e405010702401255000055850000b108002030000e001e01c1607907165400c0900318120410445512440701800484200e201525201c41c009025004100300e00600c542000c104064a08183c020701c00141c5004001c1c0076040c00ca43d1403038203580c00180b11b0a5140d03403500c8000403503034441d4000b40841c14041e8032030900c581c01d048030240741c4600079001c002001400c0004106951740a03418a106d614110758800c11166100308c101d000d0880e0141c05042d050141d00d4400421800080401c1182d80414032504882c5051003080b0003500d00d07035014100580c014030350744050702c1c1004200229070410004e8542161074424081e10304070041400b10b001c0b80c0d88005008455080f142044903080e02441c0c2144245030a140013500c0d401d0014900b80100b4020031a40e0b011801a829200c91008010856420312040395030b0b814411305140310100030a00c0c00c004988601018803801c00300581585 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 731521070 1250 731519820 731519861
    0x1050402010c020405060f0409060c020f06091002070812130c050103060621090b0f151f1409060a05070b0606040b03040b22050c0a0b25060b280801 65
    0xc00f844050000103040a030302441d0b24903840150b42c8e0b00c0c41031b048550f0150000003004c12283c400070380390900406c0d10b01c420b076100004025680500244911001d041d0400c056160019032402d450f45008407400c0e121140c00c0c00e4100402c1c081850440da1110f40280507041c032580d5654015006c541103801100005241c1152040c86074801c2444408100610744c00000d8151aa84490042040075103003000c040100c42d00340000000c0721021034412180031070b101041c040c18003480c1d017814038041070380700207002c04113040540180010060711101d0300b000d059169903528030303a0021300c998040c44044030b01c2c0c0c031704030003156181c20030074240d4003070b01c2d64000e4661940d1aa40c44d922244280242504182e10ac12807032489101210114400b0030391203103004040043e90407041064640c1d858001c294403090030b114041306c015044041e100281c0200340c1c134202041150a010380a000c0c221002c60300000080c03414501c440180d2208540201c408403542042501c0702480c40c240e410110384010b42e400f140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 731522320 1250 731521070 731521073
    0x30e0a0201051308010c11010c050f030708060301110a110601080d02071a0403080f1b1c03180b01290c0709110d0906020306010216050d0f02210109021201050402010c 73
    0x80c0010303d0b101d20051498468244e407a1042e03401d4401030640711001501d00c0d1a1481888424000c0c1c803145002c0303061240c285005650800303030034040108500308010b043c10109525840a5104030101a0591000c81c0c3d40d0003100300140c1480f1622070700204500c035100c000901001d011454429100782c80e03028050f12854030305680c0c41c0010407240061000c000b0031002000a440000403c84000d01010442d03d910400846000c800c0e400a00b0a40c07941049140c0383e1a0000203a004107a07401508001415012401d080141c0b69007401c1c00403e100010b43c00030520310800d031410f0036601800c500b80008040110b015110034058252804816401020284180740b199044403081407010082350341440c1c00b214001f4240d5410101c281d440741c3c0d00100340003003964144024202c884c81501d44062580c501000f181c1588200c407405400b0914194400007150345d0b1a06040e4056400340302c40c00c4031295800213500034143c540080f449640c4203201e040f041d54060142c00e00c655016180d04034900907a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 731523570 1250 731522320 731522327
    0x18010509060d081b0c090f06090c03090705120f0c0619140702100309050601140a03080f160b090c0d110108370605150a0e01030615050d0606030e0a0201 67
    0x2011500b0f00414403003000600d814020f40d10090305080d00a201406031035040c03001440000c0d2000314802c0c180010007440d074981c03a14042d041045410116925510b0310400340c10701510b42c01c02507001c0d403503411202034000c0008800190811801c00d680c2918060300c10801c292140240107080c0300e1500c2e10b14074045005215541000c0c02c0c1e084014a0248564001881e9000e0600c0140100e40d840c483d0900b840410083d2501600703200301ca02400480140002d0f00150107803000500d0300200191010001c0004800e0366904030782011000102881440c082d840c2101c00c4411440c14821b0507100d001c0e618000171003103001900014288000c2c0200d130300450f01c0c0e103001081e003c400d14400301c80828001e42507a86200264940080f080c0c0c81c02070420582c196811a03011a00c550100c00780d600544000d03000b201c3c1032910341c0c2007846500c2107020043e070251025a015507008181d11050000194118004250801c0c83d01420442c00f61141002d6040b13a00c8165140c5aa9000d4020345006500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 731524820 1250 731523570 731523589
    0xc0305030a091a1b132c2a0703080621030f04061101060617040c0e100611010501150f02010f0e0304170c060702210f0105061801050906 60
    0x724444040307005080c0743c81d0501d42e81d0700a03050301001c810260810180e05a281565070303d8025030b9520381c0c6084101c01079852408601c3c000d4542810b246046180c006802c407804c0c1c500920700711440310301031610520351103c04001860308140c03810102c41c3c0450701c0c2d80784422108c084d030b41600c9201c00d45e103500c800d1043c40b98441c1500c0962511001e2184946c210030000f4000303d0120780c403141d903140d0408000401d030200001609019038100f5409110403600400103003c410b0854080044640d2281011100341078143d00c16000007003080c00740210350080b41d0500c1300f0340e007543d201c080321840c56410180c22114240700d001c844074407040041e8200740c89210340c0100500e6900c0003180d400c442c105100d0071100003100c814040d510005003041513642140c00040440740001c0502200c41a02c004120a4899082c0003841500316001c0040d211203d85594041d6100180171103040c080b21005640c003c100075103d4600c10b01c103042d41d40e401b82c011400180c0c1a030b0300c054440c10039515400c090040007e07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 731526070 1250 731524820 731524831
    0x3080703050d0905031e12040605060d0615090b0619030f0b1c120207030c06031d030a0305070801080703020303040314071a0306090a0b091f1d250c030503 68
    0x40020a45040090090260b143d000c0c130007541d074443c14180c2c00741d0454000c00c0700d0a0002402c1c44250780c802041c001c03441c1e11540010000c01c06654440000301c0d042c40e11580240340c4d81c581520883c00c5905041c00c0b905039110244200000003005041101902410360b401044481d481d0044456034130035009040003441921000c07490315002c4e80003e00c0e140c1600469104411159261024441901028100b106950011381041410758030754410440580c0103150501d511140c3d5501d11a40a030200343d07000780d1a4050326180e85810384010082c0c2003d4a0507000150b41c040007182c81800403400c9401c0700c1e8010f00079840c2610355910b6002280346036071001998010709100180005505071b01e9141715440482443e6685844801c21268502c00b42040c1342ca903160021400c5a912011070950300003100c00d40500c5480070049110320a004550403009000c040d4408000c0c00c840740b043d405020303024102210403555118403400c411804150001e5002880c0d4065403c042409080110f8120 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 731527320 1250 731526070 731526077
    0x51f0b1909050a06140f041805060a0b011106070f09030b0103051509160e06060f161509030804030e0d120302180904030507080f0c0613031d09010b0a0e19051507030903080703 77
    0x29a04230403048080504c10206032003039086101080340a270218840d00d24802e0007401c05050402100b419650b840c60700a100c041808149026032584a00996082c801142c1c032104211096031031b403510b640c4400300020325540b904001404151800c102203025040880041900c1038188c0c5042400300c4900006401e0381c0c0c006404100c16178401821000504807180201c4044070980750742d140259010214003a007104162070100d5080001e5400703803109800130341529040214041c0c1000081640100f4240204144020b2414800c0e064054015103004403010700c10810024414050141c4403038203d80043c006141008030400144042d0040c2c5100300c001e02200f803c00ac0b45052461502030181d505e503964a20110040041561090f07110913010050341c1003002040c48580413640c00c003018060001501da001c151100c0f45846100030a5240710010070041d1200c0c2d004966600030b02e80c40c012240201d05103042c45400414a0045034120f962584e0780c0404c462454550500c65040b482e000c5080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 731528570 1250 731527320 731527331
    0x201020c2a011e03110702180f0a090f11040e0706020c03070909050c15040b03101a09031c11070e0402010807050f070f0611130e09010603051f0b1909050a06140f04 72
    0x5a101c0c003200c45131448c0341d01c1d081030761420400e40303000c00020010b05030b43d8040c0c149880c03640041d20a5152402203072b48000e03441c006c2c1c0b5414000801500c4080103035919889603100010391968001012440c2000980079100f80c00d440e01214800e40d02402000f07091540010401c684608010300c50325a41d0060899481c1800c1c2c0b0340e10fa5014039401a602d01000ea4001e000500141d11280c2092001d1417041c03840314503148400020945641d0041c0c0c6843e00004c161101c2544180a5810f00c070b0000640002d0303480302900c500c02c42d070750584152400d07030000304544000744000d4011002c445410b00107a04241c00c0040710f07580c01301c0c0c61400310030031104161901e004808000c0804007410b0088041103250003514144003c882e44000c00422044103603060010400210700081910340b0090305c0c02000c0d1440c0e01050455001401140c0c1101c0d8011000010814030003006030500001c2d80e4020b00144107070b81700c000020041d01e240d40120780f840281041c424005281c02d044e2002030420140c0301154 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 731529820 1250 731528570 731528573
    0x10816090e090a230c0a060e010e01030b130504060f140c0c2b030b062d1e0a0207090902010f2f0304061b170a0201020c2a011e031107 59
    0x96070980c1c80c0e1a4070400810042000c0c5850038017418950303240130b596441110780b034035200a050440c6541101c4c10f02c80380d50f0a80109910980160f80c403001e001d040b081da41911200d104000300801c85098447ea40b410051201d000c445016500080c0c1c04035040a02c00c0c2c59100f03040d405603000c2c2d480040c540c40740c6400320b018407032043c604c4035054500a00c07440c01c859244502805450603125214414607041080d90880542c85030036a414071032001141000c800710b001640c0144c401c1c807030560700001c0041a807000d80030030200141055500daa0076120b005139500540410b55988040090101d20007504162412348500f040e62600705145003083c8211582030150144448040c400a4090700005400d001d0150080c00128056854030380307041d281a10342d01c030015550a0840748282151001940d500014804d4040e280810400f000303030313124141c0d5a0f036014a6583c203101d030b0304920f102c0d20403030120642c05291541145080070181410807448800218020090760200307680da0a41440350a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 731531070 1250 731529820 731529833
    0x12140c090703060e16120b010e090a0b13060305030409020c190302030d14010e130804210215090312030603010e0a0803040b10060c03030207031202130302010816090e090a 75
    0x180154002e8070009019814903400036840c0900411241d05281d1048149034040e500520b8920000905a0006070240001c00100d58101803541d40f00c1d8010f608106002c500900ca078000384c821001202d00a03a0306203014140020340d0310a11001e2b183e50000e1004008410094000f81550040c440990f10000200ca9040c412500340c51000d0b80141d0020503540e040598921070061a01101c0158040c258034000002000030002055440c07000c0d9600903c07410010400107881c0078003130182d00d0040d0328281c3c8058220b0030a2016081c0e00c54410324103400c40102010040b50551070018010b0184d42400a000d10065840544041d400d0340d6500a0414481000d0000b04d61481c4540c080982d24202800c080240100213400301c1002915a0010000c0c50340000910490301d51504000d62aa50142000d54103820f0140c24109260b000140320814041c0e20303860901600e100343c0750144181c4407407076005424814641d6007408503600040c1400501107060302240d0041c200c00454a5410403a590103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 731532320 1250 731531070 731531089
    0x90703060302101e050702030c0d06021b100f14390d0c09080a0609031e0507140115090e0c03031207260708070e040e031201050a12140c 60
    0x540004440c61341c4101025090341000350ba02d002460a20300b0100c0396000651141e02e001c040303d1080c030404c040da104000c4a80c05980c0c55a000c802d00910145a85801302e403a010081041e15080d45020b642c55200300d00d0f485407115142c0c04400c03c90043da00c00f40104403403210600b14905118001d541890545000444001d480d61640300403505c508150008a080d110800c00303140900c622481c0070b220040b0b00040801c006e982251000c10080d0590800341e5000c0940001c10141002c0800d01205044d0801c004000c060f02c10881c1035076000c00300d071955080b02c94006101060610145007001020079503002140c4422a000658600d250490000b83c5590322140740d45505400c06410411000e8008480801206094040314800d0b000710505100303003030b030043c4542c050180c410045240c0f0351042000908041002e041089610b40f20385429580c0e4002c0c91140142d4055000086141d08149580904035881910352012140300c40d41d8605c002c54812003080c145101d11210307408035030384041d0790 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 731533570 1250 731532320 731532349
    0xc0203070b0a200c09131104090f0201080f060108010b0a1101021206030715050a08070c051501091d030706020708070b0a0501050108090c090a050603150103050c100c030e090703060302 81
    0x82e69881c0680310710791024104840f46041c8140c00901d032400b0103440d20101c0c2036120312442080b110b8003120340381c00701d22040321840e00f0384c10a241c45a0402001035901819a29034002d0702c400d00c1c190b0b6140c283c044012030460b10f00d40042e01040040148014807009005914803a060080b03148501c2c04d101070898000141007031050b02100c041c409582410310100009e045426003c03c080c20b0845005007040c0304410727280007000010800104924490f010394401d541d03008054407401e184030203007550380381707401e0159458840c40d010b401c0c0001c0c0f00c0390006040b00c070401400b07982041180d854a6000f03420402080d55100c074200b104034005180041031a105040030301d80016254105000108140c03002007400d1419880201030740100da8130034029030340c001009900402c19988400100307040c000542c0d2090500907885001108004000c00c240c4a4400290380c02c00d0922120320703044500080c581d00c0030340072038001e200440079410265491a48403100b802c2c0443e002e0380d2980800c203000440200e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 731534820 1250 731533570 731533577
    0xe03030f04120801060905010e060f16050613020a0e09030c060a02041a16260c0307051203010e01030b090712030c02010824060d0b0d0c2d060c0203070b0a 68
    0x401080050a0340b0942c030001007881c04080c25810280054000d02c1c05000312070500100d080c80f02640d039566821161001e5240c1d0705680c44d00c7c00e01e0000340300c0034004c0008407620b000d41c800090141504400401c510340d0001c0c18a0045460042160b20100f000361800c08980420424000c9c000f104114150081e0001400140d56a00c1c0020300207017080a1a9030303440b0140300704803d400f581141c25070102d50b10303000400140d02c02918a1240303505485101c04a03082400410490b165001c00300140c4039150003541502d400076038010704110703184024098a01801c050b1801400441da0b000742142d849001d403011a010300e51030341014103a4107803c1e82d040b0001200e40d16040110b503800706806402803003803584840001800d40550f00078483e58802c4501a02c40882d24410282541d0003c141c000300c0a020000d480c0da150070030191504030b07801100b00c00401001c040d010414400c040780780c41c520b20315034013103001c1c18101c0807540810070650580c0d061003143c40228902144000821419a040d203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 731536070 1250 731534820 731534851
    0x5031b0f13050702032701050403150f050a0209180403021504060b19060f0c0c060e0a17010209120a02130902210c0109080f120a0c1718060c0a0210030e0303 69
    0x80b0a082d40c3c90301031a19000202c403640c50707440c10392308941900d0980c1d600890b10313011495460825002080942401901d16003440c1c140861107500d90700402c1d02400591381c0c140c00b10750b482c1d002c1c08282c40c05d40d00100160300010444900c40c2e0300d00401908584908000b0600c401030f440000c12015403001e81c0c40f401403200707008019558001c1032100b245c00c4141414000506c90f0f849000030744d10103200b101c0a2181049181081e40e45000e042d01c00b40401c000d50017034000f01c120035a4000e4000b4500355010f029580010f44030003a000402e40c0803168010558070513591040103103006413801082c01ca0300025100c246500b011121a011850349140b40020300c44901e85100042ca5044142c1c0301c0396460f000075000308001703000840d001c00001d021607400e0b50355030350001701255007030810b41000c0d1142507142410301400751100014040072000e44901000d0032071100803c8941d1041610402403039122802c0c2c1d80060400f411140410325003410300254094545c0c40352411540b045031110800b0407003c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 731537320 1250 731536070 731536087
    0x140f070602090f0d150f0b0307030602193b04051303180e0115140d050a0b220b0f210f03040303080121060c0806010905031b0f1305070203 61
    0xc062014805000b100c200103086201d44424045c5404108009610f6403100300c0241c122002d134008000100f00039040381e141d9076484c1450f074001d400949901c45142c510303506112410344110540701c00d940c803222601c41c01109028138510105500c407810b41a8488203d03203219159110310032584600d8203408080c0801c80686070040454030320310405012100301c0030042c02000340005c0038a0640386080c400c514045ea80300801e0300d03110b800280c40000200f00250100310074030319800550080034202c2003403040240040410000c0038501120303040c0050296602c08aa02250304500c440e2500035104200301012017021030564040020b08514100310842d10f28014841000f243c960344160002560429042d69001409024103105400c0800302429101c0c201400b558043c2c548554817000c200002d8400700710140071400102c480e1070104568607c00a001c0c140400c984090f07410124000c000b0104100800072228020007480c0d801c900090346140e00d8810510071207002e00210340080d82c440c00e0b103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 731538570 1250 731537320 731537329
    0x21c0b01050108011d0406200d140606070201030f200a0806090c0301060c1502070b16020c090105060a1e09180c021c020a0b070906020c0402031006140f07060209 71
    0x41e03011904200c41d0300010004012103200c1c0c50001010320072080b156440310f00b0312101400741011020b1060103100c0e900c40807404400018022075440354024411403000844034030300b501d000c075600781c0c0020040060400641c800d5028800e944645480040c0b84800000c180130b400d00d01c895400c20703030340d00010b0040150f500300040d0365100310300700c48110051420f41b440056900041c4502e500740120000b03071100304001e500710703d40b0b4140340ca903046488155605240c481c4860680310421172403603103503c500c40244045036140403440082c180c154240d203010b091010551024000d501000310300303200c04019980000021014000503075800041c0760500004d0324800040704c0c24080400d181c4014044140c0d004944d14145110710368440030140c0c034410081e4144541c51000500c0300a5034001c2004c1c07180c100c1c1e2982c084e00d21039400c41d100702003000c09000482c801500c5400c43c1c0032821508000c076038403035079841220f24081c401d020b04080c5081c154646a4000c200708590440d00031850b1000ca0a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 731539820 1250 731538570 731538593
    0xc0b180316063315020718060e0f0603062206020c0f010c09080c3706023705160803071b180b040e0d230306061c09021c 53
    0x580310040c0300c1c0480145101c00145900e1080380144c2d60b030040c8056040b8020302c04d000003007039420b0119a070041c0c4c4100c410001c00c40ca01074007691600003c045840c130000a00e0b50340c480c02026001b40407640300c404441401e92506222003040440c4a8910400036141e4009000d085c2d80610041541c042c1c516101800c1d0f60007001c0038002c01071840350810400200142d15500b40388256405044617462403544114080824002c0320210014082c503407a41040c05440c200703d944550030780c1ca542101c4103542100346490740040c0400c03244c0b00c1411414026038005c409a66209078121520900b44031102d901924265000e08020380010030100140044041c28052881120380c44003a060b051012a08021444280b280281caa03152402d801c00d40b900e034814034203080c40c2c0c001c41d081d41c09242001070040b90b811501e00150078040100c103a04840302802d890260000804850401d11460400e040c200480008604255102d0480a003d610b420321008407600e14801010100078450604540c03010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 731541070 1250 731539820 731539871
    0x7031805040b0102210409060e09010c0305070c02010e06090d0507060813020108150d0203010f0b03010e01020412080705100c08060118080304060c05030d1b020d0c0b18031606 77
    0x10b041200e0950607a0340480d513030524903950400541649000e0030b9054079800740b9004000100c3c580200460007813006003007548103030705402c0207002704412602e04405603030080d911000400c52416036034005601641c4003803225a0060255800c1040c2000001ea02188191003a121758010400c140200b650240005034012034044802040340e07000e43c0002e22607580207250903e480849160403a15aa8142101141c0c9400034002d0190195429000c0b0003424424007461096207080100c062051060080d5170443d00500c4030900102142e841d0001c4a9018600171100b030300a446400c0384280705031241e0300c900e49040d40d42400ba8030f000b00014001c029001031440c45003a04074020024048000704807020b4909900c0c10307030f001c800f00c0e03d0844e01d58010071070202185410140e0501014a02204800842045900b103420415100c9801c0e1403501404c0806440d50072034500003551000071288103600c1e45181801c4a280c001c01c04c800f045001c02c00c0c1b404403420b07603c1c1c0c801e01c0c00c1804d4918070541960f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 731542320 1250 731541070 731541079
    0xc0906090e07051b010b041e141501050703051204050703110909120a0311270d030c0f0c05041802010207061821050303070512010e09030d09060e0307031805 69
    0x38100031001400900134910f00002c8581404100200700e00700b9081004d04001c0070b00140702c007a5080d18210043e48000c622807801501e041d00010004000c4000e8a01401d850480304c64038045c1400111070715030041c6815810700104003d07880703115448045c036078843c0c0d000380054040c8a0644c58001403e566014100e440b500300c0c18103100c0110340c00700d41900d07010940f609560391500040401c0d400b0b0900c580755500c0b43e410124000400400c0760040000d1030240c2c146d4076020104000400c64512101d030000ba000480c5190000000391540e0511089940142d500f02c0e420303a50342d800a020b0b43c0589620340c209403021240c1300704558042041401810040c01c0c00300e100d512941404032070140c00d220380b40040c0484822582c500300040c1d040480c45401c0b4050b6541c03450602c0000d030003944003030222401c00c6000b10000900d58000034803c1d0040580c00061032801c401140a140900740141081d0340b410359401d0000600c0c0d1b000c00080c05030b14420f4481c0340310b0005024035080c804c151640054000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 731543570 1250 731542320 731542349
    0x91a181b0616051c0314010f0e0703051932130f0206070b0106050310050a03020a091a040f1d0f12071502030a0f0c090e0604020703050c010c090609 65
    0x990348000540d00c1005050781401090901403c0041c50b180303541c2402c08603a2a101c00c584a440da054209485442400e2400010341e640c41d48400340100c680d00c100680c0c0c044503030106180a220341c00c1140c2001c0b02c120700410584043c0882d80440348441d01072500c50710704604a5001d004c2c18024101e16400746d2001144500d80507610721a801211140107002c1e007604201401103603103900c2a140929084286610700b0341e11424064450b0f4003d45043d400000f125000054030300d41644182c058903409818103040c02d04d8000c1c124081c007203150742c420f031810020160750450b40369445040540110580c01184074891207240300004640c40c090a00b0703d4005c0d21034102d80d00c01c001042c2500045441c51503035540c0d000d04040b0000f0001c2a5030100c114000410302062441c0780c2c008800c1d0000c8004104407060249100750742d9809248a4401c9805192000032014613040c0e028000060203424910b26101000020500f180c2e48040844040b0b105140d0610a050340010358002903d15400c8005e030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 731544820 1250 731543570 731543623
    0x30c020d0e0a0b0d0e192114030601210b0a210206090a0f06021e0f0726010504061409070b03130215120109180c09091a18 54
    0x407240a40602143d00100084400e4900c01c554016015212044180e0b4065883e01c04000c040b00503c0100365100e200c4c4c0003078445201c102c0b6904000c85002c507115064481680d000b8841190402420b003414400c0304801c9038040000000c84a4204028240c0003c8000c9d4403003c00807444841e81016041c100f030f00409800003441c03060b1a84046804a82c403a803100c4076000007820b006119000480100b4400da00000d00ca5000a854109201c25560411310250300301580c40c1c1e40d518000312440c1a038842e010420582824400507218000794000b400300403944026420b0940d50150b900300c6480d56141c1c0038130100c0108034072442c0c1100400b005099100d107000340d11085800301610044540c0b0240f074100c811583c0b007803071244200c3c0040d100d45440f00c2004ca5100a00720007449407003030b441d040c618521017140181074404915030740001e2201695062a10041c020407000400700d83c03032880e10b00710900003109043d11500c03a0020021350420407043d040c07000e0074070464410816444000707501001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 731546070 1250 731544820 731544829
    0x17091f02070809090408071703040201021005061f140a020f150601020d0305091018030306060306060912050f01060803070507050d02061603020c060f0d060e04080a1202040f06030c020d0e 82
    0x40300010226001365890704d403410700305564400d0101c001c09002080504c0103201c03060501862086000341c003a5207030a120700b03031440c041c0c2d0000c460b0503901280c00545195640c1817940c42c2003d090007440e100e002c0c2c00c031000003440103521016201026034800c19a40c0c00301c01c000c00510100490141d01e0060908001300040c0d91041d00c500c0f03036424180c5581c002918a40100725240340800e81c074034188203c0130310010003a040b00654030140d0009041c081c022900700d01900810301100c07801e55440d0026440d00c200c580ca1826040d0b801c403114001c020620381000340c00d004e0318024040302405559104c865207400d929001c815848140200c0640b0480c10240c0d5503903080d1060881540c016201694951804a0400d503120410b103074464008031700702207041c2070340c0e010f01301e07103002100100b260540710786034103400300002c54006040050800c1000c00710781c81808810200304011002508068440400c046522a660001070000e035032490350191840e0304225003071408940d8100700c81c080f4040c00c0801c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 731547320 1250 731546070 731546077
    0xb10091838090705030103140114011e0f0e240f1513030606140108010e0412090e07031a010e030a060b03070302040f022d03150117091f020708 63
    0x450700c03400107190a644142448103141c00c05a00284020110714014101800b81c0d0828002591600a41407804103a4401407041c11850804403c8003652a840c0c81440501081c01c403007110101e9001d120005101d501c285509400b41001c00303030340f001d1458a124165242c420030074001440c0142c88840c0d80e150b840d10f01c55106100000d68020305076a60303052000c120f51282138003100f901b4001e80c0001023070242950100050320100750f9041c1c401d0701000d004403003c0340e082c01994414842d540c0032a00140001e802101d030b08a03141061101c2c82c3d6030f800f540d0701600d8121407202c086a103481c10104008443ca400c016652000d091a8140c0c90445003c40d0f540e45462030000c1c1300e20390715080d070384540c0c0e410010320000715401042400048090207804010750000c0440e582180034218801202c1020200072844072444540301c1d50465a0b541140107546824240c00c506011061114082a0064200b800d00c2000524001d0403d07281004461842d9152024102c94a910502100c0000380510b03049 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 731548570 1250 731547320 731547371
    0x2d012601051003020c0f1f11030c0d09020604080a1101140a1d03030d0e15010617071e0203120f06010c06020f1605061504050f010e07030b100918 64
    0x40700b001c24045502600248154500c112951007403c076040d03202140022020300358643c011803140500d21500e00c070020343d101030501c011480307800d0000441043c0e551000e44658440303c0700c00709481190b900440c0d0a030780150064540c81c5c101400260521540780c1207554407000a02e8082c08400f030f4104600e4036401031041e101c0401004150300214115040509200c0303a400030240c07591409840085002040c5070503083d41c0a000f80045d01030284214894181294555110721044119440203c541e01200401c80400d024103109148501031040916001e0380c40f16400940e45d60411003003d0b42c1090f0014070300007090240c94204400c0c2e980c800030072014594000005070701c41e0481c004218040c0105c020001c41290f210300c0a4050080000e000d13402142040f050310a6000c142041c8410341c0da044408a0055542030300400801c0055145a41d015a16103400224507021700e0018143e03540d01b035510000191080810f0040c150b8040102940c4041094208503201205c5c0b01494103040f00c418 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 731549820 1250 731548570 731548579
    0x180b180c06070f02011223010b091f09031506140405161805090c0403032309010e010203120406021c0b0a0317040f182306040b2d01260105 61
    0x1900d046900039503c2d6008251b003004284211840540c5c103003c0c0c101c1400200640d15446000001d02605910880c0c40490b00540900007003591070920040e03164030340c4410780c20440c055000102040710325100842d451031790b00010400324500316050444203242550360344902d180400340301000c0c0e22421020001941350900700792616155407905000750059100341d4000c1c504e48100712a246845004006881c03182d101d02c03000743e0700014484100c10b50200d03031412501003007180c101c866001d910103070405a0705104683c40c100c840349070a1182e01c0265821a80141c0104e031012a007130541e01c81c0c0d03001d03100a140400c48540e05000040e202c1c202c0d8403015202101c01c0c0501503000480c0c038221000b1740742c0c0c00300b1070003c0c1307070b175410031590b1136103444400c0010317910b03103658503c02011310813005503815401030180111740c0b140790402009240341404c0d503601041d50400c545880710031000b602900411680441e028109280000d0401d08214030200740003c42c0891240b810811003199506440b410798 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 731551070 1250 731549820 731549843
    0x91608032a07030507092403080403030311090415030b070f05030f0406021b10060609060507061e0f0204080705041125140616030203010621180b180c0607 68
    0x20305141051620f0704043c100f80190100070610307002c641c100036010500100d5010b04002c41a4600445d655180030091008000300410004244283c005071081d100c580c80041c80c0c072800600007400c40d050070a502107506000f8004000b480203039207016520084034208241032a8030140c005000b48401041d10074900001c801040c24030007154169103074a590182000c24104c01c0681265441503110011111107003003000c0440c3e0141300d018000b0881e01a600d642c2d0810486560f003070080c1141151070901840303d801d2801d6440d00d0303800b03000d211600304200142c1d40d6041291141c1000803c0c0c0202d030056040120b00445070056000320b440b117041d403210740005090051407404c0b9a5440748030150a442c4515894801c3c0304000c0303401c40c010041050141c030b034484904004c1c0c1c1a070100348222008141d440d00c4541000d4084c80c0407514640700070000040386005015407401858084805440c112207103020410901d0281114000458070f40c4000e10b4125107900001d90744d80700d00c20b4000c080c0700c00003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 731552320 1250 731551070 731551147
    0x6090111030c03031e090a0f0809030c09010b0a0201051602070e09031204200f0f10020c10081602030c0703020103020a030e0706111e1905030d0509160803 68
    0x2403050302d400d002e440007580e90328206140c000c0f800306082e0303000203030200c1035902060070950000784900080f580b01c505040e64110a45401c10396030050283c0380d81601805a05500707580c0d0b548403c0d406032001d041d01985440300064000c0c212400100701042084418452051042d00000c0040c22580d0003003448100781d81e00f4080c10f0550258200341e103010341d401e0003400704000049010440f158410301003211150854000c00c0085581c0d03c51083d04014240d070030b18140d007009a600c100c0549640101e500107088140810170342d116415040000603508000c3c00040c000d00b19802010709002d20095041600b421403094490f003151000074181a40003608044590081d0403070000e000c1614250b512180c1d5600028104000740c01c0007103401d004109210300042c0008550040782035408005146400650000c0c00f9030320900ca0003a15140b00c144000e4042c80880c1c00b44910031401d1201902c0915000940d1081513100c03030b0030255070b940003446042c0b500542c840c08103641f4400c0307205d68200c84800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 731553570 1250 731552320 731552323
    0x10b09040b06061e2109030703080c090109080a1101080f1902090a0510020a030f031a09070c080a0906140a0f0e1201020c46082b0606090506090111 65
    0x31010400d088021070401d600010070707070143d10f16185e0a10b008940b56218114030b5104d100e01ca40060104000134046040c0c0105640a80806941814111001d5488250591030000710103400c40e0580040da00c41c0046503400700085400142c941c0c90451181002c1d000805078201d0521385149039a0b021844c5e103016942c00380380000500c0041c040c41d4145004400007512107600c20f4048c0d000c10302c4152074030038191291151310905140b485800710488848000c01807090009420041046203081495010038419801030191401c02e0716030b10540745c03070400041d020316842e10000307543c00c805100841c8003c2e0001e424610b00901c501d48520700d00c54080000e03042c960742c5450070060307610118015000000c00140000c421100c00d040303002c034140d010030300c21180c40d40254001040c0c107030f55001009005c44c441c041441502c43c4500c2c90512003a8540c0c03d19000764030b074a000110b032898032100e4448400307106803c00303001645400f1100030b091102141c0c0c50f10404202604201c15a040ca41d41e01c1d10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 731554820 1250 731553570 731553607
    0x20c03122104060c11190213060b0408060406061a03040f03020709060602010e10060f060503040f020910030b1302010206160203040f0b0a0f0903050c040203060f03010903020f010b09040b0606 84
    0x715503464010304240c01c00b00b00415036403c01c0d0b80800c1000c00e4284240c000000c1e410380a003000000400b03011141d074244440b0019420340d02615030340750040805c4181000010b480039229450003410320340f410342400b80a80380680e01c0103040b035074000710340c40d030001c0794030308072a400b54100c40d00c0000200f5034a8100d240500c40e0380400700e070900c5c004002c40ca00740c1c10f400241607803140c3c801b02c1c0e080602510558085920501c03500a0351500c4110410005000d44081d43d070141c000c4891050800081d00801c00401d4200d0781e001109451a90902c00c03c00392602113500301c40c4107100401e00030b1659001035582c0102814214910007001045d13610315108108840190440150f00c08600d550343c0c2d1a03007040d0f003080da540000708004100c51103c5071711515640040700d800000401030214044207000080d8409411140c002c0003500844000d61824061004094403a07030040c000f40311804d50980c211040d50300214403071203511051101282c00b21401c540c00902c12564a640d4a00c1520181749040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 731556070 1250 731554820 731554867
    0x1104090f02090901150b04080a06201318092627030c01110607080c2106040b040c20210316050a0c11040605180108070501020c0312 58
    0x40e250b40c100020303e00107401c40444110724040f120f200d80e4076520481818000d0b405822000d600485003000420400d400c014030090520714802904032078591203000c130764400541003000145000c0304100d0b140b0300c1180810710340034050701040785010b2039030707078200c4808800210820b16a0300c840c041d804c030324214202c4207420712400040103c1040c00841306030341035a00007800d102c2d00403071101221550140c034800007140700e03c1016010560381e00406807a08040136010b21a507a500303102c0d40c55400b5482d41c001d10035421680400005241400c204815651803484080c0203a0500c0481c2400c0f54100655001080052814040384040b00081d2850810308080e0103004c504059000e103a120780001c015801403c00802d01d40c8458540b413801d440d68400c44859000164a10110101040d60581da099040c00010408282c0340c0d03891000805850001c0410480c00c0d01d808010000102c04101d807500a0001707001038842c2c0c0000900107a1605214880d14410400009001506401c00f42e540f00c0701c2c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 731557320 1250 731556070 731556079
    0xc0f14070b04121a040c170309090108031306030b06072003030406170906040b130317090705030f010b011403150301061d0a0b15070501020903100c08010e01031104090f02 75
    0x219075644401a00007010941a204111a160440f602c0b1304140019031180ea0003994081a4a10301030b400d0301c0c80191701d540c1140c580800d10039085903a452003845030080881d840259224030100a0110003980158031640515141121010b099115603095800a5412018680030a01c1c4440f4404030403d8007250341c1d5142c040001d001c25080d80000d080d080103050001307204445c0d907584440d13642e20a415140a41200d10b4440000e6001d106c50203ca11910310034900340d08039070f0100340c0540400b001515208982c0c1c10882c0c0034855400c0400c05005510b56440081c0b1000700a100040c0401001d13640e82c080040d40080003d0f00c0f007082486d804150b91015000b00b1005135601440d07880c5428082e5084001c059003c0400e00543c3c82c1e000e880d07040d08000b00440000c0d030710844405040d41c07000808450a540074000c44400d540e041c08252607001c01020041400000104020100c4505820660104040800510101d008050214200f4a080d180003e120201d41001c0b0b0303c500101700000c0d0300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 731558570 1250 731557320 731557327
    0xf130303110613020319020f040c030b030f011b0e150706050103060f05042018100e09122502130f05100302010206040b070306210b070c0f14070b 64
    0x816501081900400501000b81d400c80d0301c5041c104092900840e00195141e80b0221309601c89031003229540d81113610017402c01059a210002082c01c4d00c00504d81b00c3c0201e0343d65031065415040030f000900240000c0310081001c80c140b0341022030301055107081c10040003030a002c01043c1b80c66035003a5041e51004e8030a00f985480c6645403a0001d81002d020803140c0d241800a840c0d10300ba0240903040c05103506c62000c207008003004054800d0640d101200f107a00074481d1416110010f03402c00018003600400400c021801d090800001d11100b000d48014101d5228014000c40307401204155070000d08154207046182c075030035100030141146c0342c038083e40c0711300590b4080a10304401c0d0f00544183c00e000c0c0c0306100c41e5444180e5484681c0e401e10000c1d02580046000030005030348098400c0c0d01400d20300300001c0c8a030301c034541034002202d0103c54049000c255004102444907d4000c15407114007450207000125907030382c4000584409000c010081908032505085008003440100d0162481d201020744 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 731559820 1250 731558570 731558573
    0x30a140a020607110a1703090409030e100305011508133c03121802010305090a0b0118060509250e09190e0d050405090703090515060102061602120f1303 67
    0xe040c028608071600c41c01c80c000c0e0024106c0c4c02d56511014800c5204051801c1038684810710010307001d0094100d08001d000d584107031982e62201e510070b440d0f000d01e507000900c540c10a030311408001c0ba2103103050203004407242080450103024000c000d00c0d5034011900c11400942c882d51410146d4126000e4040203442c813407020501c407282c14001e02280c081d580f4800d4a00002c007c0004031200f1003036202004210080810155001c1d80000f6005041c4800701c40010702030f600d901031000340a0300009106006003900681514a40c000c03040505402c44200001c0e041c00c0b0001402e009410303900c0f202c400846403c3e804003d010744c0005000c284085d00d03005041c90440140c5a09000540803061240e141c441060442d000c000743d400d042203402e40f18146010305200401c140680c000701741e07808046d11903411000050041c402200e040001c0ba021030984c0c01c050b4006400c0950042c00328070038040d00c1c5441d05100e5800104c203104c0d550110b4441ea0348544035002075855103e150b400c10141d0710750650000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 731561070 1250 731559820 731559833
    0xc010515030606010f02030a0f1701120c0b0310120218010b030a0e0c0f0f0d121d0319020609010c02060313050d0c03050a0311161a15030a140a020607 66
    0xd0340c220085041d6410b65076000015101c050032400c414006a009020101d0a01d000d40038801c01d54030141090f00c8115071009500003800d409030880010381140855260800508894940c09401d00e0a8624294a803c0304814007451451241e090680c2c044421041551030301c00c902d500c000220110a0780568481c808c00903640d01c146c0d50ba206262401044014038800441c0301d540c642e100511400d48040504108a45003c002d83e500c0e40c030203c818815030024080580b40420000140c588822000707003080440d8803098014840c1e130182e0019804440ca922894400301d070680c0c3d0440b801515082e01100407905400a074000070341000b000400d10541c07010015202e008644507030100c4400e0391440d0b204031030080a0310001008908140040d081c181d000303401900740900002d04490170500d0300407229507420240401a150314040e04410b440658600c0c00f0305502001c13051206030058480d00c080b03641d41102c0030001d00005800013040407011028851801c005800404042d00c80100c2d09060 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 731562320 1250 731561070 731561101
    0x20c1f0318081b0d0302090f1002070b030f0109151809150204060206041118010e15040c05190323040c240e0306010312030e0a0204020a030c23030115050c0105 70
    0x2a612842081e0030259040d200380200c0e14034101c01b800d40040d500c0c0490034271140d0225201850254043e81001143c0e85480c440590305c611108400b0035115403601403000100e41d0380205090922030103520500c0006e5180314508014001070000044900060078140000d00da60078555426600002d00000d030250b0024829026900402d14040103070004c008001d41c0f0003142d500140758030040d400400c4070006040c0e00d0365200c450883c0d0b56600070018000501102d80f003030082004600701182c7c20b8070140e03522101c01c0e60000d0500f02001300511072500400941e6841c0807400d41280520005800c0201d82043c4400400074001c0d903480341d55202c003509003e640107400b544001a854800c071034181c13400041c541d0480e5000b4422045001c02d0b00b030114060300c4030103a100281d1103501012801602c8510052600060640d00010780490420008016040e031140030161040900301d000300201c1c00f00120f1381140d540484080b00380c21091419605805000c00b180d14651804e006c012104a001524 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 731563570 1250 731562320 731562367
    0x20307120615120206031330031e090204021e0408190f02091314030d060504021e03062b02120d0f18050619020c1f031808 54
    0x41c000315042c03815240c91040c0300c2c0300b420307082044140300d0005420114005c5030014440d030740080303240d285500d660004048421091008a840d030503002d1420404031821403900001d443c00f40101a05085500200044001c21080c45c03603507000b0420855907583e040319408080d01d61160080c0303160340c10042280c5c009104940080c003400d15400313140001c0300004002150b100c82e03d10369065454003401200e4030014840180b81c2c010550711004994450302c0c00c5031440e030440c0110368808614100c0800da400c0d2798803007406180107000c502c03003848420a10b40032444883c4030303c81d00c966594001900725a801040e010003501c0508a84017945681050000d8170750007561240c0740300d80861042c1e0794078540d442c0398400003032010860f00342c00c4d44a0000e090101040714410080300740c80e203000910f10b600000c42d94000c81810103000104c2e54051292000c1c141007140d9481c280d901000a03031040145074500e2070304255440302400340450310aa0380c004166048455030b034807003010b0000100307070034140b841 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 731564820 1250 731563570 731563583
    0x207030f051207050f0412060c020f1203180102041a0c160e0604090201020705030f0309100804020d0b0910060603020a020705041503061a0612010f060203120112060902030712 77
    0x2040d040c40c0d00036012540d601203007004401c1250741d000021034041d04806210152004100f00c0001c43c3c207141481784075041c2c01040c0c0010600c0d103942c00646030140b017240103039980e0030000c0d0080840306600c0036280d0001a25514141c0100c0c003807482802480307681c01440c03c440f40300c10040c3c094041100504041c814040442d03245580010014030080301314820041c02c00d0300c0c48000b501c0790070160801e1072000d1040c011a5a0151150002070a0003200f16042603264008204400035162a1062510394155414028100c0c102030300407642035030892101614019051022841200081000c440400d440d030504000d4a515a038000f0082d5000741d0103a401403050030740100c3c0b145410b1150350404141041210400d52450b80c4440c05041c0e880140720304001c00c0e440d16030041d21010020155140d88a0841480c1d605011805040015540100b011035009020719074000f41c41741c110a0550f021004240106d0740d0510b000006000c201c2c1b4025058020b80c400051000c0c030010491501d2031207500c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 731566070 1250 731564820 731564837
    0x3312303190303020306120f06040303061d041b030c1205010f05070e090714040e090c01110c040f021e07050609060f01140d0c080709060b1207051c06030b04060c0f09060e0d0c0801020703 82
    0x68ec030003401a40d043e80c0c1492200c1038404a40001c200c4152441c0180d804911803503c2c0342d03682c039682c080c220945c1c45031074881883d0f041a020071000303119450103c8080c0c84204558101028010300e01d6420000c1306000700311200100340d0084c0114005c01d2110b403103882c1565100e40342e98080e00700d0041511102080d100e20340c0c48a072150f01a540701e0b501c100e42e100c002e10b2202800c2e01000b0141103500c403070140c0b682c5e08006a0500d55060290590708042040c18a0750394003561038250304d0802d00a1940c1c03a9500450144644001d0081c030302411504c01c4a01401041c0280001500bc207948080040a41c089144000b0f0b00f942c006c900042160000e4204020306039030780304903043c3c2d440340d14407581200446800083e4100d0140029060ba69600000802c92210b890220790440e020740e0000e58841005604000400c00d0900900710300312017610f0b003060715a2500701d020706044000d024110500405100e400394075110020051801900704c501d00c210103a4611901d8001e602940303042d00001c050301c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 731567320 1250 731566070 731566079
    0x4290412020f0d0b06091b03100503060105100527040510092d020a050712020604051e0c01081810092303312303190303020306120f0604030306 63
    0x552520f0507541d0001e0102030a50344980811500a100600765105140d60a0703010107801103c0024502c81e00c000d925034030109090000301864444161310161042101c06c3d4488650f60384201580c3e5101d10302e405540c4070102144d110954241d42c0c90990380c02900c1c01080040d460204030300c420448090450801031868a201c9440d0910a43c1c100c400358582d101100ca00c00c6a01035002b042c3c029620728005003414015900c040b41c00341d986090400507440b40d02480248403050019003d0500252001c1c15440307903804840751070f00350300c5008a0500c00030100040b18a00c03101030148021741000180c078648000500c07030720000e10000b0000e65000a02d100d00c04015100070032114000c20400c0c0045043c0030740b0750030118203401042d404c00c542425a042d444500105161014080c002c9019004080b0f64207400001e0485203850303110344a0303400321948090321040c000d0b01009994140c540541d585d0384500101d101c50402c046859002c0c842c40b0f0307000302c9014011420310300980c441d560034001540c0d01c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 731568570 1250 731567320 731567329
    0x1091208030a11091e030c1f030b0307030f060e07090e010c17060a1a0f031008160f05010c02040b0d060c08090609120a030e0607020c01020c0603010b04290412020f 72
    0x1060484c54208103c0c0c69991a079110030310f0040c003280e200030101c6100c000d240d404280458411303080c21000402c40d24801070411b070103014040c0c4804c8140c0042219a25640f5004015090408041c0c49a9601d6810703842005d03052014402900b140c030b10512211f4001280d1900030601c0c14410000520041c402c041c10586410382203008160042c14000994103140070240c0c1c8500d0f000c1c84010f819003c10605c3d05060240000e5841981001c1e114102c0714036010b0041e0805000e42803040041c1000c5006101c40c100c40b140441c1500c8003860040d2001000d40702180040042c41e55041d8464844002c4d82c0070000103801c904803149190359448100c1c1c6603031140aa807884182c0c1c00d4003040d00148903c0c02e1885100c0041d1620303840700c0c80c0209480e00e0013000300f41401c1d0151003103401600901284003095030104659078881005a80c2c1030315544c034048484071180264000c00350280e07030b9080500c000140c52682c20200410400724160707a00e030340d05c05020314445125412800b83c18030a1020300c241c5007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 731569820 1250 731568570 731568577
    0x20d110606150c19050105070f020309010f0e03010609060308041a1e0306060f130311060703021902011e02030915070308060415091a03060108030c030706090201091208030a11 77
    0x28044020544820500c061280c10005650342c0600c20f40082c07401c84003030305100704c10007400392000207101e041410000300311950982c4a00250340c0100000420340c2d92041540300c0c4000f42c0e150108680903d000024051b08003a030244000a04180c00803040c400210018021074946129440001a00311a111303818000c0001c54040313000d800c488481c2c440d105100469008900425180ca800f640b00112115500704010060b00744105003c04e00170442490a024000c001c110307141030811150359002992001c41e6031100a0300100044a44216400b4951030f10000750350015010001c5102040255039800c081d60f21407040ca4080070200c0140d9904045070074064140d59800c4d040c1e41c0e03400c03d02002c2c042c801c20045c0c14640d9a000002c41c0380e524450a24080c02034104480030381c1c40602014609601a0085001c6400400940000302c03800403c80300c15590240f80407404140c140016a14090b02381d0000c0e4008200002c10001c100044004600c6901c0c11601004881210b42403500c4900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 731571070 1250 731569820 731569831
    0x20c0d110714010905130b0a1a1e070507032a0608060904020a0e0c070b062b0f081c14060105040611010e100209030601060e13020304140a03020d1106 66
    0x2086000d050103080d2001040c4000710b48181011040c403541c076008107807400e00d510381c0d00b40d003e82e036040e03418003503e030a54000c00105803c40e4000c001b85640311103442c0510a075000303d40b000e590160301020705d1a80e00180c40d0380341d030488181c520160340ca0614442c0807c03043c100c5100c0640f549079070030b0070700c14401505c0143c0d442070b0b9840c907207590f440d4107000040002800c182e0b071000100100007009031f2038050b840c0c82003044000c0f69403a0700044c03812140c103a03006000d2030711411030005880b12500440280494900e008481c0e04a40c0c0e446013018120b89820b01d0024205040002e01042c00c9107116006131043d020240b420003403e5040552054a00410f550050001d401000108102442035040c00710380c9122100000302c50041903455464000c10242d032840302600031410b9601c030301d400d00ca030500408950429032000c003600400101803c0c040b202c46403d40d0ba01001040a01440041907401c20910000f11200b0518505020750b40322028151500007900103186e00d204a000401c0341c60050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 731572320 1250 731571070 731571073
    0x30412090605040e06010203070f030f1b0809091e01080a0b0604020c070e091501030b07090e040b07030f060509070c0c21021c02090f010815010806070e031f020c0d11 73
    0x1601305803001082d07003400b41030baa045200601034000880c40c2003c80049051090300e500f4034446130010081c0c480111580d0b010f08401060390081c2c0800c082000b2500c490074103c81040d120341c1d80b0400e039003030021400c1c01c0c1c4200f040901c00125590707a00282c40741c0c8890003490844201c2da1900c0070403040e07100749000b5030401d41200204110002c40114602e8000364428243d9020b0703981c90100c001a5842640140c90052a04090000842c0c10411450141040204812542c58141c5170281622030280c41f03442010741d20210200900040e50011001d400020300486880c28403031002003100b19a500165250760364940001a0601c0200180c0c02040007015440a040c1480d0204101d0080c40311010807142c10300d540d1400107907540d078141e900c64140c11703021104035410038900310701e0805c203000032200c6184400d0061143c0c030000200b06521008503d0010fa50201e243d010905040c0301c0301d1031010b000f403802030030041505142c019050200d0102e003200c03500386030707280226051010039901500b10b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 731573570 1250 731572320 731572327
    0x5090c1207090207030e0a050406061b08071505042a050f030f060126060c040b09130f020d1a1c030201290301050a0b060405042f030412090605 63
    0x140c00d02025600a400405059800d202d0351001050709030b80c40311400310002114890081300c5481d145030b22030042c20042d50b08204240c280003020b0304005100c444190f0711003a4524031000c01204004903081c10740d101500045480307101c0341c003401510060b1400ca80da100c1003401243c061040004014100008d10908281c035480c11040c0049030842c4050709406000e1800c0c0030682d20401c02030580200710611241c03002e43c881c041503c805080c04c505d1404990402010f100400c003030f000554050341d42d6848522307900d4528138002000144d036403600590040c200000c203003415559038090000e00d81c8008003400f05e03e142110440b9240b40341107200b0307070010200302c1d01000041c00703c450200e164828000010120310038510145500b40c40c00352015142c0c40c0e41c0d031b0700701d01c1d003421701650717412400e01e204c1070260f82c080e400002c4079801540242c41c003580d5a99514005000418240c0180400354041c034002d4032544040000551300880701500e5030384e280122071003a03078807419111007103802d6551100d04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 731574820 1250 731573570 731573593
    0x121e180a180513120516060e060403021509070e130215030a110c1c02070806100312031803030f1107150606080f0705090d08031f05010c050c0405070c080c0304080c040509 75
    0x45c10740000c24052485542c4e1070f14400010014810b101100403420010704903850b142c0340007840e084140000245000c034010610060320000991502603c50745422011182d0341d2903010301c8158103446029501c031003a05900809480b11200030b5000c2e1030084024400e0340240b104410042c410074440d40c249900442d8480801ca0b001004140c81c8845072040d1590f40380d55941c40f0b440c06205903044400300c05904410010071035002c1407440500401c2c1418081d0540910554506042400020b170506441d032082c1b1142521581c85a80b002202050040e202c02c541d041055096025400d40e1404c0c42c5480d0700404c50078040d2402d503210f100c2103a00340b051541c0f0b0002c00c8030590004a81507030000e400d2410300000074100f1000d10b1040c0c010540e02c62242d600f0340c81c480c00c0c0c1e11a903444241482441c00102c8046200481c00c0446413105036400300741da80300e40c0011200c5075907000d0003401d5010b0100d800001007101000500c00c440032b8034101c0700700d500380208000c2142c2003903071001503030307440540c5282 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 731576070 1250 731574820 731574827
    0x20402090406030807060f1d06060d0312110702180105101805090c09030606150d051e070507050606030601060c061a040f0e121e180a18051312 63
    0x400d100050408500c060f52543c0b03c4049422004040311415118600c2c255851014441d440c41c03550f401c40c2e244144101401040c1d12814082c00241c007030b05e207020180c41814001c44c000340700a4203110f0700700555540c03441041d030b4a401c102c600328840c101507140038004444031850b0034140c8400414403060f200c074052050700e60007a1000e01c038400240c0508001416600c98050310710507035072441d000c0d80e9546040101401c043c0014400ca104120745400503000e0410f020035103070803040f002e400180c541c0b10700ea6009400400002207400310000701040050482d40040981000b500c10011500182c803079104041d01c4030800d00511000404103003000d400b085c0290486542c40c59050700c10005500c54401080580d048000d42c1c8012544825a0300c4030305000300078901501410800b01418100b80b40407820754094198507100e00d03200b0100302c0c0c0d030031140003580c82040600018100054240d550040021901c01040e40f442024506000a212007000c1e0600800259000c3d03039903080740c8603e12055 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 731577320 1250 731576070 731576077
    0xa060915020c09041a0f091011090406031a01141302070303140a05060a060302160b100b0313151a01050309190f02100f080105010f0e0d030305010501140403080304020402 75
    0x21011031007a4141e410b8103455015480340a18040d42c40d00045814844001052450150450881502c840208208840045402c0a540c0c100440c0403a090700008205d50050151503852640146081e0000080003044d00700f02c5c001150300303410410a80c0e82d0343c08000500700312084058000e4014070000418202030390080240030700c80d040000d02198048401008410300700c41d003102c00b6984000340030680c0303421202c20008120038501985050305d10703e4801c3c0c1300806910010410402a008540500145e20000f4080e040f4500e4241e240d00e009059010207170b04c2003600342c400191114015581210034000c1c02d90384c285140c200c18642c0015001110349500081c00442980207100100e420548010310341840103004000ca00d9403041280104040c490300c445001e402d220404c54402c0c10140c05c0504141180c00c01d0030315540c1178207034401c1502c405100580040e0f0004503061403d00300b41d0141d0110381640c0c000c1c0d80701c8032416007080001c600c0e03206601014149100620020740149400d4004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 731578570 1250 731577320 731577359
    0x30c0312090812100f031106030603010b0d05030306040c03050f060d1502070507090f0903080c1c05040f030311090102100e0a050708030301090f140703021806160308060a0609 77
    0x5414042612a080076801090f118240703410040d0a00c01a90030400c00c0f080a850b02c2040101d2041c61035a401b0800304d141200d09010318000300024140303030b5080d031040010102c05840715490744064036250b03480e5801218084e01c264684460820030b148a4400e2620503060782c00c3c00c4196440d010104281c0c4141884103c1d080780120310514040521400074145141c0305070000d0005909107075402c4180c490303032000d8800c0585800007400c04207911400240d088581c08403183d513900c81500162a50607151001a140b60b03003050240b0041202803000f00d0103a44c003e540401090f4410940c61038944121010340d40184d002e28603400b40b000141c0c0c4800c1480701c41c0e0313007151503203403007079641509040050380701c0c07210782c2c0000c03004000300202c5020b81c80c084001614100008078810704440000100174142e01c00f010b90102d5a00003401d4000a41002c0707090041030b09442d01c0d00c0584440c80840f1a0350110005401500032400d00d08201c00e01c9019102d05032903c044c6c141c14050850002c4080e01c5030b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 731579820 1250 731578570 731578607
    0x7230a061b02030d020d0834090302030a030507020316140f0109050a09050708100302010f0507080d06030b060a0b160b0606160506010e1635011d070507030c03 70
    0x9504005a03804c020071400350900360040c213000b42018501070001000205000c41444400d1041c00848802d40080b20300700040c0d1000800180714218101e406400c1030300000d415100da0009001410b81040c040c100d503c2c8201c0884d4200c0d2110f580761802d98a452003010840f91001860b98454502103009107030780b240614120704079030b50390300004d069118141e12406d0380d40d940c3c6050081d603d5201c0a1681c1c040480c0110204183c515030000340980c00004000040240109101c0e007040000d40c21590713000042d1106104a80d26800c02d50f5044c5819110540b0900f04070a0015498000c0b80c290b540c0320b00031044800824840340c40b42102c1100091407103a21240c100043d200307038601e84070803205407070044c0010803956040504000010601a00c0d01c840024640c1115410560005081d00810843c5141c0700303100f0300e401620142400414548401c0850400c0085288000e14407207120f8402004100c2c1e80c1611520000d5989115004015000984407030006e000b090080e41c1c04491002c1007403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 731581070 1250 731579820 731579867
    0xc1e0c0a080d200304051908030112082206020f160e1005030313080d05091f09180912170708070e18090f0105070221160507230a06 58
    0x107121030005400c01d0240f124605000c02844103100c010003141d10141c4035480e02c2e181c80100e60b21080d426002c14495600f04030ba038000500108a414015580c050201d18a00c210903419201c484a5144403401441300510a2403880c2c500101c001072820122040300c2d80401c040c41c107080300311414a000801d447c0201503840070024441d01c082008110501e0000034000000f0b081082950505c45014802c604015003805a4041c0c3d40e6060200700e142c20140c0c0f104d0018448000c402e50306d904260340019047c100320b000010703440c482c50304640b140761300c5801d5200001890324400c1e5140031004413112018418100014440360041301400c0c0c200855003000144c10300240c3c0041c141c28006040c64000c0721001c070a003d0260001c000d02c5005482c1d840081c0801e1400b2030009603280c40054421295000407101603400640381001c80b521110a9410007529051034181940c1c1c41002d071050703a0390200f915060050000440301d8080d003c1030002d103804012850b1007411035203c2c80320300311001d00380d4400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 731582320 1250 731581070 731581091
    0xb07080f0f04030606091e39090b0a0507080307020a0b011d07020d1209030e030a110a06090f09020304140d081b12040323030c1e0c0a080d 61
    0x300c00703030000d8514200860399442c110704e411002d942e207907031198605904000e04a501e404611500905e10742c41514001000d4042110902d07000c2d00c4c0071200a480092051071805007802c8401800303103444d15854074030700c2e6030b40d0ba88241003502c101807400340000c00034800c030400103c1400055400c44032910454458035641d8545c05102c14081e031116030409040d031280b050030404c406d0029408511030000d080203030b117956005420560820510a03985540d12041000c160041508088070500901110103840c11458840c1c41d5480340304070113204584581001800070702c16503c05064440180503a2411468038039400b01035040503104a8508035908041d011840b030030040c805420100741d94040542c24525030001c0340c41031091204003040b004101103070883d000b0424003500180c3c5403a00c21801401c0a401d104009480450f1414418000081c0202107000e6005010005c940c28a2205c0c0e007550702490782103074441d06c4134026054000301c03007001c080750100c1d000e031421074070a020106000c84030703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 731583570 1250 731582320 731582347
    0xc170108100e1203070c0611030f06060f0f0c07060201151505030a0902060a0c02012a080306010c020d0b01081c0e01030e010b0604091d0d14090d060e1e07050a0b0708 73
    0x205e44500c00103098540c0241407100c180a20040711040d2003010780b843c1041c52141a0340d020082851f0f001d880c00103448820f5502480c02c44e05c900080b102003686400d208503509450300c10301e00c198001503003886801c12001207a05403003801c0340e03000c191701001040070308810f41e00340e00b0003410000220380ea40402409600c400b00140b4004455584108501c4010700c000342800c984403001c918128007400e10132070340c3c0400d03000c40403c0d1500070740b00e903850307036500c0300101c03024104030704000d42140c0c11403881c2e8100070396001b0081c16202008159841c0d01d641c00004200300c4681880c1100203500e02c0c043d910254000e5011030194140c83c800440e04811600218040b5841640200810f130f035102c240100c4801503a03525100d8268000c0a0b01c3e070307440f0b250001041c00001010002070040e001481002c20b503201081030a030258060710030b00000040500e55070716403008420580000c080030b0341710f141ea00310200d042d50a9600060000d0402d07810880d800001e42c00411048400c40d80411011681208 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 731584820 1250 731583570 731583577
    0x1a1c0506040b0d05031b0303010503070306020705120f1306030c051206210d11160b180d140f010b1012090c0f051509010503040609080702040903030c170108100e12 72
    0x250008640c0e4282c600b41180101204860115047c2c00910040c45542da01080c110105c0e41c000702c1c0580c0303440a82c200541807000c000000b5081c02d000003031190466022030068203284039460071000300c2c150358040581c00e480c01074560300c001550800825844400612105801c03200c043c050040700c0303600f0040800c21003142440502d26601041041c0645a800544013409200501c054036452100506103c030000e0540a42c10704140c002c14204200000b2028000341008010400e440300c0c9500e0034500c601c4000b02c00340c40c4050103064404640c81d401406005c0e085c0d1005811900c24140c0e00c041100c0c1e0b0030003246980c031140c1e101c81900000c00e450b130003c403018000d901d03c507000c854502010007000030145000c0360281c10060082c400c9a1380c00c541503a034040d401542c04510031607140390048151240620003540680303071100c40307014113915900a41c0c0c1913205840301e2481e2860f0424002e8114003d1081e404d440c1c0c041c400780c1078805001e400c007120b6610100d041b602c1002c10020850207541 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 731586070 1250 731584820 731584823
    0x90603140402061c0c0206240310020a020f0313050406061803140a0203100510170c1c05011a15070507090b06090a0b090315060906150d02131a1c0506040b0d 69
    0xe0140e814800844000302c1801c51123207440180c003040b246801c0100c0c0d210303444080752a4000d03030302045144c0d8a07402031140c4404900000c0a0b01d40e01e1001c012804450710769130107918080c07490114082246401002d403140b00c1d542040d0711003182865030b52030391151042c2081c040741d00e01074490440c005031010000d8140303001c01010701140c4c1c1e1410004148064100ba40510441d41c5d16107040f1803410004540c40300d400308191102c5040f50300c05c20800003c82a2944010b000c0d6290000956241d20380440011403010708980d044028800c0d600001610b00035a0302c09007030f6400000303081102d507219510010303513032901403d09420b00d00c0e01800120710158542c800c610110000034244501e01d020310842911041d00000c20503e8185640426000301c0000e069030f02070780c4054466048006804251502007600780030540d9a2451041d513418100c001384101111401c00d14101090302c90060b00784c840480d4031711002d9040440100f0796402519010b041c3e142c0040d6260455190707600d8084003030706090b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 731587320 1250 731586070 731586073
    0x2032a130b0301051b070b150a06030b0f03030c0705220c09090b100906050a0c060e0c040f1803141c020714120f0d1503060903090603140402061c0c02 66
    0x340403070906007901c40082c0f80c401000340d0101031001e158101d00568400310303001004c01c0320544d02c00004030300824006203800c0e8450313445080018901c6d815000b0400c0e1302c4040d03802c24440c4580350f081c181d130b0f4020018100540c3d04203000c24030003420f2104e411110845d0016030111a104080b0301201121798158810000400c422802d200c00003584c000c55030340c2c140989503180c03111f440c21402400c40b2003d008030010001c000030211190387c40740091100c8250800700130400700c540c10504550b1400c4212030a8040c9041042d000907a1030750348a402c00c0b2800c001c0d0301100103c00ca540440750200d4000c0300c11340046003840034a0040d5401034410b516a200d280c401a607501c51343c10001407140340184401c03110303409070407248142c00f0b400040d03d00f001c0340d0494203504c03044840eaa00000c0c10607000a5107041804800020500c0300b107400c45400103020f6210101d2550711500120180c0c2d0000c000c2d031b0025008100410300500740000100b42084ac1900d5142c600a40390380070360250741311b050101c07006 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 731588570 1250 731587320 731587331
    0xa08030c0d0903080904021813150b070803130309031205041a070c140f09040503130617190f05070905090601050a02120a0c0506090f010b010c02032a13 67
    0xd11020440d0000d0101281400d03140c852550391449060710038025201c0c01140c010800041214107084d0381d526011000f001c0b0109a18140e40c0d600041a13266140041843d96110005001c03003600102c03601c50b900840b0592640e50740b842c0079a60404003950480810926582c00004654000001d02503075090b41c0c3e982e50344c1c500c0d00f00c00854040500b201e00c14400c41c100a002c0c0002d00400d44a01100c4292041e142040ac3c1c610010f581011410019a08140c407442003200b04000030006111448120103901c820b980c59440498144007040c40d00082d00040c840421128801c8181c200039884a030540452540e001c9200c030001d41c1d03400d5440d1000308000c0b50090100e0b00d4420380d40ba038464003e1030306608090070104000d641d4441849040118500002c00150051150b038240511941002c02c803505070038109a0f03250342e480d1807207420050b03502e040780c40a003540c80390b030801c00036540003401840300800010041c031140308800c48049040400c034895100d103898100c9413000c5250343da0340005a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 731589820 1250 731588570 731588587
    0x120327030c040b010c060c1101020c03030105100c02150927090c01030b060a08150405010e2a070305280f09050f0105031b07050a08030402010216060807030f0b0a0803 73
    0xe0075444040480c891424603091900690740403a03003054041d0000d07404070340002168400c0d1070041c18018218001d500001d003001c090030700040214100c401c107440c8080c84460703c2c14101c07171515144400030b600101220760300145013059405008103000041c9560b04512003c08100d002d00402842c04d540e00302a6001c03c03110300803d2081317025071402803c09010300d44400e4009500b500c2503070396150502c04010081044a00c41070400c181144014004020b6540c6800c40031b03985020440750f041d4611300d00803180c078402c0b42214060311240c03010a44181030019959094030301e9000041030030440c0d003030341144411040f01d8044000385031803103440d01d007620180d4070401441400a43c003c28007648034020003101c540d922408a17a4445000c008910003071740ca0a5000c0320070320036010003400034810304942c003050010401c01540600d10036002c40306040c840c050030482d152424800c0c00003040d064400254807030f000e60002ea0b425982c40400140300c0c008440040c000c0e00701d94020b028264400704202a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 731591070 1250 731589820 731589823
    0xc1207060b030c01022116050106060e130204050303041412070e01091a10050708160803370f0b0a0f0603061e1211040f0c080606071112032703 63
    0x124031200078400307451b28180c0f03980c410244400c1c950444400010000e00190f030655038101c400c5400754040001e0124541e6000001d04a02d00b0040e484c2c880c000050200858810300d100711401c070b80003d130141d03080902c1c0840043d82c1c8000004203a4003c1503681907038412140c00e011000260141d0380c4010300950412140c403085904104020ba410200c0c0f07050342405a980c11210000b0a05503d00079544498a1401b2705541c0200c0c940d2107007004564510800300061800036510880440c0c03085103850144404c0c01201000154074810786c4802c1a9480c283d00003103401500005248210101e0700da032400c00410380c854010390001740840c407600010b100c055070500408004103a03203140098141e01249003042c919459104204490440c500710030308014492a50701c1d5049801801004040d08400b0313104090460004858006615000013548038501036060360340c1141c03c03024084030b180c0301c0c07424454420194000c03210503101c180b1091a05940000e0104240300800710f030400340507008000e05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 731592320 1250 731591070 731591083
    0x415030b06102d110120030901020421030f091401080a0608070909021207030206030a0e0c040c0203130506040b090d060603230d050909151203130e0a1404080c1207060b03 75
    0xa100d0341084004800d41039106d5030055914903504126581e5100d00c0a494028420f90340700545100c540b03011040c403070300711a240e48205c42c00b0b6100e802c4084079001d012900501346000da0101010f0002c2046415440303060758652060000000180c0d0a0b260b040441c60100076520005000d61281007650460806444400c41d51501c14000e1a609045a0000300140001055409505c0d5660b8000450480801c6040c010044c060030400003a000500025100c0c1c0c0020340f00300c29664114000645400d2100886049450303010489040982280801c030551a03540e1064480300d8139841c010001c52000e01c180f4002c1105210440300c8000711a070301d5030a02d03543d6100c0d1001d12406104c81c803c00c1d103526580d00d901c1101251040501c0c002e081c009032491f0b41c0640346003070510001c18a8604170220300c03030741801e90340603001c854625520000b0407000c0d1608208415030808d00980460000760384607003c1c0c1400d01c15041903e20b6401c00c5101814a900140010b13182c4a8451008122604060004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 731593570 1250 731592320 731592347
    0x1815120209090408031e131b0f0b0a11070f0f09050108060406091b0b03011d0405030a03050403170f0106080a0c080609060a1208090415030b06102d 65
    0x350304041019000441c0e440b00140060003070040007001030348100c0103148449801c03101711880c01c02410700e61003020f01c0a01c510021507040b4009802402100c3d810a1403004680442c2c110210301800d101007581140c000c06442d800348081411403044615050000901800500f01800090352070140d0300c1d405035250398041e004407850000140501c02d00800d001d5449074020101040c0503100c0e1410220f1500c181441c0340701d240c0d40040100704004000002d40c1210a101421102d4859150306900103034010340e0000c0107644100003486441d4082d400c0150701034024241006000120011202200310480702c3c800130070038a10051141c550080002c5801484100b410450400c8031500504941c001421403031040b080400020100d035500071805c006072458952400781a1383c145000c402c03541103900428442c0c0d05205565441481c2807219500302ea40080441c003a82d00d603201071185420141000030304004000003034061031290780c40b24003106035012007103030742020503108014114081d0242 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 731594820 1250 731593570 731593607
    0xf0207170a0504091d060a0504120f1b030e09010306150b030106230417030c011103090616140708091806100e031015080f0a030815011815 61
    0x8101c2168400262020380300c1140000541192001d80004422903154101300d0911510003042600d400c1e45d0042400ba86c410184014656660b07070061710515400c0d00d140001070300f42d83c907c020081000c1040b03034449000b810724201d0054140301044075884260000d49009813500c0702a1100720b007404492004100c0303901d4043c15541440402002000c1a0150621604480540c0402c40c00d0640c219001844d100030141000c070000146a600d0342c00040746549154038003203a00e24908507003012a842034501c10003415460b500d010482e80f4140512515030200800c680d08065007240c2d440041c80001d000e20412501c8480400401c0141c3c0003100e810041240184244080303621480c01c0c0240c4001103040180c601000940468507001d1b00c01d000d0005c890030044011842c2074190401001d0320500000da07403000e000004955940e01e00034500400042c1c080e40020f400410700305950390848014034140340c02e064500301000085985422071510114004808207a0b02d80021242c84070b00b20a42 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 731596070 1250 731594820 731594827
    0x30203061806070e09151305190b031b010f0201090209040305250201050d020f1204060510140f1c0501060602101d0a030e0a23090708100302220f020717 67
    0x40350082602401c5031b818461081c400c06032565484040201000c0010020003551410900b0004802c0121202c00101d500d808101113480c140456200c2d003000c40b041c502d80442000c840112054072002401404655030340300d140c00141d0303c61200900941c000c1d5280d0f611442c0e030b18256402c00002542c040065a400182d203070050360014103441c2c40801e8a040161122444140344403035105076691900e1204802040204020156008501580c049242003c0712600c4170504640f090343c0e880810b91020400c501544245425880c1007942012150b10740040e402039514103080d1355054001c08050707001000300f05882440e070711a40c01c0c6403500044030428403500003201a260740154002078208010a10325204907120401d44900805c20080300e41c0400d4801f4407504001c503a03240e11540f1441400000c039030424403404055001d0001402a825110301d036030f0030005501c9400c5801e084013048100340b00300490030b41c801c10404003410003025a0b14100c628003400440001603c4481c04441031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 731597320 1250 731596070 731596097
    0xc0e0f090d0206011e09060902120606040e0a02090612071205070c0206040e0601050c1009030801120503090120151b0403050712050a0209010b120124120603020306180607 75
    0x36001d07044174160700001c81141074210f00941050a96009501c1041c01c2280004400c0e0040c1d0080501000d10880e055958030b490b001c00034684100e03c41c0b100d00c1b400d0540405e044d07034280c0c0d0040c03440700d10041c405454803041c0d91a41180800455940b80429005e01401840d21218040c440d88060185462003808640d9800642280524003841201458000018003039901442c102c800c0701180c64112030071411600710080217850b0101080b000110b4500000911000719a801404243e0010295062001020046940d0405004c0d040e20382c000f4070b460b80075414414004100503000c5c4007007004d002d185c00074511000300204100b252403c40c04000400200b600420903500342c0704083d91180c070194060500b43d10b0441d04100107940300b80010000603002c403901004014040c0c20340d20300a4181c0ea5101c0060650240411100c88100a00201800c05104220200080703040c1c04000075000c0e241e402182c900a0704448400d02c00c0d810b184100c282100820945501c42201c3c5802d5a203404d11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 731598570 1250 731597320 731597323
    0x3030b0f060405030a060b1908370809030109140c0a140307120507180501080c040603202b0525150c050111031012020a03030c0206070c0e0f090d02 65
    0x202006c3d008503503070201d44d440d560317510000042150f0940c00100c5100c0e147c94070141caa42982820601c60000781506051000b0000c00f180c0007107100b054004007802c15074031a41000d80c8180784541e815580d450051002401007164040d030014581c0c0280781880c015014030090320045d0f0401c16942c01d02c10401442560002110030586100810304058079005140041c544030b5030707030809002040c507814000035028180d03000e58100c40b0044200c1d40d000305002c051000301e500c0c40c0030244c8000800c11001e0034004481e05426464803010b000d600c040640d8070111503022400e01c07582d0781000050340940c4240001000031400d2005402c00764851440001700385031304a181ca00c0f8542d00c0c412075121080300203000b0b0700e011b1000c54110009000712034000350324040b1980212084c5c014103a00c2c25011510078a00ca00360034074a503000c1c1c6444040ba0542e02c050703903070090851049922001c104040c1d0001000c025001e00140302d82582c2e10aa41811150780d2009240104020b020354003010702c640525070f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 731599820 1250 731598570 731598583
    0xa051c030510150c0501051f1202030709110c07030f060c0503090c040f2c070603090308190b190509010e09063405041d010b0a1d090403030b0f06040503 67
    0x3d50030700d52044007035610240c0ea420a141c070054529403a01c800c01045601c2621030200ea143c4268400c0c0c48140c40b42c0b1403a120600e203a074042d416030300941082c80030b28026401881d00d0440140928206054135400701d10740380098004030f0f07840f0030001c10441084407502030030300040040c0c1016401c40c41c150407240e03615041240b400e48280d44400c450404061141c0c45071a0001400080d1921501d400e4445101c1d91498050500c10b44100303840010000d02c0f034400c0d0046d55605d41d4900c5425101c8480207000701d003000b1015201c403a5a090040c40c180c0d10500382d444242c801d81c036618651441c000401c109040141d205018101800701002812940407032445e0340601c83c400c03400211a0541020610b02d035104103004e00030605c1303170010700a5580110191081b10b100080741200603001121865013198288500345000d5400e005880b01c0301c1c01050708007411000000040c004a4850001400303400c010344054000c640d03580840303401c9041c050702440e00f081c2c0c16a801e40c6817510302008241e4644 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 731601070 1250 731599820 731599829
    0x5180d0f0f060b120102030609160f180905160f050f09060d060519050906032b11070605071e0c050d02120601080105100f06050304030305180a051c030510 68
    0x140416501e4040161903441200d2507100980700b202e01c081100c101e54003e61003a10074500c103402000c001403043c0c2440c1c0140302403081c16900e481001e0010003040c2d8a1800301c03505204441c60300140840c02d40b0007440307014807502d001c031084101c0342d1600034041c1508140a21140c1000010444000f2a105804c00c503074890030259802c40e80c440d14a00042e0041140f9001941d0141a900d060342150382c205006000b658401c48a0840503100d050406595803001511440c81921510010110030b019007900419224a0309062540002d4280c209003031102d55040300c1c0220304003046107800e002c40343c0620700700c1100741e19588600b0b050313a4803103020030603c9104083c0316000c1d018000c0215141c00641c0750319681c4000407035a003942c450b1030650181800b2250b03400c43c4030b43c041000030320f01c0030002514100c6005450b440d00d152216101200a018000d12083c100c0000d0b510603105e0444c10000305070030b40d0244000d01307112042010036407152458201d10350101820f180c288003052020060365400c85 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 731602320 1250 731601070 731601083
    0xf060207030819111507020c0913230d180504021c0c090308070b0601081b04030206030c160c08100b031b03150103080c06010e040506070c2105180d0f 66
    0x201110350013100c3c0d1101e40701c94050980210364a524078140c650301c4481c060384098090701e003481d94a50a01000c14805c43d0b0b002c4e4038020132664240442c041c2e000c0851800114504404075144c0c40c0441c502d0328000d01c0c07060340000e10031440c00d03041c41030f01d04001c0d0140000310790039403504ae01d014010b11008000f03094003003411795404c03140403040c0c020a5000019903019842d20b40707a00141c1442040d03030104441040c04607a800c00060803803160408115013010248030094109800c640900c40c06801c010702044011204100000c2070021a02c1000d010714810715046100b00d08000c416414210320299110f0102c0c107218440c14560b801003503a9201c00b4400310030150b0100e00800007841c101119407981201c074416030001c000d10540130000c00c903c01080e41165440e0b6a40d0703d440c0080b5800703c40140154110380c021848940c4614962146140180700e184010410b200b43d074200c0640c1d4450036008114001940010100d080603640d1120300100c810b85c4040a043d140e020321042c1c0e410008100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 731603570 1250 731602320 731602357
    0x1704080d0c030e3403030305010806070c05070b0901170a09050c030c01021f110a05030925050d0f20040b09060102151b18040b0a051c020607060507090f0602070308 72
    0x3504c1840b020000030040d030241c200100381e40ca0402038001d10707007070085010030300410000076040ca01404403541a141e11800402225180260002268020014450400000d1030f280100b81c00244003481c09107955150016000205140c01d625200c4485070a5029070440300d251080c030380e000b05031000b07414041d0011ba0800305015404800800741003d05508060b000b0648008041d4800055840b4040c0b03d41194210303050011035200c000140c45a20010302c031648805e00c60b41c01c00d03c14400c400d03489460040030201c1580d40308040315403644140d50303d264409550303140c0792600d805140e1030680c0c26181a07109091200000391621000f0645074103480c0c210300420415511440703001c100c95403502916480340d04222444c6c00308a0041142c1d4401e43c01e1540c021310038680f980f044402c9507001000d810001541d4400c40c0041400703c030083e80c0c03004080c042d170700100b02103009030f510800c0540e640d0071645013001c5d03031420960301d0768106504540c00014140b0000d0701328000c0b2480b81e41410702a004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 731604820 1250 731603570 731603623
    0x30c120315150305071701271d0708120f0d09050a05010506210d0e010c1220010203060d02041a090a020712020703080304030305060a0321020d030c05040905071704080d0c030e 77
    0xf00d00308466400c0081c90480801c0c4450700462700746e5200c61000d000e681071665510241e5540d10754043d260302030040700300010a081914000100100c000002000c14000e2140c2c0740e4070b0401200d600145c0b01c03030b51114100041c52428020120280344030300d09080d0070b403024804003580c48102c502003d090003542e20308120340d0b82c014520440b20a501428240700040569001407172108000402d0300342d640c420130480450801030003aa44a00d00180852020060030307000c000150450060455681c1605802d0072001d40b1004c0c03800307100341120710015a407503a062034407040c0141920700041c11500643c0341800001c030104112030b0829090301d0089000c0d181e8100043c16010a0340c030080440100c0160100c0c545c40b02e00c2c54041c1c5108a03025030f00c0d80c0c90b8500c000d40a44010300400e50009000300402d0001480c0c43e031005070855080d15000b03026550070120172000010580e0155484803000c14401c49010f80f43c0215813010240d0b16060215a002e81d90656444c13a000542980129a2480042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 731606070 1250 731604820 731604869
    0x4090c0c23060f0106170403030e0d0c0510060308041710020c0d02010c03151703090913170f03010b160501020310050108060a03030c120315150305071701 68
    0x120303541c1007140d4041481d2103444030803007207405010800e203601074000050a420000401141250b480b03071645600172001140b44035000d80014003c42c28540c0c3c40000114200080040210141494403a5024070072103080c19490406202042c1c44081c0c104541440001c030494192811290114040010102114401801d004505c044801d074288007040d2045e1041e40015101c40e40c041d550000c02800340d00c080308500346c03000300b80810b100001901c1704102039110072341042c0440c44010152800c050074500050704207001a1082c04001038502a0300007840307080100d00305101e26000400f0310b000301c40702c501191404140300c3d44640312004100441032203002c010360b5081caa880f0300215503910342407041e801401c1d020300405001031003010000701141007220640301580d40503107411003955140c0c2c5c4d030b50100c004204c0388103080507210307070340344988020030325000d4040c0c40007443c139800702c40c07145400408031800189000c040054004101c1d513810000c08a05041d50b101d000046001e9600c0c1d032801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 731607320 1250 731606070 731606087
    0xe0411060315090703020d140601020d0c06060f0b19020d0806130b04050c19141911060109093003020c12070f05010b01020d02250e0f070e1504090c 65
    0x6a070028401d200300081c085c0d040e40104024610300508000703411000d80030744910b000403642d1a0140e8070001d4a000d006000f800da0b0b10303144e0310030301c00802c881c0d89690450381c00c20f80300e40c0040c502050120307161111005002030f602c0391021510003400300f15400a4000c220003c0078000b83d0041c7c07910009400c00c0c82c800d800041441401070801e0003c1e0030401201e120315409401c0798042105041c454540c1248900080200d5451802c0941d080c2256030030b0189a00c402c2503140c00c01d00902d1070f2070340c540c0407050001c94000c18000200207030740c03482400c09088008041c0c400d90300c0b102500707a0200c3c8007109245200840103140c0740041e20703040109000c61030a0300d078511450500301c0210f4504100440044102c410f070b880350000b444480c0c0304c03400683c0c3e5040e400c403408001d60054403165601c0c9450507050050048145038a000e015900c04410b4a180015140626000049801c0208881d000350440410141c1654008540b6030150782c03401d0203000d140100d41c20251981c8641005e00c2c8109550b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 731608570 1250 731607320 731607361
    0x19080102030f100803091e031606030e1c1b060f020403060b031204031e021f021b0901050604140d1b030611091f111b03070e04110603 59
    0x31541c0c0e080c008000100b8540848094a480c070610710302161802010043d101300c040043c0150703603040c10b04906c0480054181640c10340610442496801390000c051000d4000c01c03861303c0005075004c800c114181003010084550b26404600158020180c0d4000b013607820450358170f600b2800030140d900d8a10013801c0c84094045070540045404418054164080d5000340012021200c00302c045410340036050085110251201201403221355060b0a43d19030720b065644000d00003020311820500d8a5070003140d41d482140140d02400070380314a005100101c07100340a0880c1e810946614010009403540728602821888800821004d482516513283e10071000d58031007034054607040c4c26101641c00c90054403080e0348107800c0040302001000200b089443c200f4010f0030701980194080600e400d41c81d0314007102010030811107844038035481c040c0b018420228180008107642c80700c0d08c080510b4072801e40c0110800440c2407041c0070000c2c0420300801400e00c3c0a8460783d44a6a0b00c645180c015919000c0307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 731609820 1250 731608570 731608573
    0x201080a15080c011d030a1202070f06080915090606040b030f03030c19110a11030a150608010f02030c04351e0d09230a0f30021908 58
    0x2021039440c1c804a003580c0d01200a0766004030303650001d00c0001e621751808180c0c6425802903002d0a000c14030f94201000034808030f0040f0b80d030199a580000b54103040c158032150019481c1000d0110a220a010300d0068160007000ea094909110704c1c60b50710303690042d180c107214681c0d4a90101041c3c80501140351000d00d0001500e4482c50724508800c0158040801c0714000400c8240110780a8061098244646510300040c40d405d0b4807a0750b0810300f40120004503600d40306405640b80040c400c3e07881c404141200e40400700c2c8003403030100401e0a480005588a10182c014820008016222000e99003140c480304002c402c80e000c103114407580707896600c3c8030203450ba1507416086000500019410281800d0f9000c80d42d240303c01002e101d40b1100441200c07400070b00c10b03803401c111660f4490300d101c440c6840c1d5034100c04880ba1540c0080d10458a0b94080b541020b80001c00304100c4843c1014a4894a0314410303400300000c03c040311417203000d01254001e215140c0481d980c500c0d402010303101c6024001880 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 731611070 1250 731609820 731609861
    0x31306020301080c0a0614090d06060b0d091104090f080d0e0607090515071a06010306050a08010f05060109031a1b070b090f03130902030456040201080a 67
    0x1240da15800300c0303814140110381175a000501b60344105419036402d0070f00110641044060000c00400030202c00c425036401d80c443c000482c40350310303070700040100e400e17926400210040e99252520760340e18282e038401e00c03076071410400b81c0c0801c0c107004035920f0142d40001019a5012500e41e02c4c001231600381d0034000d0a00ca0001040505a000905c0700d043d2a000c4903076038030503100d00955807420300c1400030042402d0140c600e15400f04459403603164201c1d6050401190746030320f8038003042490090703506c5581e0503034458223240c50010f41c40c800c142e0804400c7c07800354040b60554449000c4442803045840303c0400340303030000b40188000b10082c440743d202c800c0081c0c0e441007a4108510489401d440458941c0620450f41a41e10000001c60b40d03001d51201c810048286072407a00802904003d00a0313580e0b00c000d40014044541440008109054082d00422400015040900e000d4860084087c400c0a10f003140c207410103c40c4501684540e0901e041212982da000003d03001d0304180d048500b010841c103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 731612320 1250 731611070 731611079
    0x5060c0f07030f11031b12010b0907051e030702070302090a02130f050108060f09010501140c070603140108010e1914100c1106390c011d21031306020301 67
    0x8200f0000c00301e000c1d580e900c92102c5240b0030992116001048001c0240d924400b010480c01c1445100c800c2d078865000009129a144c0302062024008a80b00b00010710005610456094290794140c085a0341e517400d0750441c40e00c54800382d40c504090101078030070b01030100090003a54140e0111080100f146040ad032034030b81d5691003040d040300c03540101d42c00b0410600c0002e0942c201090310000c9480010710100c11a4039090064840424000c01d40350121010003024031411000c0040100805031235800240300c201100c0000301e05030041e00722070096414440210a4501c0c000740c00d05001c0740e44928201c1ca50041c0c034012001c0f841070720740140d80380100c00210817290b01700e50002d0000c1a450f26039080e14180e0780401030f10344004071144d0041000c81e280c17540019410700c4071495222100716001301195204142400c240e00100d510200aa460381c00c07080170302c1c5503060b80e0581600750900400c000004d0151401009072016284160001c000c00003690080c030000c000242150170800466076035854 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 731613570 1250 731612320 731612333
    0x40b1b160e01050301021c0209010504050d0c03020f030a030c11060c010c030618020f0403150e03031503070e09100b040b062115010c0f06061d0a06150905060c0f0703 73
    0x1d10031000d0111944000061900381802206d00c8108032600c9040e0303511000d00b189009400000150b410050288800304968840310b10b076641c8603000e90780c8441403e15604c100304140e0406140781d406034206013811400a50002e8664501c1d81c2c1c8078145051144070440440d040d03000d102c0c5103454a600b800c003d800b1954040c0d003e9002c0e902005807540083c144d1540d0742080c1c1c49035140c0401511400c0100b00080b8103544011054071000700000319008001da02514915001500c42c07c86d0348130140415251450108481d50080c403001b41c449102c1c0c648490825101e5030a04440298a910341b8a06a0a0707603960f8131034001503000809241c1c4451411a0030000201c1e02452540c02c1e21030310011a1000500b039508407003d4405070344003203450ba895a600e18604040c4030049910641b6004041030301750146806c40364136003070408a260f503072800c500740005079540780d030041c02a40464010000700c5584604e1080540d8000d594566030f40149440c0d4a00d02210b2410001c0c00b8020320701c010040085 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 731614820 1250 731613570 731613613
    0x7022e0c111f08061c0f1b05030a060b030703083007120e07090204080f0106170a020118120308070216080601050d150507180609060c0b0c0c120307030c08010b040b1b 73
    0x480159440281d40d0175a02440d10b1f080c058194582c6c052030726500080c1e40b507080020394a070013a0681d00050b82e00d50791040281c020700d510089181c0c4d510410903503940e200c4eaa0101109512043c0d007500d0420b0f50307001c2e0005405004141503951240c029084d418020003141c8001d008c40c800c00c5690f10703540c290068445010480003000755083c60300004482e2012076141c9200d807042c60242c10466820b1307005450540384000440101c3e203550400180c507060010b088000603029844003500c0d4a8030100c02400c1295208000c00003140e03222060000309400100d0b141034850542d14032158041600f4103100315051120113810003801e00c410840340652240402c4241d00d0208103288416803503140a80318081180511000159603003c81404038080d0b02c3c40755002110460102c0c0340a004040d01e506011915080307104040c000814810001c0c1d1502c04e2008540c0ca0385000b48481d4104011300001e0300c00c2d0b2050054070700b4085621580807260b2090104115004811128000e601050075000342d07030b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 731616070 1250 731614820 731614823
    0x302120f1b0f040902030910020a03020d050606270111010204030606030b07050307080a0903050705030d1523040c0509120a0201170c07022e0c111f08061c0f 69
    0x14600c01401060300d0302141541c42ea004140032450515052041240007500010040121407007080b4800f0709402c0b9a100814104900f503401580c1c43c450203d10805803803028002a000c2d000800c030014050f80c2c0e4000d034007104416110601c01e40c02c0990012242c0100c1404c017481e16503c002400000c112007030b031046003102c1c420950003020f55210841510b140c042200d001c00480e0300e0a0003c1c50f0a0180c1d401071444034802d0910f1030901c203441c0c5a25140d9004110307503a400c0350366100e201400340d04091004008201010800048401812000c000c40034940c101c42d00450712448a5035986010304141da8039000090100500d202039601c4595480041e0241a4042880c01c0405a1488040d030001d9100340c83ca050078515100c466402e109070025080423170000da00741c1c8502602e85010f1035145100c5c42c0b205030358820f2002c4483c14082041e40c1000c0e0141d1080c0c40e030104400500390100c20101c0402010705101c3c8030b0b035441101294007081d000031281d4001d5002c44088042010050400703941340d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 731617320 1250 731616070 731616091
    0x121a0a0b040f0503010b03061308070b18060a0c050703051305060304050307060e061b0a0908010e160f081f0603021302180102160b070c120303020a0f0905090f04030302120f 76
    0x103d6641060500302d0344400512500751300640c002600001c4400d408003240b51240c1c2840e86408101d80300d11000b00019520084e00590700b441459060808221071038204a0014081001101854001c0c007507104500c001801c0c01408580c0c0c40780702040054403801882c0c060815540c03460710f483d001c0d840c6d070700c0030780b04039042c81c50018850b40c00302c40050020b02c20400303540788030741c070281c440e03c00180d82c0c03c540340c0d2104003c0e96000c0401c11820038003842d07070b1100e00c420041c658a1411083d800410843e40c0041140c58000c81080017041c00020f242c1c030105014008103800d00303440035202409800b05800180d08000c502c0c40c004c0c85501964020407a42e8140341a482c524580c2038012030b12021b00c4403a4054a8044583c18020529200010520188034512006c00307074be562013904064440c082c2d000d0b408283e000c07400e000107580100d00f20040c2c15461904040b45420719000601c4280003400b0a503440c04131200040825009030304880303401204002d0301a0030f250560411185480440741820072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 731618570 1250 731617320 731617349
    0x2031e060a0b03030711130f2f030a050702030408060106022b0c02010305060325050916081501050d0921050901081303020106170d03110a121a0a0b04 66
    0x70108a101d034204100000b40514500510740d100d056078001001d080f6940440081005203508455100701c04074084c9102000c514170008540812001c4011071468010050349014541c60b504610100c0340e0042111344001460748808408918500640d04103100e43d21441002048403600007940800501c0702030b890a520002d015030726280340505003824004031311841c401c40d005600a82040c0d0344010081d00f203814039400c0d059070700d44081d0031001c034800c2c202d4494414061030420802d5241d119a100c4010900d2105081d00109610002085850310702a9550581101ea01c607100301e809151542005011265890401d03d001d985c1d5080d84920f8031080c010f038400074500660643d0000c2c641612942d020b9a206016080c54001ea000100c0c00c5540c1d175940441c071400001d107144010301c0e1250042030b4201021001900326000d12000c003500f050240948a501a80411641080c1c00240d1022804110550480e0020a02c5160745580310754108000b041460901016200f101c4109000700707403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 731619820 1250 731618570 731618581
    0x3180501030e060f15061204020f09130803040609080a0305090705010e0f01030908090301020c03070c0e011401030903031508010e010f0218060a0e030307060204051207060207090c020a02031e06 85
    0x442c0d407140021207660700408001a202039001c60015071200c08000c481048403035000014000360f201d51003d039010f800813002e01065041c090400340051b40c0a441d0031320f941c1424808405401c81c0d00d90001c10042c0c00100284c100441c68002035041648010019201e510307504002e40604003ca070380c00450302ca80c000c0001c6962040040b450300400c00b81034440e00810240044004d01030340541600da482d000c000c0200b00e82ca0910040014140510117103882d10064500764100301101e034807140f403103106540180282012a144218000350900380000c0d4104d15240c11b40290070810545070800b2264440024090300640003043c8440c180c800130025914ac440141c0101c1c0550b8107110403c000c0300303845e680c150404900606002c0d4850401034124100280028079541c403001d022100f554003c13400301301a0800030409000d507109040a0140542004c0000755580c02c684a030f4404c1d0341d2219000306d9007034001d001d0300c540640c001c2c05450300212100e1400208401401c0380c1d030200d12980c00010b5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 731621070 1250 731619820 731619827
    0x20a1221210507083403020901140f03190b04050702030c01060602060c0306100504080105010909060608011a21150f0609100e060424050108011d0a090c080a03180501 73
    0x307204032540e444240c403c0c0c69144800b000005c10002d0302c4480b42446200d42180c41d001c146171540650240c1d80540c0c0d44000c1000140301d440c4101b8041f1802105120884040c603583c42a030703500084103840d03104003221800b5064007a100b0303482969041032410081c0951541e0104c010302030001c81c00020300026544503c03c070fa50368000c6400804008003407000c03455500c5d058079420540e03d02407a00c24106134a03a0388582c04c40e4070a17402041c80781e6070b400310f8104005003030040900525846008129054601550700010341d085240a84a02e0020000c442d007884401c014800905903803040b9a0030355403172040700c9001c14003070310380e001e440400c10005401c41c944047c040744101c00701100c000031a8a028441211207001400340c682c41500c40040a403041e07101b9907158050044c004440751001e01e0440090800391040c3c0281a010b45003540b44001110380c500255000070814000044552440c101040c071030003250045002c038019a082242030550200e11040d0720304d0002d0403015035070f50341c80054 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 731622320 1250 731621070 731621081
    0x303020115060221070b090303041101093f0b0402030705040b0303120903040e0c0901110d0e06090d12050c12031303050310050303040f1a0403020a122121 68
    0xd40042c3e11000e00e80340c02404a410080384020154a49810035035203554404100f0b20403107c0001c0da90001c0200000d0000074101000085801e003417840042c0e081044510f02403400c201450344a8140c0d6032140b0491101c00b080c9202d000c00e16020340c00200c41c80c50b16070b0210310242d0342070b0f00c203108020b0f020805103060300c1003000c0c0b864010000c5181c0139882101e003114520003010440d0500091000240300d070007815074948298102011241d6600c0c41d0030014040c9980d55064004a42c0701c0120500220307003080c5411103088080300c009840e0030138a00025100c00e496040203146007002c0c99030181c0745410801078039443c104407090f56012120b00880310210b010484d8850130800300d0400010119001d000115004501103070000b01c16510354021a146501c158055404840740d52010006034001d00d40d551040e8940c0340c0c1c1f680ca0540786800155503101203024a0002184003ea002d0030860300301d007040810f51078424841c004080300d01c00949480c3c010314200c05007240e903851000c90b801071032084 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 731623570 1250 731622320 731622329
    0x5040336090b090103120302160c0603050a0e03040b1e04271416031b080a060b0c03090f0a09050f0612062401051605300405090406091b0303020115 65
    0xd080050f03281d42c1b04c100080200c80f03071203018582e01b04261038140901d01e080e45110f0b0300a0f841003045a01d0550001c0481b8402030031001f0051070020400c1d5900c4000c0101d074100d5503201c01c13140d01c41c034220911070f00c06154030a07001041200020f0001d0310070390303404420980114140105098614076140d80c0262548203280c1c84404035000009220b02c441030072000c1c01c2074918600050f500141c010074680d600e0a900d002c82c01b05542d8010454924014001c20000e0b0800c10000342c1030140d41c4081c01e07628041c0c0789185200311508481070346603440c0c80030840000e01c14410103000a0802940c1ca850780c51055515500880526222407016070000420302d01541c11071041e0901c2041d4402c20001c03140341c1d1a401030402c0410801318a04d006600303040c43d1a540500054844541031400341c1c0c4820450681645803000150740b6100281150400d8030225601621900d41c0ba944600e010b038000e109041008181c90803060004144a04c8602c500c07044d248642c00070000c04840819000004015104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 731624820 1250 731623570 731623579
    0x706170705030c18031f0e0a030e0d030e060409020d0b06040605030a0504050c0d030e040c090b032404020d15090506150705010b09091c0f1205040336090b 68
    0x3c2025000e015000b0306481144441802500340302000290070b21142c41a405800580e0f6499120788603510f02c10300d03200448960040800c80110740d03000e001c418900c10b51501c101e140b8030f1048240350050407840800300e4010308940d541c503110440324009400001a04182521342013441d902070802004940030703610543c41d0f40e411551002e1a660207000010002c40b035600031807204e60003a03101c95201c1800f00d403094681c0000505206c1c02c2c001250403d03500b51003001641401042090103000c220b9400144952103074101c1c144d860b000c5180456090301264120b8400903856828180c0d40d801020380002111a0500e207543d03801041e420307240195002d5074892861020608454a180c005280f1288200004101e000440f030004a584504903580703803c5070002e0000c019031805264407a0486080c50415800e2401c501c500101140724000c0400c0c04107596a02041c103040c0a091480414416080700c0d10a42000c01d07203903001202c0c58121043d85241d1002c01203078643c0280902424018041c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 731626070 1250 731624820 731624827
    0x301020d0e0607120c0e040b1f03020403051212070516050610030506060d0503090d1514090601080f15070516110a05040605060a08130b0f190507080408090604170706170705 76
    0x11b040100410b182c60074246c0c4207040b035120460078000300d00d04001d0303da800e4900588403403079402e0032420060a946403511500080080c00514994030700f002d5007040003843c040ea116a240c002c882c103100d440b006d01610318440e000401200b0034400300c400003528440c2c81504c0d0292510000d0280b01010742c48004c089400c240720005040c241010980c0500780900005a0b449820280d0a0111404410302c2c0010104850401c00078000c20040c0302c1c0142440d000520b58690408800c540f2030076114200c071804004200072460040c460019074008030008400c02c2010741480c9003d842d00e40e85150110301415580000040c140b400d440740300304903000a003100c0c0c03518182e49001c80b01c1c00001041105040211a150000304008203000303403103180000710b6566113051450310620442d0082600b041c01c0741c108030400c0040f030b9120452075089540034a21644584814000901b9402260806c180ca14894008100b11003000900d543c1214216195010f010400000c1068102002ca611034085501003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 731627320 1250 731626070 731626097
    0xd1106060321040902030c1902060f0604090201140a032f0717190c050c120c0f12030d06050f03011116060605060403200603060a050603060301020d0e0607120c 70
    0x2d21a6003001d90b50128010302d810b403507119860407a04103584290320310f0004a4034240c1080c090706d0f001c1c6403490318002803031146482c1d401441c076400014005400341e41c95403180300459000c0c0d01d55070946c100301c0c40c055071200780d010b41c01401400400d28202580300501300304540c10451403002048910b8407a05c807441c1207101d880b2a0315420001c841003d812808020134413911640070310307000031003003695900d1900d050603041562800c1690b400710380c41a91800d5844005500016610700203860941c1c280000c90010000a02c12140c0c1c500160f41900000032151000d0869510400c1610011030f51000403801ea9000d0500f20f41e41c418005508160801c919802881e51f1904d003051240f251401280d02034880300072640540180e88203c4136100c0b825400c0d00006c0344161075a85a030010341c1c0d101e046280c8140002c0703005059100340c501410b400030200307010303840c2034040791840e03c107a09051104002e4942d0103680e41000702c801c07000081c8042207141010401d8060459143e006945400c0a03460a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 731628570 1250 731627320 731627353
    0x105100c050a140303012405041206060e01090207060f09020d170f27010f0e15040e071115040f171e0a12050108031b070e01080d11060603 61
    0x2408815141d41c4114140400050f441c0d00740000310740c0d9104061500c80d4546006d003040c8003410349000d0030b07892440301300d810341c3d941c4030058804581d86010307040f0b028150350a03e9801040590007880300c00881c20008030b915011900108521881001304012481c0b0014881007201c5106a0080d4421800e28540c40413803900b105000c090f88a99103076a181410543c2681c1c202c1c0e0050100c041c0f03a040319020184100d6040100605106083c2402205102d9038000104200c1001c4c5c900e07403090304a4840743c641000170b81c003030b14058a08a0b1220f00d00d4140007001510350a14400d5203e1980700310161490000c00b2050040d005e50f9000700790340f00000e000d03910701940204007038079665210400e003c0030100101940c003035103603401c90b1000c159449a920b00c00901d4a1000340c90740340103e062000400540d8000001c6546282c0c03400c10080703004400307581031800c180c002e910a442961740d9a00104e810300010599042c885480c0c0c4540c0c005424441c50349441d06821191386505400c000c4991001411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 731629820 1250 731628570 731628587
    0x71209110a14130b01050d0903090f050d0b04080a050d14010509060a030c06030203070c3203040f092d02030601032a0e04020d06081606020f030a0e01050d06060302030f0c03010510 79
    0xd0506249040101038024102152300380c1800740c0000300741c00d2040101895600030003010704400c1e10700c0350b5200402c1d190741c040c8500141000b0401e0b00c00141087e0103521481c16100702e66040345044c0403003503404501050502c1c0a0117080e124039a920302003951450403a51603011130340d00103100184103107072520a60082d00010710120901850030400e200103618001580031294074554622143c0e1014850078003414000384091884ac0d104202c10701141d86811402e4040715400340d0003284000311030404001c1d248400180d0801210f40c0c00c1105000301d4181c001d076101c8c80c0700303903000c110020340c004050405103902d0707841480c0303410042d10301a1810701c81c400c41c0d010341c5405800545406103000d0302004885043d032010f40d10390010540035010000ba9040d0350000c02803480203040e0f0a42c603a60310b6840703202e23030b1090b0300500803995014190f030307401001a16241e559004007080030640d101c0c0094084c2d401200c01c01b03240360300180003420545130780d403e03241a0750300038000000700c1e141d1040a031001c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 731631070 1250 731629820 731629841
    0x305090105040f12060e0f070509040c030f051f02130e1005120c181b0c0f030a08150904170c01090206030703020a110c0105070b071209110a1413 64
    0x6070400011a039800d090803604004c01c3d694000c1403c1900600300340c002c45a40041e511603c0c1c00807a45114107801c0045c2c09001e40e5421100480c107a01d4a1406d50030180e6282c0c001000d0021904942d4103001c404036030f0421419607071324000710b00f084006c0508101d10031140018a1440b120106000d0068007015042e8400000f0500f580c0a940f2440041d4800221108000096111f00050551402c00c0103022a544400c016051460300b4000009615081c0c41e07901c05407078413408101454007540401c003001e03d544030181503036603680290000605418049503950540c14089606080c2070a2154226218640100f000d4020040d080700e50101540301110000c0c0035921180c00d6030250b500c083c000c41c0a070f5519140140e4941403078002070036000c030329110b0041507088104150b02c40c0e41c00404543c2c00a5000082600a95841e4410781303031100380030b81c220a15450505a03c04214100c07101da6001101180c48000460766070035070209480c1c0c0341039402d4121000b100c010040f00ba1a030000750208 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 731632320 1250 731631070 731631077
    0x609210a18030818011707210608150c0309070b0c0c041113151e121a040e161502120f040f0e0c180f1309060f0c0c03050901 55
    0x206181c10500452590003d4071a0380340095a400308192010000902c50401e00307007820460000ca101e0303e03a24030001c0005051082911103003a0007001c5603132001810711021800c12030a903d0325405591148600012122503411078041002e40384800c0a480c0f190522400420301c02d4201700d411040383d041031940c662148203c400d02011070340c40d80982c820843d41c052a103a1609407101c0014001855a40002c4001e11143c41d600340855202d407000309400c0c0a4402d47c003410110550468111703980615003403007180b420341d0910000d41074440781c4522920407141031003803c80907954140c0360641d04603e50140740010004021983c41c503003d801e00080c4038015a801c280045c290034070203a0000f01c2c0100301280001d0705001410404076048041c041400e140e5a0500d00200051014400c40888040c80140300f09080c6107030b5142d00d00f090007090083c002a0580032044182d40c003510001408849040c20407080703020740d40c1684a403488114203030f900d5510001241d1420341d070369031006500c07030f041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 731633570 1250 731632320 731632337
    0x9050c030a05011b0513060804021c030302180f0d140f072601060e150f030d050d1a01170a020d0908040905070309020f1201021c0e0609210a 62
    0x165a030500c012200c482c014400031440c0000c86520204142049100b9014400e0500c8402112a04512a1000c0c0c0300c4904102a140c1c0f02c0307000040c8600291130100000001e5035880004243d410380103850380c040302444000c0c80c40104000c000c03014003044100c3d508040351080410110b10182d01c060503100c0d000d0107031000060220841410000d581c1c001a0500c01c14103040c0138604c101074401e00384200c0b0382008105090406503580c1c1c07450000742401c501240541680074903561552560340c2d02c80e90050448085c84124807000e0042d4104031582034030f452500342131103042c107072803480c04410000507540d00c1a00303582116229800d01c1c0203410b03214000d60a00061400743e420b440f03500921406094001d031903510f400380c82d00980b800100b0100405003040c42010044c2c0341c280b01240c0324602210303a40510b59400c04003500902461150307a86104c0290a00c2c855600303c0d41c49045010007000507070358581d482d80c94141d50b9040e02402000038a440e250301c81000340d40d070406401900c40f6890031511 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 731634820 1250 731633570 731633593
    0x902040203150a080102040b0a050d1b0239010c0f0b070203070605241014040b040f08030c1b0a030503120a05070318020402210411310905 61
    0x40360011101200b00d414001c042101c00c0c80d115800348002e2521200941c0382030700304600c01b030141c090030b40300c4014072402081d40340c0f03428402e81040503004c211400c0c40d071041c11601c00095661107181d2000400d400d0100c03d80c208001c4036102c403032016403c042041c101240300c00c01111a15030780103045d6041240042c00d1030004150027105400f400e500d0303004540302c07152130034010b0803120040c200c2d81d5140f41800a00d002c150f0070300c040d1804c0200407507540b00c064042e0305080d074000c20f00c043c100910150004005c249000d811029000765603221403850365444d250740e0310540e60305c02d40d00c150846612a0b0101022010303070300c000e0012914050f0212811503600c0d40c902e890b68003d031021080f004180000c04c85080d8117449125401074042c0b4040c40051300184d070181c0c0001100c078006e070080d900021745455241c2c41d10909401045d250407188801e14040c01d1001c028402014598031803045c091070841003061840c01654503451a9922143c41d118529088006005054040f50180507501d039214 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 731636070 1250 731634820 731634829
    0x110d1118071202121b070c03030f2d321c0c0c1e0605011404140105010c080d0e07061d0306012301090b0a0c440d020406090303080a050f0601050d0902 66
    0xa0088d442901c414580d030554107400f034001d000d00d840d013001407426800c5010850240001c0000e8100341c03814480300005c0100704100c0700d280034028004110f0000d404420003015241c00900002501d00031143c0c8031400005140242c4d10700c00849400030741503c80d00000704001c1d9034503a81c0072684c143d045400b040656114026208240d01c1007800600310000d0f8041400d0a00070330b41c03044c0d4250101e020a40c140f00c00a885044103a4014102120101d800140c0460590250340c004007010215070400e5920300c1c00030911070708515076008401310302c3d4403c20381d8140001c503281654104500349450500002d43c088483c0d9400708003074100000d0344000034424203a10010003510155664041c001501800c1082c184030560000c424401c0071001c4003120620030b503d11040c240d1321054114500c0d8011900742c4072500481e110300c5009480044d0005a0700d421441c20b2080341c1c402d45402506a0718102c6a0003103520440d440380c020314034180066840c1d8410001085149114000019107114940116 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 731637320 1250 731636070 731636093
    0x90f03060b190f1703120c07140708120f19030506030c090402132409050106030518070302091e011211030307110d1118071202121b07 59
    0x54500e03a64840d000501030600e80401c8a14010030018000290b280c0658103400d045184030b0240949620002d200e42d990b4180202c408150000c4a907980390b06101e04103030348542c0003920484101d4483e0507940d60318000441e080702240d1508010708525007548012814a84c4461030b42c080300d035020425060152004646040244840d80e00040e8070714100c0149850110304200441c4070340c840404010040c1d50f0021441400c0038510030220f0b02c10007003c55110000e21004406034030264904020860032280d500c2941280d1950b0b130140900e856031304015880c0341d5a0050703540b090300501c1061001d400c0c540940d540100c0c1d0300700c6c84a00c2c4803150818003801d4034280c10551f241d43d469100c45090100f08912400c4082040b405549021807940e40e07a072400d031034030300c50b04e000714410300d05030b4240440495116100c0c600680340c1d10b18000402c10100080600f1a961000b04410505200500c13606100391001e43c402c10a07910080d80303039110103100c02c02c1503004070029443d04102d85800503014041c0b1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 731638570 1250 731637320 731637323
    0xf050c011a0102010c0c0f0f0f0507030503070b071103030a0c0504080d030603051005070c1104180b0a110f0703030b0301090c17101e0506040905030c070513020307090510090f03 78
    0xd0728400c8070600090075525035080074802c2281403a00c2401084404203440c20881e40720010b00138181e100d1609042c0340307451030405452401382e404e002061140220040c1001c0b880303020800d42c50f945511050b9401d421000800076140d20500004606c0c0700310754882e02c05800325040007802c05036244603131458441d440d1014030000751203050130420040d0810902c210740300400c81c140b0192800c4e0800801c0c05d10b40d4800070f4103140b8005d4000280391101d500019075014450486a5103001c1800c2004021205950000a03145003850003040c0c1c07040401600c44070704890039000c0c901142034900300c001c3c00800781200c0e4513542c0c0c1c0f6504c0c000039031103a8040c4000d00c2c0440054015210140c40141012005007a100c09541443c103685800c2903529040b202d0765403a2070300040c241c0c40e40e20204000b40020a4003c02030311001440010b0308000240000031100c00320b03180c940c0102c0402c190070980c04103940e1007001c02c03401030f0188034510b0100d824074040c00b141d107480e0000f1039035186018604103440d4170 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 731639820 1250 731638570 731638601
    0x41401080c010206010f050607030f170103030305180106060509060705150403090e0a09020f04020a0509150d06090b030615030a0c0306050a060504020a021f022b1415010f050c01 78
    0x100508950f01802118014089041903800c0c452500c804aa010321940e1402810018807291403c161401107402c480024100c0701201c115607100e280183c000e0600b03440100e400c3d803403800c21040b401414054001643c01d40e580f010300344030450301844802e40080360216a580035034610b01b4981d06890001510580c080e54900b207280b450401c0400e40800c002e011454007a04103504140540ca91021121008006960060341c41484401c11540c0c2c0c018514101c0c2d1200c1e50032914000220428007506954002d1041041015611030003181116000c03154940c154000a0008650709007501581c681c42c0c0029042d50216459a07442c04032025254108440c101e03655028080b6817203040c8561000385c04240e030118a00414880082c0d41d507201c4456081c0f11181503131050341038440d43e4042d81c020f020800d075240c01c8580d1000841ca0b01000c000821110b9500e09001c3e0040f810300e06800d030340628002440b00080329202401101c5401401c1c0c80001031041c200f0602040045c24812101001c66114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 731641070 1250 731639820 731639833
    0x307080d090303050612070302010c0305090616060629031506070b07020706050403050a061e180510060e07050d27050c10050f070c05040c091415030f0604140108 71
    0x2e0050102c0303001030841c1d4000c861030701c40d105c5038010004102c0e083e40d0702401d0101003042207140440e01d521840c04250740205000c684007112280c155810340c60030b80b1a83d4180001030300c0f16025a4207041c8a60007a00c48019810f5881603458804021030b00005180e01811003003c06801040c0d16074450b440840300100601c0400071034079814080e07000513140383d1903e60700d81450b580710141d495050503400f900707040c2d8034440402e0400030350b5101c018410300c1c488288400d07a5070b40e10056008080010640f01402003a2100742d0754210791003410240c0700e0711000195240c0710003000321100d030001031800c4030031950344010441000b051206030341110092021502ca16900c0c0c64901e0514041c680c2c158082e406003546030307180f95080810f0f1103507400070091254a81c2211304001c081c000190b070009070064030f8890883e030b020354131200c0c000030b58051400003140304060318140006640c0b001714508485e141132000c5145864a09112500120010301c0410307524a020102640c0390420780c8801c451fa072100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 731642320 1250 731641070 731641073
    0xd050f040c08031c0e0109020339150705070e0a090213110406181e08190f1e02031002030702010c110a080c07030501020a0306090e03031b03090307080d09 68
    0xa00e00304000c1c10b42480034604110107081242c980b12045984403014944036000070401100941c4000407990b001000c603027041201703000407a100583c2c1c6995002c07245003490f1480d11080b80c8182440589005071040890590b01da01e4800310742c1020500711004c0c001c1e100001882c40403102414094043e40d00d000034440710034410030503070f03009400307607008a14100f40b1811420524903050303c00301c6070701d17060012101c5a0303840c41c0c3c0c4911600d03030842e0201c0261004800284c103030400c2c1002c1a20217510458480c890380d0280d080364140b0b006c0009061030740712000d8000041c00d00c442500b040c4511418141c3c407a03556400a410940d01c054210081d550101c03c001ca100c0c1e090083c0000440141408101e07034940d81c2543c0e48a40a51700040c0c50348400240100e18003804104410040d9040301c001c545400c1d4404004010b840c4d42d05c1843c00c4a410700d00e08203601c40021003201d01500c0e060751101940040145601038079040105080814007040c000d41c030114100340010078aa04040c200062500e046 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 731643570 1250 731642320 731642333
    0x1091a010206130803090a0b040807050708070e1f08010f09030f0e06070b0903070f0303050402030705010521190204030b0a0e0a020303040b090f1c0506071107030f0204020d050f04 79
    0x10202110304641c031860030f0104141d00006111150303600910201c0c0c1d00d90f9089440391134210010002412a91442c4c03c01c818085010003400350a8800d00554203402c1e9038a09a55030781e181703070180380040c1d10b54070085203c540c5401e04102c038881c9426010705040c1c5d9100e0004c0d085903440d03408000344588942c2c80300201a40900304800300f00542c101820f00c008200c0104009000e02d00005250203c0100410300784581082a80c1e0510340c000c8001500395030919005010300030588040340203114a044c04030f102d44c080d005890148511b03042c0e103207070140d50b031103418110301000d402e49110400e00007052980000c84e0000304081c46c001c07034402c800e508001c8402c40c21108020760020351a003100d0300e004010f9502104840c212400100e0050f1103064800011340d0314107001e45a140d019890483c501c3d0100807101d02c1d0092203003d481568403a68400006813030300d60007a9a825001e40000a0610000c5c18406007407000f103002400c01400c0030000b400d00c4080300d038140e560800340540c0204001c1000b55 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 731644820 1250 731643570 731643611
    0xb0c06090f0718141612050f0a090c0812040e0c0a0e09100801050109050a0b0d12050c010f060f1a120c16020d11030d110c0d05150109 59
    0x111034014064070000c410100d4442c0240c1c00380d4000d465458444078410052074000b0580a600481030b00c01d1410001a112050003150f8068000300da00414007800142d00c910070f00348185100b1281808a960780c0c2c5040c00204100c90701107500c02d480a41c045001d880400c0802200c1c211040300d29551030400c03d804c4500e0100510070b0b45404020000e00c2400c07a030084100d040c8110648120302e0303944580b1200c041400c86038011b040903600c3d10000194140e9141c0203640504040041000301c5694882030001040101c00003500400080c400c2640541c4501d005015aa02d05c2c800040c00701181c00001c410349809034402942026045d40a10101c8182d85e440351580311403401d01c0b0300e04050441d03070b004003103001400090442008103200404910501500300080da00409a004029503440d01c255440d8000c004a4043d100d14408050803600030558074403d1900b10008103202d0640a0401400a03012803040b25240140190b010303040740850b610a01901c10018049032100202e0303601030750140d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 731646070 1250 731644820 731644831
    0xb060d240b041401180522060b0a050f0a0b030c160b040201080906070e0d150e010f05150102060105100306080d12140112031d03030d021b0105061c05160b0c06 70
    0x1e050000420400b05c885801c00314185a840011842e680ca07001d2140f61802d25038001e15942c0c4004881d081042415488500440030807030300010b40303580720020b000c5c1120346d981c649038100e154050148038803081e42018680c406002c00d269440c0203d40026070b80d0b403104584044902c000c514080c4000c5682000c0710b140e00100d2940106550310303082500819015142da941401002e1024440060011900c5012551258800c0a00c00040b0540141e0700912500741c1c0c400d08245000c01051601c0d44800e0814200001640101034a900707060400c81403008481016042c507648010020381d0000078454080c0d801c0d02622004403450320305131000300750741d5070001030300398224003030010b008a0a807140c51b2400c46404d40b422005403042e02d980384074806880d40903a580342c80080f604e44070720f801035002055005403003a8111200d0340201e803403c1c01d0b12019a0352035440303c10280000040c501c1d00580404690281d800c86e403120100f20840521268690842c481c0c4c0900011190301401c0100101500f10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 731647320 1250 731646070 731646101
    0x160507260c0304141503070c020a030c0e070e0a06050f09040f090507060e041506110a0b24090103050c01120209100809010c090602030a0302180303040602030a08070c0b060d240b04 79
    0x200c490349038181c80b44001058441441034230300805041d91514550300002d150310804950b012074032030040300e42c141422900e40c1c0004500e4400030385642040c105171011560300f600c0d140c0c00d05424646658058001c49c16442d00a56151100c404c01402070080c0b1808074000c0c009084520304081000700101040004680198100406d81c42e43c01c0024100070216040c0e45001c4140040c1d090b44607060404050000d45020030200c248910038001021007040301017a0f21850b0500403901c02400f04200b001d10000d405038004031864900c550151040e00789920301b401c001460300c0741c0c0d01700142101d014014488005100203081086800c03092260609120b03060800c241c03101c1c989a00250b4074410100020100741d0041166a907140c030808108810001c001d0941c0d4840b511a07100075902d4000071071000000c0d11401c01318100501800c1200c00c130a0300301c492803c65607140020300c03502d5a81003204444410b2401d050140d060100403d0304021030800030302140e40d1032040100010380300f4120b24003104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 731648570 1250 731647320 731647339
    0x7020a09020c060a05070203090306091c032c03070b1f05030303040c0312020709060330020a02150d02130f0512190311030a030203010e160507260c030414 68
    0x30142c0024a8580c0005205008a01956411000c80c114080e006016803d8440ca0040c0856054040f0340450300700c2604682d80300010001e0012019130760410000542c0d13040030a4041c004003c040c00e80c1201c490000200c91820704550740d13100440000b152010540400502c10540c0c41842592280060804030000c50450500e41c88042024402c0e01c03004042e01358120f5980550f50003401071400038010004200051030f0350307040407100d0071402104d2007032103403100101442d10304c8070000342444000d00754010911400590b0a0103c6441203a002d038140b24001d001619500d1028001000c1c40c000e4004a94451840d040c8120300508030f82d0000c5104601000044079651070004501d220610000030100e0f0707034100b900703059800d010000a088003601000540d9400140c15070001d60494402502c9030009035504000d17140c0d01080c1c211040e002030010090039010030040e02c1c2d01409071103100d1190100402100000e9081d0b4841841150741c3d400200d4100481c54a480015102103030513502c9010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 731649820 1250 731648570 731648587
    0x501060c0b150415080615010201020a090311061c020a092c0a02090a0605071104090f20031014060303120408070302070504110d0c020c091504020c03070807020a0902 73
    0xe81c88000700344a1075032074004141903259442d0f4002c00e07000c0c8100c012007440036482d0403405407a181700f102c0d48115004a00015072595105100b201c15800c01e66460404186c119a1002e2074158480c558503808882480070b01b1a010340414102401e9090a9005079500d07407949015110749020f5025070000031144100060042d1028104040d0490300e8040c03850a98500002c00001d003c0c819140c2d800c40701c508004201c8903004001810624000d02d0807401244c865000c1000707590600300001c0c0103d03c6d0040e014001000c4d406041d46280d680125010203951150129251014000030114125250602011508407400000e604090300741e000d546010034000c286003a070000030304010705c0700c8000221107080c944240298000350000910600030002c0c08021840103400400e015903600e444c0529038803226000248a2040c0003002d84082c80d15503882d202504200408010242c100b6002c10603000036840502c000c00340d941c4642480303034450002e401032000001d13403074005040f180d10402000c5d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 731651070 1250 731649820 731649833
    0x7050c010f15080616140c031603020102131203020712030203071212110c2e02041d0601030b0d120306030b1e091f050709030206070501050412030c0e100e03030c03030108010501060c 80
    0x321b44211809803590f642c00700c0c07911146140301c0d049218400214990a00040550640043c003e4107044203000310440e480d03500f8a21091201ca034000c0c0540d2140c2d100b000401000a02d0301d003400d01a0050300e0912505450300c418140c404018200047c2d501c1e418030f50f00b42c0c1d0a02c01c140b22508080b6505003010500c031004c0356030313410300341840c1496402e0090400e0007424800e195245540e49100a646a44d034070441d481c095958405900c10380480d0000181aa500c40c0c404c26418480c0209817030b607004240d481c0e103076403046480000410151100303000300201d500f600125018200007082070880030341d04010900c03451400360032076120f60000403044400e8054140d41030388407030004d000002c46489203001a02d407241e40358402500300901140b44414400c0c10761095105138001c108145806112070400c80c2124a0050460701194096402c01d09609050520100c14400303402c203405070840180000380395170890340030fa61a540c0008014400a0400e000d10703401010b030b070304103030ba6005203d66580 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 731652320 1250 731651070 731651087
    0x20d0e01021b0a21050114150d0204060b04060e09010e0f07140405090420010521130503030c0d180206040924180b0f0907050c010f15080616 62
    0x801c40c200581000c0c009030f483c0ca6841d80144001911520040c40b148104e4602460164094505500c0c0c40b0080c65205050079449100f60a05c4420203541c086640821032841d64402c001c1e600142d0b200c4010950114a00060000d000c2585075500001e80040c100300100300140c00a900c0e1196940a0052340021410540e410006508185a9550202c40d036184d00d40160340c40b10340c1c009030000502003404400910f04450101c1020040030710b50b10030340191500e229803040c0a80e5003030606007018140600700e50b030030b80207601e5842e0704110b0200b50703e8103441c42c1c0040d1a03c2c4203418001403c2e860200840c0718040140d01e07600c08581402c18141c000070154041e038400d0070002e6488201414039819546480910200f20710b11074041030b500e81326079043e00400000311401d80303803805081d4481072408000d1106085002800020b050b0b4540c8800c4805070082e01540e079056403070300d094010500360341c001d4030b40100210f142c1e038002600e02000540b900300d02411580c0c40000ca0540d0319890340c0c0c0174295 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 731653570 1250 731652320 731652343
    0x70f0f03020105040308180409150c02010b09010b0d0e0303042f06030f1e09010f180503220b1c1b0f0e010c050703051509030a09060f0306051c03020d0e0102 69
    0x200e5441e400c8900c8640d07500c82c2980311f05548a0f1030140b04c20200030b0400052102c502c00f11008000c1d040140c40203a00302c40b0170b0352030264015020741c0100300094800b001402005c508100200ea181f0310b9012482c610b030401c0d07a046501c3c454150003040110b9100941004000301034031020502030280c0b0203c1e611f4407000d0020909440c080703000401e68400060302101580d41c03407004100d289008214140200302602054103450f040c10319054031455460a444011604000a0341c54070341c1100c80c2e01c4600000701041c071045d6050003400a141c03218070024004c4c9000c22070528812400609241c81254031525450751040500400c4904456020b925007035140740e103061110b07120341e610005a40348942a10002c0403403158032004001c1007070200d4021400120012081d0321501ca8643e420b0301c034000c0b05240e41c00075038811307020066244203e01404405606060000f0801e489401150354072820401c0c030052070404060100402d9810400500518010b29101642d00b0078000000e417a00c1d081c010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 731654676 1106 731653570 731653583
    0x21060f04090309091a12010b01030506090106080a0504030519110d09061d060904060806091006181e0e0d0801240f021e070f0f030201050403 62
    0x79807001603070715807140e0444505220190000705481c80300301d400c0c20b141c0c28014501d5140c424810711041c40000004c0f6003511074900160585001030080c5005d40350384001000a16030001c0d500c0d400007145440480c150f103903070900303c9060040364640440c08041802c1030004170303040118402c075410711200b41d903141a601c200595a0500c144121000f190340c201d54583c0400051004040303410300100440d080c443d0043c0845c00f22030894104845590281080c8020440100400310100c05842d4013804035900340034213010b08030310340440741c4495911100544004464040848003c1c8a00e080c20080c44811601c900d903a1010b108210020510880001c6000003000c058111030620402c03051681108520081b1100c0d01001c03422800c60050030b0120a0003000d4886050224000500400d9400d05142004107500c440303900009105d560309801f080140d070050169400c40e6000704 = true := by decide +kernel

theorem cover : BRFrame.Cov 731474820 731654676 := by
  have h0 := BRFrame.cov_init 731474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 731474820 ≤ n) (h2 : n < 731654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
