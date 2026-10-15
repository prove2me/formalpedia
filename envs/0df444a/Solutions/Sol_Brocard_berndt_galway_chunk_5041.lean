-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5041
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:33:07.477488+00:00
-- url     : https://prove2.me/submissions/c2f65f04-0fdf-419f-ae45-7cddfd7ffc13

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 906474820 ≤ n < 906654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 906476070 1250 906474820 906474841
    0x80f15090a0807020109080708073803091002030f070207292524020702090105040b0d290705072307121a010e090d0e010512040f0c0509 60
    0x4079030701d0340440c50b00d507990b54900c01a96620703041e8102c06881e100b0500301081c40c0b44001104400c1d5801c4d00444e41c41e07040c0a0351800112030107100185c910880c020b40702c555141814018581010400742540c0e54031000d610040e0403a001110b02c41c5d000c4c200072040c0101544c06000e044040d0404c05131103080f005184030800c46c850004000702d035040c030700004c1860380410541114580304030001c2c1e62000300d590a0406038070b1840c42d6800310440e40300803007003011441d40718822100b038154094030740d1400740e10788020040100b0f0304240391a0030400c0c004244000518481807600600c2e1075200c0b210809403840b085000c1507a00903c0d07607061003010852003000c107802e24020a44803030303140c07032005002c50340d0203c442c10251243c0c0144080d0f141c8a61000812a80880d402c2c00c504101c1590101a030781d030810a0407611040c0c1d0382e15419040b181401f01070520a200038902900b040c10b015143c07011540b1a04215401283e044e14442c004265603410000e2050451009000c11100c0707881500b460f04021 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 906477320 1250 906476070 906476083
    0x30607020d0f0e0d050c010f0306050a090902040908040f030b10060e040e1513032705060a03020702060f030603010b0904020a0501030c09030609031e1106070f0c0c080f1509 76
    0x441c20b0000c201c80c00481c0790310400181c084948050140c80c0c0850291030165681e03109590b0030ba000c00c282c0490486450722a10034801180c000034004460782d81303000b00140c0185461102a40c2061300c4003440d0012030302480083c0010200240c14003281403440c140304090102c0070346500f084020720b1008014960b8005400390000800700c0780018401d00e001c00c0c251078801d070800401003485e40f01082012002c3e10900c540503040c000d84560700c0d041c40b405040e403801c1d2050711550081f4414200f003401b0f24103006e40644014606810014940490340e00002e050390003010403034100a07400005c0000030b040c2806441c2941c001075820b02028142a8000b880d611044d0007014101039a0380380d4204200c0c4260170000046402c8001001401c509081c003d140c8008903c801d07081101200c40d603910684580c0d1030101403900100a88441c1d00c410404840b10500d252a11007086400c01c2020b010400742d00700c0d60010031441c002000105d08400913136003071201c801c2c408901024076070100070b1100004030f0074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 906478570 1250 906477320 906477343
    0x1a040312110307080d090c090b03150906010303050f040b0c010b0103180201120c1209080c070503071d061314010e01050a0521010219030903080109020f090f13020705010f0b03060702 80
    0x42c0c03a60711700c41d540d000a00810760060a00e10240c00000760446a560188014040a5050381d2034694840800e500c1d007542075032010038540c084001000801c3c440c101505041034100340c0304c0d2a20740d4400c0d2070002904944901c9529955603103048a0a40e0540b045109070642d509145025606030b40000e40301c44003400240c83c46a488150b40d0200511030681e41c2d01d007034802c00040110616900b044c44140d009159200094803820f0404581c0d0300e00040c2c1402103510300c140d43c0e918600c0106050109880c00f82c0704135005080c0d0601101041c3d158011032016481130b00081007250701d020380c8451190b8040e800f06014800b01501030000340c540780c595251107440c01030032103814244001c1c1d943c0244114a001c00d60960403951000d00385500d0781000c00b9060095075004003690700c9500e040c2c08c80c401ca4200100e00a010482c0c40e4850800304020350b0710312b600405040c8200ba0106405041c1d03030048000b2941c9964403c409102c5020510076140101c00039401024585002c8101960f9a1941c100d0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 906479820 1250 906478570 906478583
    0x2011401150e041808031b040302030a060c0c08040b0d060e0919051e1e01020a1205041a0a0b12010c0c392102030c0f010203041a040312110307 63
    0x10b148241d0384480d0007900c2c9081c1c0108800c4c8000310141070120250f081520a040591030020f5800c40881c40501601c00b5240c00501030010000c0740e1f50b030a002000e10307020304002d2280d4005001e010901c00400303400101001440b003503541c040742f81e14070100c80075500020342c1c403100c060130720190803000142020511061501c51400008605040d883c2180508401e481c8110f0800070782800c0d48007003000052414a080c5990b50f2075041c0f11000d00380d00441c14480e0014285070810b0005010607004250440d0284400c031000d8101110f01270400d51084a00300d144035102c00c0c0349421800d1449515801032104002004940642e100040c41d217542c40034094000003204000c1e010070382c1a00c2403843d02d840300700c0281200900710b0b5590301d485401b9104251260314040700d007907011030303090703802c00070003a40100030f8464400d401040001d07285103085114114401440082291411500c0103100034040301c4c869910303a840c6292190104000311000001c1050126030b1510818001040e950065171125 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 906481070 1250 906479820 906479837
    0x17010b031509061e06063403081006080c0f0702040e032d22090216061802220e06090f0d0c03021207060b2d0a121101020c1f0201140115 60
    0x90a1f5010318101c2c0c07003065207100700c84196060401d00d020288103018840e4440070f10903a43d081c1c1c012030205051207000040b400c032000081c555000c240040a102c4c1500240780d04102080c2c020030200c0765156100ca0080c0d00000361031b65507402a80404500c8004680c046600d44601c0851441c1d41c01024842c0300b0681d4100c1d842044400f01600d0b00000c2c10000034215222a04030f1418409520304e002c09492607498980a07405900b81d12300c482c02038540281c1511603450949003454100304101300e1218055075503540940f8031070410b01c65a170040c05800300602a080312251a103080c10400300000090003c004011400280c002c100340010426580c0303456115403d0b4184a0701504a1941f0980d03c008072490f20005410114030000032840c0750303698000107100c944107204640c0e1840c0515101ca50310640c0000c00200301c0204230100d0b01061040e03400e071024040103c0c0c0b15050302200b107440407141c040e1201810354241300b100a081101c1c2e4115803594907080146040802d111004000c0201c1c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 906482320 1250 906481070 906481087
    0xf040c09091e060b06070b0106090b0f0a140d06081e0102270604030b040b093003040602070b0c0d05060303030610080402040e0d0c0c1e17010b031509061e0606 70
    0xb03030304c040080d540c00b52100b17940b00460300d00a02580c0007401400702040e181d0700c0100b0115160015640d20610207403046281014581c825070b5181c0c1840c50034480c1000420001000741c0050059000501c1d00000805080200881117020f80c0110103550745160310521022082c03000088065212030340d1382c0c03c0c920100c400b510204905d1f1065402c05020b1400000c1488100306807440743d180b240b08203609440891101104200070004042070194031100802c3d01c00c0c0e094a601c00085420900c60f860042c5440c0e215680c1102c031560884080d0640310000c02c0303c0403006102c3c0200d591180c002c44c0030310710b9071801030001600680c10007080303002c110862000408644032644107000c19015001203403052180124001d14000c0700072411140c0142e18400090f21040e04849181802c0e10504400c0c45541008491040280110340542c500c5d9220007041e04a52810301c10107034040c0000385100c900f440c0041144d4034120300907081032060408180044400300e01c10340115045502126000c0c1e480c3c1d0361 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 906483570 1250 906482320 906482333
    0x5091c11100b1c05030c151614040b0a090f0311090112020d06020a0c150c0f0309050d050309070b0301060906080108030304051f020903061005011112032d0f040c09091e 74
    0x140b041c510300c140b04000c00c1c1f000300180031101a1040381114003a05610101c02411500086107015030380120005020610482c00700d40080c1c1300890042c544071681e0341c2d8034861034010504c1c603071040c6c610520304110181542404540c040c090040f0700d1000103a500d07181e000c940310310030305140074084681c00300354050314920455007103846982103803074000300103441c40d00e08000f40400b16204020a41d892420032486000b800303000340f56a00400500080c90f13036000c3c00c0d20198401051881c07140101c031030115001c12400d018502a01d107940e2444050740c11700002801040c0c0682002055920a00402002910004514080d480003d00611220031070403540e4004c1d01903a07113995032500410080000d00780c4103101d108110341c3c0c01d0783c0300c40d5054000169107488000006421500b08010070000d6440249005551480415480d40307000042103038900301c4d4486800d0b0351000519040e070313090000f44522405800e001e0040100304118035a4142e035502e0342260700c854044410b0f248421600300b441503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 906484820 1250 906483570 906483577
    0x10c06020708030f0604061e1214030406050c01110c0a020f010e0409030804060c0315120c09020c0307060b010f050729070c200d0605091c11100b1c0503 67
    0x2e00c2120161241452140351020300000c499460190b4500302c030021b40400a0240b50004e01488841e00d6011414030010f41e14211080c5d0b070135983c1a51010500342d80c4082003005000400c2d180e51110f4031800540c40c81c90030746207100d1a01c00840414030124041807804550b100c2301a904954101e1109481001603a428120300c0c40254002d281200c510141a08122014860342c0300c2e40040043c40c86000007603040369600c6400300b0304914156014400400c09202d071403000c0e4000d1021101082d0368501003020ba0307020592484082d0801b1401c001048ae49004082040c002400c3c1402710403490400200309001d40c0070044c11703019000c4285441600d401984d0f000820742c0c664100601c1ca840e2202800030700c04100202c5010140310780c110320020000c000e07004244002081c01030b420340b02e525000054003015214020a001d007141315501c08800c480c078250401c0144e00d901041980851055003084590144060000d00300f81200000b9501c80381c0c044042d105492200c07140d1b01103410a2442c500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 906486070 1250 906484820 906484823
    0x14072c180c0a1203020105010504140601120e0d03060e060109080c010e06040b030403030b011101020f03040f020f030601060e10030e1c09120308010f0501052a010b1f020606010206040f02010c060207 87
    0x1910300100f10007081d00680705480c1d01a400030f020f01e0b6a07903020b002c101e886400614030b1161004010540641c0310381340d140c01301b402201000c03544d9600d080c50141049903041e104400700f640d031a010001a10004c60050b400b00090816038017461a2801e0380352200405801581046110700c01e829103992140d050318060082082d8203900c0349018a0094010070403005801d0203e40420707100c085805050003221100c02c20b2602075419074445036952855140b8900c401c0703134406103640b504c0029843c05c11045009003855070b2000e000c01c01a0040c02603203407112241c1380825007410701911090500284a40341c003024200032503021403002c041200c2000300360300030400108168020006056000032014165480e1405a0001c0d079070354001950b4510070380401162040b06840e161294001d101c0900000500c071b040082000310380c960002d000313421b429102880305001542da620308903034100005540400c007070000300307610704164031500702c05041e002d0001e0400c00304800c50400c204a540603142c0e442d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 906487320 1250 906486070 906486079
    0xb0303041208030105150715110405040207060606120e060f04020121020306030114010e06040b04150e0a060e071407080f030408090301140c0714030714072c180c 71
    0x1140c070746030441860f4801c0c803078a44100904050100c1101c031601c04c0302d04403a03100c07941039890302034aa1220090546041083d00d0214140000900e64461340001e02d6a1031040380002012400c0c40d40190040c1050101440c00f5864281b1160741e241c07000a505d070308040d00502400241d561880120f035210701c1481400b84100094011131200b40b880e030003841c040c2c4404ca000b4001e5000361100104451024030445c4c051100e4240422201e007042e9115500c0340c903010780085603126990768001a0b0040c180d204102190407901002500d14140c070a0344094001c50850580500f080d0800604511020385841e03a10003001843c00c04000c07229040b51a0000c030700e1002a124505418007a5a50f00f14042039800b0b542414480f1000b60034010016100d58139660f51340b410b009940d1039019200c90b401019220138401040394a022500320a4024004008a402482418100740d00d50047c0f441a070407642505c0b050150100030b1580003254070b54415070580017010306c0303002c0c00c1800d45031490010398030340c20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 906488570 1250 906487320 906487349
    0x20c0102041e060203031006050c01140106020703110a050a0b030711070314011409070b0c0307054e09030c0d0302010e01200702100c0c080a0308090105070c060b030304 74
    0x904003911080c8454801c0d1030242c00141d50742d000300380d80361300c0708407282c814005141e60b060240500500191295040d280000961004200c01e0318031140002c1e041800036900c00300c0200100645200401c0c0800c809a8505621920b01808900710075243c1c0180c90620001000242d001c1d4420b40c00d00041a41090848408550328280070200c180c13542c0398900b0550a100c80070032042460201c0c18040c41c6100700800c1132a141c8800ca001f10341140c07501c40080d010800050f00460000c00460044000c0d0f610b0101d01d03580000e0748000721900131200c410004051112100c0c4c901c14000c20322030401904000c1c2035903080d010f07001a041c4462403001d9980103060103880414560305500c95105900100000c100003103030702e071038403528106c04607540e5042c2a00304070010050620046103044a02a42041c62060000c0c0e82c0d0701075940d43d5504940d6940c2d000032000c500f070640c00b102c50f0350015a018001c112a0070a600d00409010382e19501500072500c4031413040c40d5441c1002141c00400e040e0642040d07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 906489820 1250 906488570 906488579
    0x2030c12010f0312030c0206060f060d020f0406180315050a02090d051e0c030c100e0604090902010806090609040b0411030d030906060501080f190b041803020709020f0f090301020c010204 82
    0x90782e49600040d02c18001030241941014064401c41503007800c20b400609a940e078410030000c4202e80c81c095141c0019042c4039070428041280060580f500000f01c403a80c80b64108400101915044e920f20048400041400c1020884a6080c0944130500340400b0074181d80b1488000c0203880ba4020700c90308102900200424410049a90812440e0710341c5000c0f41d14030070500d115a9000e10703c0e0303100c1c6d064106000710112460102c031600c00101c0c05041c4810034118000006183e40c01a5018484c0951911440011580d0050141c1d50001e01169218242c4c200780d004528010b0000303000900c4148031001103024400c46a003074510384075008048035000c403000b00c0000d000c4d001d0640210b414034100a004615903005020591140d5001e402c0120107030340348000c940c14482e100c6080303100255203508051103900c1703a0060500414407919882c0b8042c0807450000e03e002402e50080035440e00c1400342c420074061050031120244440c08213103072940c640500190081c410950304c410613602c001070014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 906491070 1250 906489820 906489839
    0x601051c05150f030d05070c03020a061206090203010f091d03030106090e010e060d02090411090a020a0f0309080f090a091d120c031b0f0d1e09030b0a02030c1201 71
    0x184200d14501401c5900b001d0381040c0400102a5100d02d82e040c1c2000f40200b055a1050024080c241c4c043d1240f0040b1176607a80115094008907081140040e48418105402d001d00d030241d04002e20b0310120440ca19850040ca600002c91180640403440e40c9a80560158139003c00458200840c90000d0785c1d44c0e569500301c080c1240380302c4d1060511044400000185070300225480a00c554005403d985084855500304610311a004108681520110240405c1c0391075581116114003040100140e94911b05940982030300d010244042c10141803c0707174200015650802e6035040600c091382a030300c0340d1010300098540045a00003d103640e240031603080f42c0c5400042c207505403000520036510721002e08003070300714030388555402c50b40c0b69401040b9440c40c0747c1e40c0c202040c4443c611078098425003281030041c1414049021001c4000409095014001d46445055002a89000d0604c41e800d1031460b5248260b00c20028400300c03207180d02000145400041c88200c4101280c140664142d9685425204 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 906492320 1250 906491070 906491081
    0xa0c0605070f02010e0102090d03140d090f0c150923030604080d061e050607020a1203030c1e0212090319051c05120a0e12133b0601051c 60
    0x1100158240005d82c400c110041c8200d1300140005451200f0050250f141603500e603024220310701c1420070070044415a80d0003441500151442400f40786a90f000300d080050003009145c000035580c01400d08505902c5030000f0801044903040380f070398501c0000c0a4089800700d001036140d6074060042c0c0c0200310401c0020401004200420383c02000050713110404001e81002011880109100c844c0c42480307281791540c0500403843c4018054901c2c030340c5403408400c004110340000c902081d15103607043c50498210411403100581c4541c20b0810a0003c4402503136848041e100740404040000c4102c41138505110303544a403404940104440e6045203046a960388445801a800100c0c2c81e1103030035498803d4045950b034600d24080301c841c644444881e0b20050800c0841c05034144510050b198500d007003507019150684800b106241401d10700b500c0a98041880b090703004803a0140182042d05080c1d0b041d071400032803e107070000921039071041c0050725544a1141e902106040020b0704408009554006 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 906493570 1250 906492320 906492347
    0x1030e1e0a0b1b070f020f1e1311090409060b0a0e090606010806132f0c0606032803140403140c032b140c061b0309070b0a0c060507 58
    0x5160680d80d0808400030f800d0b841012045035140400c00d004c0864502c411404156000826542d106521700700003814000b4445840601d10300794200648061800b40c940000d0500b40e00d1041c0040c2000c004035444038450403543c41d01ca240d0b10305a00040c44185c1d40000c011807009826896825200c5043c008040001c8420804902c11000014525446000120f001b800054050b110461955842ca07001e45580a00d41140d25910006109507002103141d081c0150020b158032550b889400c0b441d0340c1850f000410f4503000354010503441c0c00c40c01c000401c0341c40680b4280340d50f841145051508881c3c1c3c50041003c0460410007050200902149041c142904409007040703c5503110701100303140d1110b040c00040030213407089003c2010362200c612214109401c0a25042510003c2c5480410780b90304003000c90116640600704011061070701d0403803c0d6940c40e4015002e820362034040f02e8241c1d1080d050180900702940030600004071030080c1003001c142903106a0078402854002070060591401099 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 906494820 1250 906493570 906493583
    0x9060e1e0703031125060e0d110d0807050a0506062106041106040909080a320a0c0203100e0d03021c021315030203061905060901030e1e0a 61
    0x1003514909141044051010100405880540e00d5614140c540d9458104240341c240107000102601c0c0072040e100c00c040d010300c0d4084031504c41c01c000e0b00400c030090f81c21845005021620300d40c00400d1620303059019030032045607001207030070242c0f50408441c005c1c940300424910502544008001000c2955440382900782c90a03504401040301140c04181c20140290a54000b40d0100b00413441c008035003c1c407904068407107072420340c0d42c50a020495003110019594044003042d141380b52544985e110a80d0000c04014071540710a4030020071024400f82d58041e14440001070001b20a8081c00c02d089c910758001342583ca1701c00074200c569015218000c2d100c1d006000740c03c40fa00105000344207a4520380340f500c4800001081c0c0300b05200007544655041d402c28458800000307000083d0845940002c90141c0d00541c030790802c03c007400410710310b0031032844441c0c81d141030510181d220042500c062400900c4d01040708071b6480f10b003a04110200b00304402420b00200c080c15400d5000424041e10b500c17810 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 906496070 1250 906494820 906494833
    0x110a0617070c0b0415240f080601050109090507021002210c03070c0b1f06090e09150406090c08030a05180415030b041a13020f090105030d14090409060e 67
    0x40701190850406000148668854008a40400c4071304110610341c1e14040000903002448071010640720500c00c07503034501d4420380c0300140400c80800412000401c4140000d040c1541040c0000c2d020b144940202c105e09a621030008200b5480cc01030a040317014a40d01c1196201c000c04c0314241803444d1903c910001da5428030100311000881004ca0344a2401a0703200b0320700c0c1c0c42e599103503030020070301521504004011404480d516056402c40500502c0c46481c2c007460300d49007841505110200509000c11901701c0d0007502d00d00100c3c007403165800b692029002440400520703101500b5580303504800400c1c8000306a0034080da40050081840314402200030103000b0410040000f5103040d43c00d0316001d604030b43c1040000450f080c40320b5030000c2c0310320b10060b83d4205075403c08030702075401c80e40138007c0480314000384291300340000720754556501660060459810600869a0341091408240030441c51000406460300710000b83d40038540024014810019103040c502c0c040d00e40216140428010750 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 906497320 1250 906496070 906496081
    0x50703030c090b1c0204170a050d080103021503092b0306050d0f0303020a0c080c01091a040b010e06010203071403120112050a060c050c160608070e01020613110a0617 73
    0x1000e6240c00c650807251142e00e443c0c840d44802000f00071071368801100a030244808600315411815141020809a00500024680c0e0509038076198448500e9010311903560300500c0946c59140120510350075100072259a5181c40800c14135001140d00000340c15200c109001d10420114080f020ba840342d29582440b0305a00c40d001c1007603e603107021006000c03506060300c00c80080e000fa0083c001ca0000b9003000e9481807150789032881e955100414072035841e59160100c3d0304001c506641e0607060b0052052112040c0341c1035480c0d924000f010b00849030300702415400104268801c000f00c8058a5002c8407000401c0240056243da070380220351006038010408001103004902142501880c58100004000000c1c0d00d48a200c010716006003102c2c00c010041204a0034200e0410040d080442182c41210001d4540341009015003130240500040148180b817007107043c1c0e4002000d5400041d403694400d04a1118502144a40511a42c0c1c607002108610000382c0180c02203030300e991050007031040600660342d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 906498570 1250 906497320 906497327
    0xf03061003060507051804090809060d020d0f1a12031c020405090603010b10030207020a150c30050913050106020f15040215031806011403010605031902090c09040c050703030c 77
    0x1058800f5450b12810581b400310380c80e054200110541c000d5054a151074025008503802e40d101d0000b442c0565000100104400c1c0e46200c1c0c44c40a1503104002c010a03003c3c00600c049403290000d14a02c00c00c1300c64002e0f0013075201481120340190903503425a075000b4821078a02c000e90098404c0e64452000c2200040d158281070150380440d000003000c121020030380100990007500300380c205903004442d03d070001c034060408001104080b41c90f42c0340c60031f620340240342184031400307000308202c0030303290b602c41d14483c02c420b160900f9000c40b4541000c030745900595020402900122801d80159810300000141554012404049000c910b80c19211401ca49082c0c00a031020705480080d04450b089c2c03850241d228101020b10741000c002d10b040411403840c0010146029800c5e04040158101c0300c103942c49914007480707108010301007a070152401c0007000c0d191080c2c013201c406003e4003440e00540003641c40b0b9008001c607100b64034014000c010048550b81c00520300e402ca0801200403a01d060300c40c02800d0300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 906499820 1250 906498570 906498577
    0x50603070f1107030f0b240f0402091815190810050a180302060709050910050409031b080301330318170904110a0f05090f0306100306050705 62
    0x3900d845041c95011241d034215408a00c501208100340500303140440014144031420040a02903c1c4d000e0140c10280054080407210300250700f1030000000508030251901060794003840421900141c039420014085404a05040403402421030380c002004103010409042e41031a440c195001c081d54448800c13518001400c6024a400f0790b80704550710740346e90a25800065204001c1540400c0c101c001101a04400e041102c0032030143c0c000f0300030000801c0d03000c0c02190007810704981c5000c89040000c1c2c2d80d8600c084501841c1e00694480e203202c018580034803080414850182098051042c290a003000240c1080c01021128040038480c0d00c2c1d03107080b011b80810520044a40050b80300c4071144203400414450004c0c2c01c1c1915101d48100c00f140040c112070700c00c82401c44c2020303500c07903a0404110403100b48034049112280144083e072075060748000b1440841d509400c060b0755511040d4001840d4048030000e50b80e0506c200c01c00c02509d41a22500314045a1080400348100e4032020303800e0380c4a00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 906501070 1250 906499820 906499831
    0x7030c0507110904020d140615031f020d140408031b072406091802150316030e03090603160201050601080c120c1b030a09050307030f021009050301050702010b0109050603 75
    0x480c1858500d8140f400c642042c3c1c0140c4024443c450310116035903403a255685024018080e1f400c04410440d0740c0710304032070000c99440c0440c090304a00c2444094044812200b164190038694003103800788403002c0d540d22191031b0260f000e810616a1400745003d60069208403050704111491070001e1040240301e805440515a104081521580302800f0307450044402e980b040015036124000090b148250340b05484500d00c1964051521101e64010b003c1050304290300365200d250208200304041c008140c00f840f0f28000c62602059421812030300c60302e180500807038154803040000a03ca2921692246030b2181880794000748280d41d603210041d0348450040320104100c5004100d01c000408482484a42c003144d01581141016030000398280a00b002d80e210480d59800052a43d140315005101f1500802d821170060600074159901d49001251443c4000d0080522645030792035140030306414405071102900800292803d0100280038001d00c3c9206400b00d4a00c1001240c0c60401000322445070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 906502320 1250 906501070 906501083
    0xc0607031104030c150e0a0f030201080903070305370f1206060e040c030f0e0c090907080304030206090607060504062301081b01020a080304080d050c07110105130302150307030c0507 80
    0xd41c03405c2540c0114140d10a03180c402c04c015081411519529980380e41d018100f1422203d420905610001d030000f0009880300b0150381c8203006801c006644a4200c850212210301750341241c2c542e81d03054054450035225802c40c2d2104620740e51030030a510180d03a41c003801c0d0a0343c2d0030440e00181142c040480703055000c0c000004413079100c081c3da1418244c011546180c0980707030006490180c0c811060444034408031007001340d08800d1b82d680c0245000310520f50401e44040103420400e280070302056417071186210003070040750003180742c030110758400090f10025500700e0002d004900d803914002000341807000c03045894005e13000059a0100c401030140781a10701482c020548a840c9450034021011724110660451003002d00075000a10404080c5003da80306000064a030815060400f090b6103009102d980d000e0800e02454010441580c0a0601c0d1403080c2003466a5524100050040c841a5080079401205582c1703201c0c00e81c1c0d62240107620880d4030b99001c02107643d03c6a0112500d00c2101405841c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 906503570 1250 906502320 906502343
    0xa0f060b0901051212030c0c0616020d022b0309140d030e01020c0714190b070620220b18030f030406200309100210051b040308030c0904020c060703110403 68
    0x14020003d004681047c14030354041c0c1083e100104c100c1ca418001c0703c07580580da00400c40e800314290100102900e5a0329800584560300c424071511403000c3c2420070510250719080c0748240d065029601000071290401003c854108400c07002c07654607006a50b403000000c0c0342c0040408403240602c06d503980d04000300d0180220781c1c45c0500c0d007002002d901e0403160384280221440e0040c40b80b100c0b8079100801c0c800700307150b41351040d60808804850707402100c419024948509600c04064050031940e03c030540841d03019298031804d9511303407800747c2ca42085030104070001d403010000480030400c103200081201202c1f84449043e00e00c039180e0145108610104400b40340c140b2034a6001c0d508228034040c50403c80b41041861000a07003014a401c6441f00960088110103130312800c140581130b80030950340401d18520729144004007030b500c203620028059020200c0441c1c42507007e541103a014032401070080d0340352600406440d80710031065035076002103454200e1506c1181048025a0100c0c0c0d000170f0003504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 906504820 1250 906503570 906503593
    0x6122e02040602010e2a1e04290603010605030402130603020306090f1e1c020f0d09090b03010507050307030207020321040e07020607232802070803030903030403030e0a0f060b09010512 81
    0x4421f220703802c0c6609020300e0410884292564030403111501c1c0105104003d401b42c80724131400071245080d000c0d0107080b042005010081d048011250090b9050f944425600322180344140289800d4000a40c10302503001840200000050000e1125001c003080e112140b00205990000b120b000c0000d419540001307940303101444042032f0008111101c0e00540d0b038a03440c565016070402d48100b2100c1d0120751341003001d00c1054400d110340c00c00c4160170740c0200010f0400c14005400760000800980c1019000035441c000c6407400e02200280c041c6a042c1085070a40b16900246079130001e0040c134900307800000000750000d10000b0a0760140c01c00ba00c07244803410300c2542c2d0074664940b628100840a0080006a010481103c00c0c0020510310240c43c0003007103130803007000742030032903c3e80454407940c014018461500000700c104d0f50030a915040004210b0580801607081146039400603000c1c03503000401c1018450241c0140d9021842240c01070100e80c4c8410801c8a40c1e4a103001e14401544024410750 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 906506070 1250 906504820 906504829
    0xf0e0304151116080105040c050405070806040b0315090c09100b09090a06180e0106061404090c02150907060810080a060f0b03070b070b06122e02040602010e2a 70
    0x1104008040d241e00f4000340d070800c400c1004580c819115a1b5503141080280500c229041c0c0103481c0c01c990601240c1003c1c0760007400900058461807050751340344900190740e602004070880c1c8810421900d007240c42c0854900d038458030310f154400c2c02400c40400090310f01c3c080b6a200e10541321000c94050402c142742080c410a900020201502c2a9a821001c5002c0140300c440d0840000000000700f02c5034500308069003501c407258000d0003880700c8120032892800c0c240040d1001c0d00c1c84003000003400044500203e240c007032184800c0402070640c0c0c01303002d40b424010440d681601c07403507210302803161526a48038070700c88082c0c481e00b080c07500300143c08800075101e034100ba42d03008022030000c640000d01900090038040280d1003c8002d00f0009410401c00c040180c54581c0040c08039007000100c0c01112000d51a0f441406e9103a125441003110740340c24510000306041c2941c8040d4086440b25250314029000b4440081c0c00a03242c41440070721001e01ca03592a0205041440d10501c1c0044c1003a42d0600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 906507320 1250 906506070 906506087
    0x3060e06060603011703041d0a0e060114010e040b0913060b030303060105070f0201110763050f01032609040b011b030f090609080d050f070c03060f0e030415 69
    0x44000d07006c1080b0008846240015020a101a0000c11400350806041100c111500820311840b19046140104a010200201c0681c264020308003544d1400320200000d0042c0301440d070392035000000b20280b29842102e0071944a15038464901040a12203440405960340001c03a00280041d004205000004180300b445074411841030401002c403080c010724142c10600c19410440d81881e04c809080d42c10b20780c10b00240441140c1c0903d2500b01d0301943d051030307581142e4200726508400c0c0d01550003001210854046d1422007006003c11040c01c0009030315905000031312040d038041180354078101c80000c0c144000300c0040400070840d440c1119550500002d84014140c83d410301141d0b00d040700b00a0782c2d07091002103082c82a903a440c40d00e92841e0014144040580281d420004010b109014515000844070b481ca451030404640760070358100c0040340c501c43c841d001072040c80c299400004000d0107410282c2c40000c0a41d00707100400c08030a4155580c0a00d00c107000b6010340f400c000140c03035406440341d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 906508570 1250 906507320 906507359
    0x5041205070c030f1a04060203100e063d0c030e0102190b0a06090f050720030a140c0d0903230307020d11090f0403090f06050d0c02070f08030403060e0606060301 71
    0x40d0f10100030708000081e03a081e400c1b01c080e105150000208a952080c0079100c07005000340b032240c13800310708180000c00c4018000d003144008820a5000103040d134040003c00070006c3c0c2d032009814861903e4a5401000582101d5040307003ca150b030180c62800d9030020a400c0c84002c1c800c81408134000300d80e2203c00c4d45100184c544103180e550740d400844c061545001c0c03203450704134052010410741004600200f40e0241c0001d00e804100d00055090354a00004c02243c0c0301c0e8403640381a00c3c104940e4101143c8501c25031460041c45c0c400c6081c0c0840e050f4100c003d500869004201c54000303002c0040f0149036000401164410a400c2084600014a003010034550524065590404c1c03210356400403402c0d442040c0c1350b10280031043d2007044101940400b1840184c55070032481502c40c2e240c404060311901400b8103031506644c442504080492082100b00c008090307805101510326130b6060034030703200d41c090b00040e20f000c3e00700703007512007103a0300040c0ea54014000544242e00c2c6030f2038940110000d5070300000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 906509820 1250 906508570 906508583
    0x10030f0b0d0b19020a050714010612060c110610050d05030d0e10051501200c0a06030209210604031b0c09020901021c08220b0a05041205070c030f 64
    0x4190503545401d01158803a51003071124112a080010414a600f40b070007200f00e440c140104103403101c01d640542a0350500c0d034040b66210190381c54400f2903000d00180d4009840e2940c160307800f00140842034205c0041c1072803079269074080110134148543c8820003141e40904c0d6000c180010412800d050f0320007046c0500a40560341410000e2201500b03640d0345100501040e80a1101c120201a45125050f04501e900d9038130f220400c20b140004c0c10280d080083d40c0b01d18509518080b011003018044102038410080001031000c1e142c2c403010380207410401901e0300a111b1621001d014950101d6420000c142c0c12004240742d540c1c0703640c1140e0148080410030600204020f503280014510b10225020b00241c05001da100c1038201c000910384102c0322440d0450755a0310300703a20039098200700015044a45d521101003c040201c000305070b01943c644004102e13030031101c10820100303007030b40c0464040c80c4200411050403544110485070381c00307084000f03456103a9441c0100005005031105410f034906c640d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 906511070 1250 906509820 906509831
    0xb09070e0f270106050c1c121107140f0c0604080303011401020f0d02010f0b040b090a0c0e030703050d020607020d12090f06051515040b04121110022a10030f 69
    0xc50b60049030080c2c0c40000410408188024414020704c05c05a45101041d000d440d8411401002844910b010350701c4650701781d07112481d06002d010300045400031030b0400561298400c1c80000203584111800d007402039030250f0040780c0000c0c80c1400480381200c00e014000c6041d642400000341d0350b408500d00c03840c1584200325084074242000d0140a4520759190000191082040140c20580b100b1301b10043c420380c40c00c440f0506603568003d0702c1d40c22850200c3c00080c01d000f0000255079450803183e007607a151256110000070401d0005c0e080c9000c1c83c203a0f00b502c00079110341c10300307a030f854281c1d00040010074003078484a10107041d81e9008030381017070103080040a140c0c116260241151000e5540c151040311004c003001c228282011076900b80944400c0c102d1410780740c140c11075085d0159004110740c002441801505001581c01c0c60206514000c3c0100c24650040d10007942d905a810f40c805c4c1d1101101d84040301840c90740d40035420000c4050800003207542a050200c005255084800c3d6142d6a82c0307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 906512320 1250 906511070 906511129
    0x819080a0306030b040302010e0607052104030917060a140402030601060f02071d2a0405040f0b041d0115030c0b0d0609020c030d0b060a17040507180b09070e0f 70
    0x11a004d800341e03001303400004494144080c00c0c0c0c10048003c040405111042000c3c0c107203070310344500008050b00f01c003040e108262180e280132101510b00c3d5001c080175441c0c40d0185100848c0c0411744034007400d071030641042082c41c0512807a4149100311030195244c3c110200400850307001c3c10f46041491480d2060b603217081e0700e4000d582e03031044112031201d80da8280c0d201040040c44003038240e0368100c026410304d503462134050410070480348034a00485024030f441c2c4c180c217031a4809507081804c500b03034001d10522006040b802030550076680e402d5400a258201201c0036851000d115003981502c0c1c10150350304001e4204160b07007229a000c0041070211541d2280b0000342c643c2144054a140b1441d10051a03507040145103941c19611495030b564442e85041001d03251450300700006050140b042410022980d40d1410094102020742d484521181c140468880003614158024107000004072459005a01d80301d0b000c84981c40002c045540291102c417007103020345440f13051540001c50380c4400700c0080100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 906513570 1250 906512320 906512333
    0x609010501171506160201080907150e15040308031e01150c0503190e0f031204091e1806141603020c0313030c0905010605130b090112020a090f0819080a030603 70
    0x346051040718404424017400c5680c0306d60110740000030a8020020b040c14600951510300107901038405114100c0c103420440c0d2076000c400440005440c0341242c5499683c20460880e0b0b0044600340003240c40c03041285848110341031720506999000340c054881004180040d20300f52011041652a0f1000f441406c44500e189201007070111b0ba140d50f2540071204507801d0007208100203501e02d00c00d07000400340b0102c080c00c14041e68122010214040b55803044d0003030201040310840c0c04103006608100840031170443e60115108110700c19801000040307400c000110f201c4401b65581900c0c09407130560410005d1003a0003412800d81d5603020303039143c9001450351200481e910b49c42110400202002000105154030840c2d004104c9420028540195011480700c0001d05004a8001420110f51206164854119181c11140c2141d0440d6a503001d00c60103800c040c01c0d032055000850b8003030002305203400081006c442d80200e26400754402169940d82d01030340d03040403102404245c1d4428000001c1285d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 906514820 1250 906513570 906513577
    0xc0504030f050a06060b09010e190b030109150b0a2f03070303051605090d0807032a02030d020f100e01021201031a06030a080d0c021606050c060609010501171506 71
    0x1c100020500703d0a01d141038000c4c0d641d180d05c202c00665040c000c6903a140d0700040400c0402ea0104e480403d00240f0f107040803481d0303005400c021a406008000850045401d52080d810341c2d682d000302941607030381c40440b0360480c42198403036000103d50224521890500c1c07291900c5c40801b804a4008001200008520719080850182c00180d15003050052001118071180700c900d40c289449442e2802000c085030f50481100380080c5460400243c507000c0c144221005018840307181c806001c40b0468004005e41000244002d038420300402c402090304a00001c0c1902400d980700020305882c0100084400082100380d211080c0b65400b0000d030845240d0503c18580a580f08a1035001544100e042004100c900209181c3c042c0d03005a40030700104c5c0b85101682e108a48043c0c0100d0b503202c0d1100220f0a10b10624060340709090a14408070b2031a400c40054090740003001c04548a82e0383d0340c410881400c200384600740c00304090499809002184041030340c3e01a050740c100518110b11034002c82c1140c1e1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 906516070 1250 906514820 906514823
    0x218130519110d08040e040f0203030310080d030c121a030f0d1209020607023c01030e01060e04080a050418050a060b030f0a0c030603050304030b070905030d020a03030c0504030f 78
    0x40032501c800030441141400d0b5002c0c442501c20954003551940c81d19210b10581c05100e00758600c3e1000107003005040c070300000c0f00c03d501600340d0b92281440052026204001c2c000d507080341c016410340900d018400d00c1511000c5c000360f03443c01c001c070059140039002810f01810601c41d6005009000040740c6003000b0301d41c03130b2007403101c02048811149000103018410400318201d0a03410401808c0c003507902c140c203075150f540d0111019101c07400c519215540c2c400708a2000455420072003003005444089540000c6504000c2c0c07000d01401e90070854050880d0401d015244005441c0d8010074007142a80703000d0114480e560a00314507054a454a403d200c42c991010b41d07410b55100d1042001c1d1580b9801351100501880f854a8194100301000828010b00104445907080d44c8141c080c8405109810a000a6030008144c1e80d503580c80341403003a5a100b003152000c01107401c4180000f07072400d00246032071540100e0742c06083c604809030f408802601c5a0203920003040818040030000c00d100b9030310f0b907d509 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 906517320 1250 906516070 906516103
    0x9060303092e05070c05131b0c060c020708070b0307141305130c0507020108041104061403010b0102071a2d120a0513020906031005090609060c040302181305 69
    0x7194110210328689001c812030404100c3d00703000c20360025071800384400580341d048a0b43c455006061303d4900061105034080c0e003000041030070910300b0981043c074201c40980900001d0201a84509080c2d940b441c039071140b0130895118120411001c10080c0c003544d080303115403030840b10760361812132103170016084080340400741300f41c00a080166141101d1a481100380e142002d100b000940355016147d4042c2800c040d040c40101f07400101004111418560128001441000203584880a4072031200b20150800d01035840c1c801400c81ca9030001911600712215180f0b1015200b400f2009401d01c0d420080c10400d0047c8056480149550b904031450344500384080002e8031444481e101c9103032000c0140c0080810b901d0241070041000d84c2c2200340a0780c0c0e1f0165030101c1d450300c43c040030074900200c0003601042d41f403410080c402d12480100e411800b50701d408044440e16110358000910610072803100035400300501d26217006483c40100503650041001048210b02080c0b81c90701c50030400b42c0c6400030340300d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 906518570 1250 906517320 906517369
    0x403030801061704200a09050a0b0109090b030309060f1201121b0e01090b03070305120304050601090513021e090c040f08010e03070803270c0a06030c0804020906030309 74
    0x110707880a42404010607006043d038250410b500c502d145144102c1e1a03100c890403844040c09603481d45000800100030411f001c10580c0b5004900d02c0c024080142a02d000404409000440521074003510144c808000c3c007440c641605402000301560096020185c6010700b441114015140c2006040c002e00201c07002500507800d070b16200b05021300d00b903901091400e103808248003040020500c0c80c107444400000140200031500041e1501509034402443c2e8840c2a11034100300d801304002c0c40c0901e11482c1122080d90f220300039041914011039020800c0c4000b4484080545003000714112441403040084036440303d040040b40c0781440c125540c6404207070010307040200d40e4140d5400c90042003420001c001800740103580315128030030b000010b00400c10110104642c00c50740301d4900c1122080c40258a09182503070589501c0d04980d0090074030820f41c41800159050107400350901d0440c0302d9444c00e0150b40d5030b500304190300c20090a442d4051006103c41d80300c035180e14004004e6080545000f500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 906519820 1250 906518570 906518579
    0x613120215070804051017010611070b0f07020a0e1501030f020f0307020f1006050310090629040c030506311a0a08030903070e060f1005071104060b09041d030403030801 74
    0xe0103041b2684e00380030012940030308502c03461301d20400c5040d201c291a010041400440345d541c9456600c1d04104105480020a1000340790040001d1025500c2600e03c44410765540084c901c80703030307800c5074444902109443d513038203030350b00c43e9108024140301510014202038211940c118560012610000547c0c800210030551640400000c034401d821450240800341c1402d000c0f985440b50115000c41072174907801c89000f0007030341340c10080c005010700b940c1e642c0c200c141158002c0811503180a0501962908010406e0240700c3d001d0240b2414026104c62581401400300d030101c030008020300c0f900ca18060403445a902024002c81c0895001d1113650314485441e1401c01418070442e6100c2103407907104000d40e08450b200442c01e00101c510380c00d0320300141d030b0710600462043d009901d00c02e0b911254945244043c0c0d6041000b4040450040109603101d044510500c41115040d018000b0041d400744a4495103240c160400366402d01280b48480c102030500002c2407650b001a00101c0100701c14100521 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 906521070 1250 906519820 906519829
    0xb070c0b01170c01030e0f120a030501060327020f0a0f0e0121082107031406190b1e04030609050607021f0506030a050708030414061312021507080405 66
    0x6000d8121424500e40001802c0c01d9903680382c40c180c0445040c182c80350301c0040403c0050000c1c0e0b1007854054207498400e038024022040a90006144201203442c0c2030011031028428030890301c0c103a18400c00a81c1d511000c3c00c0b91010208600b004036409115185905107075154400b11030001c003003840620b1103042c1480c10b8000340c400143c2101c1c0004600d25007183c01000304003c2d501101d40c00c001c8082d0b6074900c00e4809844981c20206411074140e0143c217000329558194030000c400c52030540301406c51b80b0f600b4104402d0b91240e0b09025480c4a0924080c890701c4c1e5000000c100c01e059807210b800400d2801400c0301c0e0b01c0e17002a4800c0e0341255503545a03000340601072044991180706440507050200348101c1032145ca07001f00150110361a034800c0013402503102082000a1103030050119103420b6910000695aa40180681d0742d00c4150404c028200d4100340017564241006000075060b030a0030b15450030b0b10034a4135a0241da0190507407060007500b80c0024010018170b0700070b0001c00d039030303604020511 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 906522320 1250 906521070 906521093
    0x6080d02150603120304080d060b07030305181515090118060602070e0a0c2a050d0c0c031716060f150e13080f0406090312090e01060f0201090b070c 65
    0x5050348031184042245a65003c2440000108001c8090345c9030388807420502d21500504481203c00e500c1c1007808980d1350b10f58030241100714441d503410b228585e5071401c02b140c1001d920b8807440c4281d10000400c0e188144004082c1d501007100c041c0400c80c04020000149516401c2c0d00c61100441e207850040c0306038600e80520006008540010001e8a180480c40c01c10840c00800003038900d40d4550401c05002d10a41c85e2044142d40c0c00600d043d0025035180f105042c1c085c4903011900351007010701c1c00d013400d406150060095500801d0918849240d602c454140e00010f52503555405c504001c4940402280c242145000c0d004180c000b0362202c08107529000c0791514001c50f0740c02e200440c0c0400499124840d46640b1101c80448110f445007079141910441c00b90502c0d46040d4034010602286c10b0750300c03c040300202c9000e8100c0064030359280301c099881c04031074002c6a1340401050014483c141c020151840802254400003542c00c032203480d400410001030307464600245842d915103082c40b00301d2044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 906523570 1250 906522320 906522343
    0x80601020f2b1b06020d1112060306060307050105180d0804030528020f01030207051609091115070b18060a2408061915090902100c0507030f020d0606080d02 69
    0x48010b1441c03481c0d000892614803800812045e00000c105080d5612508080400442d0140700c68a8102002c07082039403402c00c0b2101402131240070001071042c030340001c12a003240d206840d07140c6041c040b4000640d080c0f007048522504101d1003070719440020004402000150300806c0500a400c000c030030040b48404c2841c000d27240b105c818580c9000075954000b000d900303200c42400d006030b03034240a150480c10700800720b2140300038108206001400c010150001d0160714828003280102e08006010020000041464803100c03010a101510001d0303044030040f80c01508824900b0401181400c0380d0b0b10380b020854011130602d880721000c107071881c0c0c0098060b0007020399020f400f032550b05108110b5610000248405400340701914003c1c01c000d4203a000f2141068505e0483c0445600c60340300e94007508500307600324000c2a001300d05800e00c5214040d065112540b083c041c16800e032554450b03000c944181141645e01031025203d204c0050140e10503000101f92040c0900380b50f081c0c020010b030a05280105 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 906524820 1250 906523570 906523577
    0x70317010b0a1116030303060609060302030c070219030503030a021905190503150402121b030907050f0f0306101415030c2203051f020c0607080601020f2b 68
    0x61005003905000d4a08803034180c0307841d02d441c01030f40e8581c525041e102e1a500030b14802e2080003105156150f008070069456586500345165940c15045040b07100031100c00c041640c051180200514040d1100000740c920480080c0c4516103a48580d402d540c400d942003003e85030300051250040605000c075000f07840d254149542080c10707020344140f5242c403050018040050000000b0f44901505500c4295450003900840d200e8000c603894407940c410980e007035483c0d120300301001c49403481e0400850b80f01702c543c14082c1c42d00d6460141441005084e145825034840c140c80c0c403580858070b04010161083c460002c1c40c0101c20318040b00307030b0300c9001c2c0050329074040c0200b03959030300e0100c0d1804103c6e074214121a8a050b501d40c903901250701d404003120036450440c0c440e51000000c2c0080051710100024003045000d20400c2500c22800032807081c100e005003207421240c0000c2d0a14040c5442e503a2021060050b0340150726524015401d001b441403c1c2684940e40204e20341c01400d60303c806041501080c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 906526070 1250 906524820 906524867
    0x9130605060d08092e021e120d020307020106030f0f0b070201020307020d0e06040b030c040603050105031f0c2003180f0d1b0e07030c120506090109180203030f0703 72
    0x458502440c800c03d9915030060705c072010894021542c00a400007200d0040f0f0307540c0118040110300a403113070189440040fa40301d101344107808035030000c5000024111050f124a00e440c10300700c60440a90070061240c0305556842000101050007000b4280c4410320940d5a0596505c035882c0540082801502a10031607206204010506400107a11005032181d0304203103200c44101d800151081c41550000080c0310300101c140038801c05d0060142c0b0030307907086440c1801a680c940c018580c0e2a2408103820541c2d00f605036070244030f013649500c07145c8800705a18016010310b0011042514541c0442c1900300c40d54400200b8081010700240c5040824004039103805000d01d01200088074030940320b1000e0031203014201506862820107140000401c40c03001012940d14200d44081e005204c5101c0c0781021a04242e640c2d0b1030a820ba2041c24801d83c0d00070a07010f061713400c1240c0300f4001d090034a45030100e04d1a070a0b4050140c1d5080001d00180104445076554a08143c42c005100c117040300700f0080e4040c3e964 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 906527320 1250 906526070 906526073
    0x2010f05010e06060f0d0c030e0d111509010b0a0b0d0c050405150a26060a05030a030f14122406070f060903052110080c0d0f02030c09130605060d 64
    0xb01100e4200004955030b0742c07a4600e4949640d81485120640076a46190170381505040c1c0d010b80040d07181c6541001a60342180300b12200313984060080000c208a908640307101c03d4a8010b100392a600041d40100020f642820f20000c9030408003a500304104c49040232400760307824419030180c1811a105498640e08080c5030501003994000c00310b120800c10100031030790050980c402c00c00014500d0880c040d445409042e03004401c2c0c00c500950b02540034124007000815541030008800c001194140d961442c1c090f00300d282100d004040860780401d4210030803269002050b40c102160240d40d44010090401d43d103c00009414100140003034069101071160746c0110f1800e50600412640000300461540c0341840c04498610881c41450305481080c5000141c00e01c8861b0918414001d9101c4035aa590311440c041da918002c1403c01540151000d49100014148001d1442c200344090225031080c6080c0340000d100d203004850b41408601082e210310140103441c021190005002c0c0d4203a010907005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 906528570 1250 906527320 906527339
    0x90b0105040803070f020616060f0522121103071410180f1721060108161404080f0307050d0f0806040203060d02030d0215060a2412180302010f0501 65
    0x6854000e000c5c214403a0818003551215400c0310010103250006c40c0d0302441c1881c003000106a61a8048581490100080c680214a110081014186862006690046035101c800d0850702c900043c0030008107880c441c00f403c0080001d0071016203d441a550880104a03a5900d4040711070015540c071420100c001c405007a843c5c02690a03a500710a0060032440c00d0b060102140d0f4000070541c044900000b070300081c3c00802e440301e02c910294140052002d441d024011210180e003a2460a160620b10000004480c082c5002c21410310010340054180f960b9061040e040140c14400580300d90400240401000003d001a5950400c2030800c803403141c85148006002da2801800e1600071540000418040d40d2080c42e0b8000f410760040490740001c104035002520303030560944440c0c3c8600558003045480c50003010110682d113a00070090b22903018900110003441110842c1d80500091040001c8449440c0c05a00c20030311040b040d4000c0c0680c5868000d084504840d050441d41e45801c0061000600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 906529820 1250 906528570 906528577
    0x6030403080a0b0d0317061e060913020403030306030c09020304050705100309050609030d0e060402090f04030c0507120b0c0c0c10181814070e0d2109090b0105040803 73
    0x815107403a054a9449800c90002010103d9006900c0841c2401540c1050752190061284501d02164030049440304010700851040008040c0260340444c240a4110f0910f14060f250402c001850340c030443c0c074071186610403680190816800680c46250620a10107c2074032003004000c84441140b640c07509454164075003016000d41480f0380d44884c50500305a01c81e800c8910100d42001c1500d0f0f41d81040059180d496101d00c0a15a8107803e000151490b1030011031304e184150340150900c01c2c0740c1d4441c0601c01425400820403414001100120808038404020602c081c2c884d00c9207425185d152418011407a0400606581c07400d0020408003558010105425a220303506071030514504c51018410f8520b01d00020642c5aa034814403000a18078005801000d080c55011b1410415141d0380070704450300400464090001c580d110a20410f24140b2a071440602c6004003501c3e00086030011281210a042c010b42800060000405010240441c450405911000d09009190902c0c01c100c0589900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 906531070 1250 906529820 906529823
    0x210c0405061f140405061908010b0c03030f060a0e01122d02240f07021f02060f06040f0903020115060318021203040f0803040819030801150e1e011b02060304 69
    0x191a00e10f4042c103201041c0d0f005050f004094545034803204408042020300300c010000040c0081c80001030b0b0400d66000c84140c240c80902941c0340d9a20000003840c0d0600107030049800413118200000c40c48500d901080c0a441c00c403419400b50042c50801e1201a0403086420180d0300c00e414a4010b0483d04d491421645035040c0c481a01200414002e007401107040961100101000038100031401c1c100c070000e000f2240700301c45a640102c205086505ca0781c09118945026901041c08075882c400c0351641203030322400c010800b081d1170408180394015182c0340b810440c0135030b44480801d142940c1015015000e41024582003100000c0350464008401e10010013034003035001042043c48040c0240100c07405400002c0e9016a61595520300c140c6d01c0e88980301d107200d9405401944c070000c2210150042100d60140c0c0d07801c180c0c0e4240044994107410001180040c8a045d0000c82400e45503c081d5030181c00002c2115046012030000141121034019032400c1b4408144039460300580e00c031002d40703811a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 906532320 1250 906531070 906531077
    0x8011e050619020f010c020705190b040506070501090606121109070f120b120606210d0302160b040c080c0d050d2006090d110c010914210c0405061f 65
    0x103505070426420703c40001036113010342d400d0004120344280c0016a40081312400c0c2c07844a074101c04500c070105101c50f54007412030207400c01c000412007454590040d225450165000080c0c11485e03a48010840c1c5e016842016100c2c00c80c80003400303102041807500e1040c10b0030385502c0400d00c1d103143d0060403e816006140240005945440315444c200e51022041e01e602404c03001105503404482a91080212078582c0304041e20b041c0c81e0070113201800c0f9602d1284100c4018081c2e001030205c182c001c0d42080c582da00714030769031500307140115034a0240309008a010b443d0314401282049403d5051202c2e4907000c2e40100c9406c90040e0009400088010a00c5150b207070000303103841019001c03150076884c00a0310009105440030311940e0a40814103d0741c0e200c40341c9480c0c195004003450f5a468440300100a800320381519402c000c1107038034170125180d0743c81c000c203500d040720703440f030007540d00303000511f80d0313041164000c00c1c2440950a0901c00c207504a10211140c2c05001d1116240590351032001d070844040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 906533570 1250 906532320 906532357
    0x50a170d050d0b0409060f05090a0b0103020907030e030315100903020102120d15060e010f11030d0509030d180203060a09020607080f07150b040522140f0d08011e0506 73
    0x42c141c107a000c40e605400041092001803298200640a441d40700c80e0350703110303034508404202494030004486040039403000040003203030702e1902081520317100100744034103040c1c5902003649401030500c02035206d0f0b040c40d100e0624800e402002c2c05a100708008044090200d40301007407016030f0300050021022961142500e50b01c5503c0000c0030050b08015122048040c07030804007044007600705254006541c0207aa440040712840001200c80d050044202c40094204100e0783d81111f01d5074008551110050049034500001c109030442211401441c58200c4910381070298114601400301c0d0350041d420103014460201c05030005481b40c4100b0000401102c000210300200880e0726054a01d100d80001c0340d0241044a500480b003e0204079000500c01c624101c00114280b9403a802c0c10f000840812400070351031400c1da41c2c2c202c51007050a41186621070520060070400c0c082000015280c000e5480102d203514100e400c46007802c1d411407100c102d9103582d500b40000c0d100c000584800011801c2031541 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 906534820 1250 906533570 906533587
    0x9030c07091d01111e0403020105070f06240302030f0312280f0f051b0a0c0c05060c070618050f1302070f060c1205061e0a0f060801050a170d05 63
    0x1500b0807103491a04607942403112091044900c0c00140444000400c07000f2141038110380104058402e90000a020400521205000c241c1011000100138841c00002a0313280d85a100103075603100c60001c4c114030b011301403010310840c10140904103e40c40400010350804446480c41100003070024440c0f43c014401e400c445050720101040140d00038100002003010703204d8000102c1c041c1c80c08100190f903603070178500405ea08503181c1042e030004070740c0d03c40414100415008100d81c04c0c6610401131b80d111001c240d0214069031094010616100010300620780d0510709400606140d2f1403030b070103400040c00e0401c10415910341580c0c141d03004200b2113100c090504008040002801411009042c258110740404100003d03503100c1e080341c841944403524041011900b02c0255041103d083c4d40003070505030904d03201409900d6400c1e001030020240b05045071500ca601c00000301c1a480703a0000380c271030401080729045c8059a50042c054121002c03d10b500c1c10080a036580e42c103821a0303410003100144489 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 906536070 1250 906534820 906534851
    0x61424070302150c030703060b1305040506060d020c0102030403020106061103090d03110a06090c15140304301d0108150406050607060e0c01030204080706050a0e040212070809030c0709 81
    0x941c0a1112441c09141020a00100c451700100d07400303404603203480e0b03003c80c40ca402c210a44001110208100503041d04140621000c0c1002500c502e801901c144a14440e1007045d00250440300d0014000607101d107000d080003800c3d21030f035503c004140f0200248680c41c444000c0b0444d024044162894050b413210b500e811142c040350b000007901603010340707411941000050307001140751500400303010601c0c84c0c440d0b421403010b43d045944103001c02c415955240b1140040d45c05160300c03a00031080d86a5062215450512400340342542c424690522110b05a220750814401c82690f0300744c40e1400d0402480c02d0000c0c00180000c0c0080d512155200d02c0020a51740341c1e00180040c05029084544580491400c2000380013407120303200d101d0082c2c0100390741551107403003518100d400d0343c4010065589400d20903942c07940071001e00003c12003000f840861a480700d00042a040c0d0528154120380e02e480000240504006400e01050b40c00402c44956100030001d10142a0f640f50380b80040d40807100700000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 906537320 1250 906536070 906536083
    0x11a03011208070f0b0f010603020301060f0c0c03020324010b09181017010e15060d0209070c0b0421080f071d040905070e09121804090b0406061424070302 68
    0x10404c207840080c1e0f02c10480c50090700d90040c8015500c0800a0741c0307a460079410f03070000b401004002003892050550451103640070b1203502d8050003c10706166280c0c1c01107814031045c034995000e100d052220030882c1545c0000031a00501c88610910b0800383c18000054240600724003546c00d401c00e46d070104a11510800d8075000070141e0020311900c000f0342d01d1001c0d004e0305030841c00b81031600400d20905c04038144003059900c104401005100c1d000308030790070010304210290820080002d0700c2440750000b03400c040c0c00e0b030043c1d00901c40500e02015002c0040400c0c050f0a04840030000204240101ea0407100032050700032540381010b1b03440314079000e884042c903c4015211580541004000028440003241701c9050f0b03a03034065030380059a0754240681e6910300240540c41962800c10001c0000f0380c07002480940f5260042000c100002d20b901c4840c15050305860a54503140c1d1004100803404101c0000c410700c01c01610001c030b1010001d03025a00b130702664010f15030007100024003c41014401e2081c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 906538570 1250 906537320 906537323
    0xe0309061c29180109021e04080a14010213050f010e1302070618080a030c200c040b010e0a05060325030501050f120607031d0106031109011a0301120807 67
    0x300005610314000c0c0454030720303496803a40c41c0c5480c02c542024070b080c01c0c140700c0d0380c0440e050030100b202d91a00321910000d6000d050511104001180c2c0031000c050f16034020001040c03524010102c1c0502810440045960301e201c03e021603104100146601184060311004c41c0c4085980035800c0c00000010784101d100300802c0340e84100c0107941c40100403095030140c450705000303042c20480702c214005c08000005100030003510000f0b040c00461301413807281d003000400d00c909103003551781c10750021148503d0009900b01303d00c40d41c00c04c2d000c0c805242400e1150307002402c004d103844000c100480010500804583c0500ea0055000100003580da40c1580b66940c01c98900c64034131303000a076403188010020a001e01505124189140900486207404003c1d001e6080342200a0500c0307880e0000250300030032030341c1390064000342070220340c036010031080c4a0340d001540a241c03030490242180e800c00407007190507001041c010b40c4521140000c48e0f0b920040e02d0640717088505403460420366041045c11030046140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 906539820 1250 906538570 906538627
    0x70b03012411010906090c0602060c070f0f0b0703020c0d18090f1d06010603060501051809101505130503010c0c1211060115170f07050912070618090e030906 69
    0x4503c3c00c000e40d691048102c42e01030741c1d5901c08161150810ad1301c68105a03140d1180383d0040c85084081f42c1c40755103046002d842146103080c42c0c0a079903900d402d401c1c805c5451802280d408100e5803040b19050121501c55400c3e0300e00903501301010200c0d111580001d0151340c12003644d17021030718285141a48840c2108080070303100c038a03031a070b41c40d0600d980f00824020031002a040c4100010309501031400d4558078248080340891411001e4180400d07620001c245600701c00107950009482117491520782d62111141c0d0718036542d80403000710101c1c080c07a0355000320300070380c5421906075501c2e03031050543d05066801811801030034581030085581c61414800d02940780990740000540700000c891109940405448464550010040c1403e01410841d6a20881c4280320000383ca070034428401030010100007444011985000c0034201d00d042c090703400c00030104400c0802c40d15918241e149440041c40240e9084c401041c2d00910249c0382d02500101c203000d600003003104034038010090100c40d00c603581c4e0760 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 906541070 1250 906539820 906539831
    0x40c02030d022a01020403201804050c1908010c1b2a0801050f0f0f0606030714070b0f06030f1b040e100506010315050a05100e0d03050a02070b0301241101 68
    0x3c0c4468000c5d40700e4402180d280c101922101c510020700300b04410400350007070880c0416181003518400202d40200226850300601044401e03c0e03071400518200780c103410014000d2981407281007400c403000c110044080c00782c0c5c2220381c20340c2411828000003099100700c2e900d030030740810011400c4d05100c90100d0380340c5c2484004041040101540801d101d030302c0009003180b1940307031947c3c600180e800548521001041640004a142c10050b000759040308003894940c0110707038a42008009071300b240100f1500c0007a0f010a00c00c8445030b0312895500118120050950640d20004e55960345c603944c1c104c065070303800b8a0f07000501617039542d001440c00c0c1c2c1d4a4003030b80c02805106100000801e8101ca00c517001c41e05e800800120603060311b01800680b84c002e030400b01400d04000400418403c000300d0001048070b030120309072540d05d07400d80e4800540c0c4a51034898035030001c1400641040782581011299920a00040029114058030031101c03203804003403001c200903000411102c41804610f80b119540c20803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 906542320 1250 906541070 906541147
    0x41a0f040908160b01090b130902010912052a0307060c03210b0301060b0405100c060605060a0804110315040f210f020c06030601080402131e020304020f040c02030d02 73
    0x40b1207540213440b44810782800d03030320745901c001201c0c11104215003007206910321030942040b0b44c1c082d01e003250050400c188102c0c1d959010010711600740c80200e402e03400034424824460803110080400f126243c0e2010941c18140021070350301c0034184030b0070081054001403a4240f5004641e00b000c070641101b1407880811440d0400340c003038558441c15034060340c64030a000030314004980c00d6a080ea400104841480e029a1100721490241010b0a4511701e0b2f039582c001071259107074001002d03600b50644488050f032800f0305040c00c0d01d04441100d54000c0e002001800c5045400f840c1990b030241c0d1042e120400c012080c14142c503524200c0c034494aa00c0400000604010341040c0703460b20510499017141c11018040040c0071690000380d604601264000010400502c0c19070120048203031403090000d032101440c8003c09480c803150742d60700c1c6180d130b00205200a50800c04032103a400e0f14191010710500c1c041c28002940c074825181c0310300149901103540a04072080400004403104403100321400300501c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 906543570 1250 906542320 906542347
    0x6300303040f1a040503030a11130e0f0705090f12010e162d0909080705060c030708090c0d0b0c12041103061006050d0c031415040605041a0f040908 65
    0x40300080d1160440a83c40040c1400e00c251150300c110750240c05142161690040000500080c070005403d5540134807000d40150f4460a00b0b0340241440302d45480075003482242240c032980042c02450400c1020050010305490350940041c8009040d00c1144d1414450805140109081c5a03100d010740503100c00ea102044440c0c140b07005592000d501c08400e8104010780c01c01c4081900850b0000443c200d20410440c0e01c25400810f1050180810518001c4141e65050611f00704070380e511411074001c014010340a6104c1e840c40d41c00703218880140407001100c00001e012440e0018000e115000c0140000d011440140c1552072a490300f207140207450400d0300e8400f4031011442c201501a10841c0d00040f418000c10500c8011621a904c980d0325040b200280075010b00404000c8a041c1030319006800c03040c4108820f01441010406107504000f903d0300200000c2e00c5003a48401d1040d8106007000d1400308549d10031030710f8075104941000008940c000490042d05226201505410000c24441901d080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 906544820 1250 906543570 906543593
    0x1c02190e1303020613051e15040515071409220c080411010503070c11031501090c02103b07030b160906090b03100807060f020f01050630030304 63
    0x40b075002e44d40ca5a5481420301c04280d1340304000b40c255406400501c9007101da440c01168880348000c291140c441002d0038403400194140d030122190350010100c031813007403408509030303030005818902804072010361207200d542c0b8010810303141e100d4201d0140c010501010103808134060311580e1028000400d81c02009040768004441c150740d01000e1005110703181d0f100390104c900c1680c0b19100c140a181e0b86880c4c80d01c8400300703507031010b400d03100e0003403006d00d0781c2d40070340d06103000300100a00440e0404d45104020b08040348140c12494035400c001f48000b042e001c030442c2c044540102d008103500d10300802601c03102d143c0c01c941480700ea4091580080240f21900e0002481181c45c01019a00c4000800084a215115204203400104c48160620802c00448d00942d000046c00403640d16844c0c0f541151070030100c80358000340c0441d00602d9401c4c00b040c0c043c07000d4881c00c820759008000398030384070b804a00340000f41e03841640c22a03030060f99911032400542899032800381d100d080700c0d01e91915151001c620341 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 906546070 1250 906544820 906544823
    0x91e030207140315090309134503020c0a09090201081e040201050c010f050709090f0b060304030e01020f0d0c2d021c050a06020403111c02190e13 64
    0x1410300c0454500c0101c9400c1d540310030098018103201d00c0c40800c00e8000300014044004500003049001580c2c1c0e43e0204810306817012600018080340c3d0207070704440c1c0c0510581d27001c01d10030b1072101028080384581c010506a0300c2045040720301c1c0507140f1b070490415a96036070036980001e00310400718400c074890b444408490300c00c6c2c07100c1d121526200b40d980c103418507104103c8240e400450001c3c0055101d400581041c0c0120000483c0d0000d56080d00002d80c5d400712500800902c0e416010091800540100035420104100400a202c424004160184030041c0060180504030741444003907403007000100d00801c0342c1d0040c0e420231840c40100920b13180e108079043c0c5950090542e682c13149643d00010782020000c10354803081c49407090742400300040e0b085800c190382100311100030021403018010a1a024403900005941340e0852030560b600e80c0071201442e000381004c054400b41c141d10700c103d10a0841e0101c510031004140b810b0f901058807026048698648640c0080c8541800603041a00849 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 906547320 1250 906546070 906546073
    0x10f06140f040b2d190e010b0a03090203010e0d0f09080c12030f2205040203160e0a0f1715010602032b0c030b01022104030605060f100210050f010f0603050a091e0302 73
    0x1200910400d070101c05c4507001c1c03400da26088600401c4108608170040140807060705002c00e0444079500001d003121006520000360350001c21101b820503038080503005015800d4104682610704084c14544d40d2907038003030700b603004060b240b0300450003400820940d0b90400301c80398040d41d29001714800310001c0b8581e24040d42d00707009405000c21249003e00a80c0c1c0700702d40c000d04c0104e9120101c9011207190006412458100c0b00445000c00d20b51400b07071252005c4c0484500140d007249121070b22038603001602031f081601d441964014030000d0760200c111180d0010f1a030304104040c24929082d810201c00d000d840040500e0440c840001c242c06400499151009800765504108820008044a4183c40c4500181d4904120074000102c05901583e00000c01520030100c101c2d520003c540c0901004807580f01590045040d2880c4654900070990301c43e0000c0e1441c03422b0752400c4490300784403200740160720a0503100c0c00040c00c030f80030745c0c0d010781d003603541292441c10400f00009400955548020055006 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 906548570 1250 906547320 906547339
    0x100c0f0f02030a05220302040e1501090231080712022e030f0209040903030e1b151b1c0306082409150405010f06140f040b2d 55
    0x41c00071041d10792101098860f40e140c0154560306045500d0401c03141c0b26551054403010002da01c6c1d6201d9058004103d000500309010041d0031080d124005038040b414043c010000801c04d0761540806400306c1c0300b50708000740b807407141c11440c02c04000305030000f4200d8400c9040005200c9143e000301c440e140d000f901c4400c44031401084c0c2e600401d030703105440b180c018480071600d0310081c030952045044100d200401401c1810010004042d100c1d004000d500180d01c0d240034810f44070040c0500341e09250030700d035818440303000d050101c8e5840020b94512403170301d00b0118103201e410040283d0b5003541d6100c0c100b5074004a00f044030403401985010081700c000b901c1c05802165000001034640c1c81c2488190f00d050340c4140c1c0e60f5806040402c01005007001e40207505010039914100764009004511507400400d080078411030701000c4401e16800b14a0b95074804640d8001510b840114600e0280706981c0807510040c6070002c2243d1520000710002c211035455195950000d03d110902c10165040b40c45501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 906549820 1250 906548570 906548597
    0xf0a030b18071d18150307080f06040227040807080c1e010501060903031707030213120b06010813060c050f07050708250e071e0c060507031a0d05100c0f 67
    0x1003461039a2032801341803402c02003107013908501410040f10b000101100c40c1d668403a840b40341044520218201654803070820300c401c61806000100401e2001d030f50036403880b04680d10440140c280a00090010003001810038180000e01c800c41d807489040000306c640c00c801e20b2405032030300d0920407e810036952900c0000f11389030b032094400300c044a0305544c400c07401c403540e0180b001844d8009003501c810b0580c01c010b200503910107140000e0080004035110b500500c101d007080f009030310000b801c040c10401108100044071403009420301005812001c005a440c043ca48243c130b8520030040e10303080500003c1740364810080009200e80650700b04e2400d49135010101001d24010400c0c026454194bc80508403c0c45565101c045155021069180c1600c2003082590520401011581c1c00c03000a82e41e002d1110a10416008041e000021482d0030850001250441c02917104490051403280030701501c44000d215007000741d20209001c0d210f0402450b0303520003005c1c00c0514822094008104e140d44a0b10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 906551070 1250 906549820 906549829
    0xa020a020d08090a091a0402180d1401060806010605030c070c090213030203280201181d0a0506090907060513030b0f090706081003020f011b080a090503030f0a030b18071d 75
    0x806d140100d407180c81d081c5440000300000717034005404054010010711405405641c40b0100e5880380c9025403240b911141302c6404e01400e45580e0380040e03006610100040010b2540302c000c480c3c1c00f07074120340560b80b00d1040d450604140d00d0b582e440000810700206048240049945500d400c0300c0c421400c9854401c1ca90780c2204400340312001000000c0e0102d900d200c0554028110031240d20007000318143d00c82c0c1c84001c1400c0d04005414481c201c0d00c440c4041000700c0900e2321840d900031340211000e4000f407078860003013aa144a1805810100400440c504144080d1039038084041d43e40710011088a02d40000034115444007103030104000e1040200000f6403034003410005020312880c03001d510000b4203603000d0195941c0301da881e41d4108500c2441c00840b6040000701e4481c0c180c4902c010695808440e080100b1314909600103074844e40041001400c8007031450120303006004d00d824007003007104078040000d10a008840104000304000b00822070700d203a21002c41350031541d10041c5c103145461201c2c14031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 906552320 1250 906551070 906551081
    0x40c0309080417030c011803030c0c0b1902040b041503270b0c0f0a02060106181d15030a0506010302090c160308190e0f061803040b0a020a020d08090a09 67
    0x5030940381d040109200fa819918824038810390f00404481c82c3c95802c0d0b4215084070040c8840003604104050004100b6515008031003c40072039250440c044070182c0c4a070b070019100504155400750500d102810b01016a8060714010301c11080031588940d52140311096606042c01c500d800645410a180e0611130b2102c86500304a118252803850803801da80c504405010240c00700030720b040d050000c6100f16103000000d000c3e160f2158054001d55141050103002d40d031420a1001041a00d8a418043e45085140d148842d95011400e070f240717615001089003401c4c52030322a154242c02034481000902c0b00c000f80c0030b41201e00c00e80300c8080c01c1d92081083c000038003480080710140074207a541140841c2c414910f40da004694250f80300d1928644042a40485004c410701c4100c40c1c00403512814070305018000136500c00340902c04009698007503029039850748103074000c3c4d10404030041071200001c0d10030040454104e9001d000003c9502050802c024560821003c441c0f00d00031100d13010031001d6490151 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 906553570 1250 906552320 906552323
    0x41403030c0a1412010303051207050c031c0b090115110a0c06050307020c130603050712050304050d260c010b0d03020616030b090f07020f010501060813050a120905040c0309 76
    0xc0500340b080d000707400c5401008400600a400c074061204000e420300c0190030b00c0c025840b90b100d00381d90780c8008004003040701300105041c06001c82440801800d61012080f101c00131224a000070401c4101000c5070020551311100d90b403c18040b42c00881d800803030f035041040a0a0341e40394401e1300b04c05281e41e01d0752007000e00001001b8443d551000c1000d40d00a0024503003091840c016928001d458102185c0d900c40100e20782040c0c6a01c48400b041403020510408004d40395120340c0442060341519090741c0ca204d14030890b030080d026049040180a00d01124900146544194a00496120b5021040c41d0800034030ba10241d40b07007282c0141649880140500300d140c0c0343d000381a1b03551b102d080340b4524801c0b814025003859203c1d070001203165582e2507810311034cc00440003440d650620010007450143c0c01c503100c0351745a241c0401842a16006405150300520031000d040c0101c1c00c5140590400a02c05c0d00108110501c2c051341e01c0300d42d0007200700f84c103650302a40d0411140d04034560440603035200010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 906554820 1250 906553570 906553591
    0x8090604051507120c050a1803260f0a200c180a11160501060b04080c0609040e0a0c0315022811070806150f06030f060109170604140303 60
    0x402c542031200300c507249034404020308048201018400070a41514441d45100b00003440000c1d010045075001741c2c0c8500c21070b03025050008120708660340d0102c8802d90140b411145019001d86115401100040719240000c2d07000039925069516005171131500d0951600089070030050030000948400106181c0110f8010301d6003408a1803040101c48c09100541907022042d1140a0000d152401030000e118203181e0b94000070008103242806401c440840e0003140754168200400c11000b500007030729880081301140e12541d28003013100002c00030142d2118415244c003e140d071400034441d2074943c807402c89000d12003140300544c01000c0a4100d102c0c2e40456100c2e1088805040d107820300c0705214214080c880d0410866164040c54058a400d000c1d5010984640c001000c00c150000c1c2c4808000c0034140c2600e0800c51400003800150075404002c00c1803103c0c0c4007403c000b440ca0303803264440c08000c080040070a941000099051511010229801c1c1c0d8141140100028240b400204403881b8004824 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 906556070 1250 906554820 906554833
    0x130f05090c210a0605060c16080a030210050903040e0103080306030d0516060e1203040c09060504060e01090b0d06020a0e1804020f1c050723010c0c30030e010809060405 74
    0x50b03815050203000041420b5880c1d40104181e00c80300001e04541440310002d001c541000ba40d0462600c400ea007101880340c205d01e040b100040d400007240c81c0d103c1a541e80101e00c541e5484411403460291f07500140480c44e000d8000014045030f9002140a0001581a40c0c144e0050513021f40c8c0c2d42c40303506510a22a680d80e5541c501058007584940c0c3c031809840d0549481c0d080b03180c00102035400540b000e880600e80c96804000300c1e8007a20526009000a40b41400030518040181519800500c00c13440216201c83c03110481741e503061400103a07070303a00142c1117441e42d40e007030001080c0019040505001c0c82100301610300c064884c0d40224400d960081044841000b0801032008140140311000c00038490304202d580020740902c0310a014120028200004024020f0b603c030040c201030984905000c034216021001c41c0010500070151507a9103010042c21003c0c0036644000301283c5515001e104003140b64408144d80303c1d00c6004c03610030980e503c0801f41c44050199440d550240d90040c603071707440003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 906557320 1250 906556070 906556117
    0x1b01051320060f1216090b04030303020c1f0f0b060301051e0607050f1c0816030506010504030c09061d090c0d06020405040e06161d1203130f05090c 65
    0x6100740d0300200500b03050f00b042000b01011510380c21500028400c2d200300b804000481000b407810441d00c0d0179070320349682c0803890442d400001d03115034080901095000103100b103044034100710145901d504c1d45100303207103c120b4a0846000b012155440c2d88418188244c648040c84c00c10196030584100800035a083c6a413214007a085c0129003222580200c0280940c9021038402c0c0000510400c3d404040c1460120f154820040320481c0b20b40401840000c400b8442c4101103004504641200744c200041e081c1c0b601001030380c4a0169030f0004203901d0003010f01150306041608554102d40328407000705640c0c42c810300301903503419088441c0c0740c40b0762021500e1a458a00307144800a010b001d120010b141581710404101510040140642250f000d0818000501000f0170380c0703604840070f0b2910b802680000c180d10411845821055803007a110140445403480040c4111540230040452500c0341a41e20744a603005040c0c2c0e07104442c851420200004c0400d120001201d0001140c0e200000149210 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 906558570 1250 906557320 906557363
    0x604091502070302150a0204060906030e25080f030c0106090c3501090506011d0a0605221e050303090d0305070510050108010b09090715140c031b010513 67
    0x300e14242c08501ca24117074080482c4000c085280520308038000544c5e920301340300000d0030446040d40505c0030503103000f001d03c10307951000c038098940014a070810350642202414030845452146c01c8245140684403d80900400010044c010081e2813402808540d54400c400012a26941c1d003400100340403180c0c40c403078050542030466a80c9000210102580219103404040c50005d800c03c404c119a15404c0c004650f8000d510315240e1001401501e06030b2503e4000b0030100c42281c803440050010115420442c201e035013030b0981021b102c48408040d465075420342c1039100702c0760080441c0710092016021070f44e41000710482c1c4034204042d1042410025640c1d080fa500c1e40050005d4609000c0c2c5466440c0e880100d000d194002d143c1907001081d01d01241c030401c281d1a6000e82540c041d58800f100810440c8640400005412101d090005886080c0f2007100c61911a0138070382c4407640400039039560140e03d040c03200c03903040b03096400030402076a50b5014020032004281d00982040c6102e44110b6a0490 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 906559820 1250 906558570 906558577
    0x14040f0308071407060b0f1e010518030a1b090203070906050702010203070b190b0d051009080d0c18080f25080a0c080c010f05120618090708060604091502 68
    0x2541c83c103a103680300002040da440d5003040c0303021181503881d440b0300241c500d001e084c0c1407841c0e501200c1020071840042040400304c03002d428414140200410f0403d07040503140540c80c1d961a018054a013102c9852516090000805d000700840e41c12045021030300c110903200344c920440c019140c207400c05003440c000b40c4440e084400100d04500c020000640062403841d0714601407141d44070b4031164000201411403c1e90b003105141070169003002d8101011510008241d440e371003560400140360300a500344000cc0c6e20036040e40301c0102d17003442a814049603004034540b51000000021031405512400381c40d442c4c900f0035070b000c0e460350320032407003241380e0b2102c4141e0409039403401d17250342c0395199034107010740c02c00e01507400c00e5078260803d000810400200b8403070018110424030b09440e41c1910f209000c1c0181c0a4680124280040c03000003940756120740c0c04601404a58035100c02c1c19141000040703554586a00540d1800d008000210b01a03007030500034142c0b0a0b9200304c2400500c41c02202e100300a41 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 906561070 1250 906559820 906559831
    0x5010f182a030203031b0601080f030702270c0903060709080c10020106180207050d0203040e070e04020702060408010b030d020f0d030f020d06121e08041509150f0314040f0308 77
    0x85407581d0000040c2d804100400104044483d081d5281049011440c1400c005030320000160304282c181400502c40401118511681103425403402144011a070040b00c0403607079909085282c0ba820311030100b008002810b9040c0c2c0c110308a925507510300900b140c5006241c0310f50701c025130200324002e80c1450312a00c10b056160180c40005441680c1e851102100005030391450700146c0d0000e01481840000c1c000d01c034001c03200e80005c5161500d0701040042000b0010f0030007003081204da000340e59564403901140d19107500103001c1c984454030f030b480980c000c1450902e5684207101c1d2425642a01e400801c03900149056500904400c40288000340d028114140ca0350800c2c81d8200080071020100d4401c00d000350582881021603201d8600c0c054404503014503140301112052504080020202c0c0101d60030303260301107101c0c880b81c1107001069030040e2803034010900d40c100c04020010720f140d1000241464600b555401d206a06d40c50010100c00c1805440180c2002c044148400c04280108015504032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 906562320 1250 906561070 906561143
    0x4030b1b07150e070f262d01020403060c120905030405130e01060b2706030610051e1c0b090c1b0d0c03141c05190905010f18 55
    0x21414060244c2020041e400c40305007100051001d0224a02c0001e04040d4507802c10507001e8000081c1c12040d030f607400303088801092040c060030005220b2019450250741582424001e5440720b4807894000003a200f55401d0b0800901c0c1e034040765000c840c4900521542e01d4101e4095031034642000d0506c50f84401e00e1000d506015107907008011055802d1054900034100f1400300782d00e482059144003061010307040d0341105040303e00340c035409560304d40d011290082c030119224081002d00010a41c0c09005002085410003001410810b0120b6000300518180c2c004809039013031004844d1145007112442c8101a800051900024a01d615944028110041042da220340d5050546242520700a06a68160006108103030f4550415400c4000c0400c00c1c502849408d0500c5e1020b82e41304071102c081380b801d2580607282c00c00f04800268413040c101500026101c00d0210f0f50960034800e029201d01407202a54a02e82030700c981c43c0d6032400e10600700d1107502c86070030ac0a00080c1030700712400044104131501003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 906563570 1250 906562320 906562331
    0x1b0606062c040f2007030206060109081207170a080103020f0a0303090e040f020d03120f052509120609200901140619020c040506060406090306110c07060504030b1b0715 74
    0xc51400c0c003a01503808130120000d694030022803800900b820070141201c0e060059660007403041540102e001d403101c0440100107511040a0304002e107011003d03100787d680109000408880c2ca80d403046c41c0c40d060701e009a402da08484020f070b007800f100c01068030010700000d0b00e40005029080e100380307216811034040c00006207090200c0e00010340b00ca42805003200403401501084810400f0f601030100030000c60001000145021600c0318808442c50075514501c417803070410138040c01c0c02058000054a0180c0c1807801545d007a00e080d00003001128420b40b041601d24030303480315144002840341a0b81c840917041080903403030044046010410780401540c0004140312200e120380da000007125144129900400a10b11240184030840c0d10145c04c041c00707010100021b20019170420003010072280e10500014407000d00c070304040c259010f801c61030b00c028002c1c00340c0041d1241e070210150003924000d0301388d40b030b5549861102c0940345d92000c003a041005018402d01d80440c8888208503407a4100c0d2102140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 906564820 1250 906563570 906563591
    0x50c0315011a0d0204090e06010e0a05010e04080c1011040e0c040f050112020d14060f01080103020609010e041104030c0303120c0c11010302120412020106061805101b0606062c040f 79
    0x503a10041f10002d000c1c1d100c031004201514610f14102c3d04802d1840082195504260480d03201103c0144040c2005900080d49165400c00300131441401504000800c40d0945840d0b007003030b05920500c242d54501c517101007c00c007984c00010440d42110300f4100000f820714980001940d054204861031032155600b8050862002c850340942895124020a0503509140110030808443c1e48038004504011002c8010310068461030700f11000e070242400e1001003000e0b0b000001d8081c0024040b210300a000106000007000703500139402080c2c906c00c0c0c0318418440004803510007203840000880001800102049002c40c4444c402c2d10f400c241c0615002d0700c0d01c8002081d40c0322402e000e69049502d40e980414448151794203124602c09003a481c07902c403a1014400c201000c5045d45402550311904071182c1d541c00c400d025240e030040e08008000c041c4000c03003040c148040100080e1081c100498180c03c2c2006054405000032100c1c4511b00c104101611500018070005100b4002c40c03a854581c5e9a55420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 906566070 1250 906564820 906564839
    0x402150c010e01060f1e0b0306120730080306040507050c0f1c05070807080313140a05060c27010e04060b04091a0303030a27050c0315011a0d0204 64
    0xd10502c240081841d900d0301d011003032440700380d80c00f080403400040040c031861210400c40404455a10300000d450740c5811002402a501d80381414072280b044110015408503801c0c11003050302e00c0d000c00c8a900c08082018141e141310f41050003000d101c005c10000d00030f0300e041d030b00c07050b0010b059107043c2d400c0203c1a44e0071490042e144007031402680c015810dd43da16440760b0700c01c110700b062030320f0700a05050a42e560100940214200201a80008800210181500c002e0700c943d0b9a080600041041c0410300c3c110744a1b8207200701a50700c1e0240000003001c1101035000c88200d698801100900501c1c0044040c0548280712442810800702e07040511050303445004060250a150710b88070390315454412007201710b9045a103000c5d10f004004540018940d00032050383d0b80202d112002042e0400805001d034000e98440c401d0b240d00da003001e40d039003052100014102560781ca0603003c0310340b89803214840a10b020b409103e800410300c0311610340e0702c15036424009030005000130100542815220070204 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 906567320 1250 906566070 906566081
    0xa0f0501021213050106061d040e030918101d0f09010b030607050d0525080c0f0f0901020c030a0b010909110d05062202030d031a0901150f11060402150c01 68
    0x300c3d801e0003c10b082800020301c05d035002005d07075003002c2065511032240f009103814000c8003a8461540d0b040240001c107814411102d100100a05200080001c0060000000000c0d03036082a80304000101082020706a6800744079800c044101010503030f00c56a43d28088200201803403101d540b1803620382c0240e1003c0280500030405030301c5894441075039441540845a00500c020480d108005000b401816030303c1445580e4000b501c0c1c03140346945c1d82845030743d003407042c81d000341c046103000221700d60302d641182e0103010541800da00350782ea122005010107594010354039029043d20360603001080b000105900c14650903215101501c10003400c18006051600d41203020b550580120007000100f041d410314080d1002c2c43e58502c40021b0100342c000c80d0380c03510124014014195640000f0f400440709505082c3c0010b0010050314866171208442d11b00ca181e280d440c040882d40c0251a011b24600a20319840c3d881d13000c0000701100d50340c64007000007509900c00340c0390303425500704280228400c0a0080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 906568570 1250 906567320 906567331
    0x9060b0d05030901020f06040b06120f0307051e1b040b270109110403030503011a0d2307111c0c0f03020a0201170106021005060f0d030e0f04020c0a0f05010212 70
    0x7850f00c0340c84090019007840d03440c1080c0300d91a000ba07001c000000f40040c0c5066000241550f128032004442102249001c01c2c411080702103120114041c000c00100181c05d444208030707039109210000541d04c0083c0e482c886045070740300c98170000c207141d4502c0c06d003944414140c0c0c1300245892600c919840004c82400610a651000fa00707445006010100c5140969003201d24058503091910740385403402020740c001230245000802c04c031010810f000c1840c10685100700742016081016642c0036108000402d001034840700c2005200001410780c0707000d1a0740c0706000103800d002c2c10502c41c403036a009213402001d01c05441880070354410400450043c001c03945200d40329030024030400007580005480d110443d03019640f400b501500511003154040740b0390b50035500305040810340c3d40358030000540c0300215141541e0804d040c10301210078150700504040032170005442c100c600d10710707403000d01c401d904c02c2d81d5074628a075014081001c00914107040c19040a130244000508101603024500a6298281c91 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 906569820 1250 906568570 906568573
    0x1608031c1b11010b0109051302031b0c010e0c010e060403081606020304150501090506060a0c031e09050a120503040e100b0a120b011815031e020406120c1209060b0d05 73
    0x1002c4a2840b003d21030b00b840c81d1006d00300801824074060025485401040da03212083e43c003c0007142c10b06d00d41060700b25104c55602c1c203c1d91680148928140281100100c00003a8030554803a6031a9500400070b1000588025081514145c12360326514803c1d0700050408030041c1d4080b81d840040381543c4040c502843c4548005594102e00d404030000b83c0d941071300f11000381072404081c41410342e105000c0311a801110b00b400300545803582000d403424001c0f03e110306a01d1004010f1b150300326600030030040540e070741110010103980d1a00d4104444144503c0002c00941c03080000780701c9004442c0195920045180b1100e00302c0342c803401c0244075904450808004509200340c2c46100308224050001000001e20304200040c10440c42101e0a120a2003418403c02ca2100c0d2002d410b0321076045101010300c188400a542540590302c14000e510521941000491546e8800e1608801d8050f1001d612001c0da5041054420a0341c820020000c0d840101ca1240d070700d940010b440d45814803803c080601500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 906571070 1250 906569820 906569837
    0x912010c14120402040b06070f0605010f0807050a030602130816090515150a0201020d18030e033009101206090c0c2a0803030106021608031c1b 63
    0x160014a400152041d48001444050701160160902c1903000c1d030111404640182c503880801c031944207002d4043e00c02200c1c01c0c00d600920040b600018121002440021040c40d80e9030703049600d4901070300955500140d008000c0001c1540c46e009869002e03807040101003070a039140c8101340740c5070303140042c2c00031101c0e400b04c01c0181c0700c0188502d5030703c140e01401059200c0c1c2040e0010b111081121500e051030240819041e802e20301c01d5061301d601d40c01d0381900700f0610b400e000d44c115864a100b18100c0024540c504046100d00f404110703000c0740c01070500042c000903030380b54030644882c85444215401c00d000b80075045080ea22816040b103004100d48440d02c211031580e4000b01039582d80d80240525500744400250b030140c4c03107980850742c02c2d00402c2c5c48600c602000c075280003415091403641c445084408000c541010003000079412034070690200c52070300296521000d86048988a4100309400c141725400049440046034540610100d10002c0d5242e05c514602c44a180340c03401900c00034a050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 906572320 1250 906571070 906571091
    0x2011107021314090604120c2102070b1810020a080a030902010c02131a0f130b152a1603020d0c0810020d0612021011010f02030112030e040501051c08091201 69
    0x5811f200c1860646055140b07a21251500c0d400015005140c070740d07801c18040b598a00c5882400b000d03020700190400b0541d520840144200700c44090034040d44200c240640c5604100c2c0001007461905902c0340d825030401d550004198010303e035000c42603040c481d10140c50701c0103945018407810300d1550b820001440e40304021112000400002ea03a42c0691000c1c1070410660f0354200d80d43c214101c801201040380c22449021036103452003101210005440482c070200010401c50703200c0c00701c00403201500904002c02d10403a076281c5907902d98441460000c40d0030b10150400c2d84090506500a0203d10606540c50342840d1504100441e01201d1560225030025210101c0c010340c0001c0c01a41d0b5030300980c004640002d0145041c01d41c0e10000c1c4002901c814410810a401040e03480d202e039075003152039617901c03140d45ca03170440580d00c228000307034070050344500740c0ca032501c41c1d1070599101600c4c428026031141e110303403042ca0040c1c4040d60614014007181900341e5440100259205c040070000c034200406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 906573570 1250 906572320 906572333
    0x1208130e040c06081005150903010f060303020d140403080301090e03070b071d030114070c050703050d0309060b1801090b0103091b05010f020d0c030509040902090a0b1002011107021314090604 84
    0x54880b580049280e81c0030003003a0307a02d42808514203141d4040030780c1c8e280e580001a00405098942040d0642403950010174950003041d0801c9560090315040c01404034a00010418403c40c0401041100c0030300c010f1089005507032041c14070943d1386046a00e010025155002860000c4490070006144000c00c0100520303800ea82e00a00030050b40240a036806c20000d039404680b0040c158410803003440d03120001c0c0401003083d43d0040d034000041c0c0740c1003a540c0702d004001d41100c2c001952400c2c180204410355051001c0300d204100c2c2d20100300c00d0076909102c00e14001d007801d0703601d0307904050701c0b200300300701040301c04200400c0b0007540100c0110b800d14010000d41480c69017020345056400c0f2041710844580c00c0000302c5c0d81680e261034495a41c5994030001401402165001394106203024108181c001e6641d01c01181c00208070740c85444515070300030072802d0760556032030f103000040140241d000505089500d400650070301c0340040781c1805840e1000301240300803103c0d80b030980e1120083c0000d0154 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 906574820 1250 906573570 906573587
    0xf0c03050d020d020703110a0f0e06010e0f01270503030a0816020109030f050306060d0f05061509030c01030e24070801090c1407050f0709020d0b09011208130e040c06 73
    0x41c600240c01a1059908040d4581e400c61002a00102c400300c50a041651840b055001400480c1c29607142c05844103005400c9a00071941d1a01242044c40e4055440c0b0f8048254003407000140e40c2c03020301408d07004040e11141584075906c5e00d203500101004c50103644c1031020380030402c601c0c1e43e081102d00e4101030400d03164042c0c08140042da4903119512011030761080304180710008509209030b41c0d4030f8020100d07009202e80d40100800320f2816100240841068100c0c501461048070b802c2a13518107140c10302982d01c038403800154103910400c1d090585500a401201200d400d15041e5041c5081e69040c0000d41c00d2200020409810b0074420042415000303818203000d004455000c20110903a03110141400424540017607e04c0c10103d00c0e841005400c101110807046500240c0d05542d035115410b90180d004075080c0f91560b41030650101603400c0003c00079040350381c0311102c0008503c464454592a030710284d0b494a0300c00c1c0010000c0f440700b52100c01d103801103204203803082403c0e2422500614614 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 906576070 1250 906574820 906574843
    0x80a110c040e03030426030a06080c01020610060f0201020d110702150c030703080a0f1401090c0503060f010c050312010b03010e0705070221010e0f010212060306010f030602030705070f0c0305 84
    0x30b29084080c1c5403100004244c0340e0084d0300c00c254400780d00303414850740f07611039110352155072150002040182411712500f002003202c445c135045480d954144001a41c4903c8110703035003c0c81d00100c200c204045c07403140303080b145030781014000146000d80c071400210079664141000201d0f01c1001952404600341403185801c40456881894100301a00f40056180c3c41060005800c010020340030454803e615401880c2c4248401001c111480910b10b40108400007481080c0301c0f145450301030440d090041d01104d204403c000e0000c0c0c1803250034001034071400c0c190402039810348828000301200b503000120890107450803032401d544039858468401a0710200802100400406100f40401629400c2c0f141000c40141c5003c480310031180b4100600400d00a600100107100f441d0180900210660040107140d003801d58501955480c681815520042032080034940005034104102090080d40a103030000300c1e61811601c1d14146880780001100401c02c15626428a560108104081084000c1d68807 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 906577320 1250 906576070 906576079
    0x3040e060a0b1602280501030509010903090302150403140313170d120f0c030203091c05030a09050c04020a1101060504200d091218240f0309080a110c 66
    0x7410b10303010381240d009003041c024416210542c1c6408640d15580c45211007042d25041c8942e1665080c04040701042c01c1c40b0b80741c0480e14080c08030b0b295003418041d0401f155011b445021055246900b4400c0000d140d231128004064180404400030784004100038945840000541c1c56100445880c00d07290f01c1580180180c4011414040134004003003a141405152801d055501d101c050012a01510843d0803003040342d480c0c64000715009802da806980078440c00c0e17040304c00c4030214601d01d66020001380c1c105d401007101400000d998414a401c1801c0ea50703c100117881e00c640010340071400b660405c51401010581c13005c3c10840303003842403203141c004040840c0c0a100c4500d50700020702d287c801203100c50b11454000a4803070041c1c065600a15146580008007241c1000003010040c00600f195100c02c0124290100000c1cad5421908900c005440c4a901c81c1507034181c2500040c0c5d07002c251006818280340d190b4814402049101c4090000010b00d0703200c42504e4051880e1060a20800d8070707100d23118 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 906578570 1250 906577320 906577339
    0x80310030c1e06050702130e1b0402090d0b1807030c0503010c0305160c0203010b060f07020a08030405030312041a040510060608150123030a0b0109140d0624030503040e06 75
    0x5103030042c1caa070340880b0003504003035980b10300500118400c0600311034034180880c1401c0305118a100c00040d118960107090441400d0402a102000142d200b4182c074140e01c4090544000d000c1002a00041c3e00410610301c401640172441181c01d003003d002d5482661608035a810801c02403c0a0182711480140c030b00c0d04009034500148010307403081040c0407201c1005503900c5208210b40b4254050102034400501c42034590340110300704403d56103c0001280541900d90f80025184400070a076825a00002c000d1421b00001e9004c060700d2840c028003d50b420f08000003220700c68103815a4840c003c5000c2d4018029200481b41640103540345c9034424010009820100080d41d80f4524002c04010710034030b0310840007010045844801c40c40c070418080307520b1000051100c105040c6e440761107a98000c2c1c03110042d09680314400d4650241c400d021326089030740b00d402180080d00c1a4031154142000b0030300c2040800d10b8069410700c03c804c60b04111884d41c0b00090502c242051025000e60108040b20311003031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 906579820 1250 906578570 906578609
    0x702030a3b03100e0c100503010b030f0406090605131b08150c040803031305010506101e1209080301090501172503020402280306151b080310030c 64
    0x8500d1901e14240120090301da0030949555050100c00c0da040e2201c0c40500002c0112142281c03079411407041d00d0b1041030200c5404e20002c2c02581a070b4121480565a5415070b0344120168600010051013180c881c0c0e62a140c500010700f952044900681a0882901d0241414940003e040da0145158000f2401040c820400002d0005014105481c4c0b540c0c0308400c2d031110450301032035024a800414a60001104000c1c50440c40d440c1d62402034041c40090105843d114240006800e43d941004001004003030084280d0b070039680499544a000c2c0307895400881c84c00b4060044808041044803080d40c00001000149407500865002d0000300312200e02400700305080d5552500c00301d4645c404c0100314880300c41c1a0030041c00b007600135074000d0001d41d5500c0d00d410850400d66040b0265104446100d001945414821302c00c50782a40c4011904100400c0b4850003911000b4202603840d8400c4554014480040d072140007560103031100c820424116804c40c0340c00022400703181c01c1194075190702001d860303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 906581070 1250 906579820 906579887
    0x50105060706180f0f060f0510050d030903121d040507080619030f210c0c1703070c0f0314060601021509030c150a0c0518010f05040e0702030a 63
    0x1050550b1100000960500010402041d1401000080d0810089030305400c02c2c4071351a80120849803003402d003004405c1544006104455081c2c3d910158001e20040600c43c60400c0303400212002d0090500c000c0c943c0c4d90744e691200d800c03110340c0c0d0f280000720f041010b260038200c085010038100d4000c41f4180605e144c110f1008000d0040184414410440d40c02c4003280080a00b600201464100c0c0c03110260082c98101009a550602c604481e0301500b111805e0308030348900b2641c0c0043e507020041c0e5010a1800c50301036600311204c4096090b50104024030000940c00f5941e0900030910050840e1020f40b56003003a650000e0705528108094002d0300801c001aa8040360450050020000e11441d03a202d032800c0c00e00d980910070261500b40f0505201101503110150a54440c007110001400604d88855048a503170091000c1255210140b0046038660341c0100c1103c818034280d450304500b055900e07000409a82001e03206400542c0000441c0b00305d107980b1891015a6518a071401407040240302a040c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 906582320 1250 906581070 906581077
    0x402030309190b030a0504020a1205100c030b04150905010602030a081f03050a0f050c15040b0c0a0c03080307020c0108270c0a0f0f1502071202011b0501090c050405010506 75
    0x540304074103102d40004000d0340c1c0d00c0003402030042500310949a151008074800106025107050b445026510000107042c80b14072001c04483d9400b10260501584000380900a0020a00d081042c19215081b007078143e00c507482000d403c0c502d8141c050b5540d9180041c807004942041c1c0105003150005c0040180707107070700500d58a800c00300d00090700051800e141110000c00702c580c2c20041243c0603540e0490b0a0041c901a9808150f01480581d0045140001080200c620f101041002d008060000f00420050304003d8600368000b242518544445076940002e80c6070a5003044864035004024001286c1c0c1c10010300c01c82c0442030070003d4450400c01030509030000c04c03601058180c03030140044004048140124032070f088015107058081d58642010081d403000901030040184a4034a001841080729641886400c500b5000b40003460304044000b041040d08403820790501c40100400c101d00c0c00e0000da83c0001038081c000020312010350b894544402446544001d2003241084010302c17481c0c1d00c81044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 906583570 1250 906582320 906582337
    0x1e0105090c090102010f0207061b03060503120309010e07030f0c091820040e0c1c0b010e130c0312021006030b071d060d060303112a040f060f180504020303 68
    0x82502d492000d00100c2c058040384207000145400450250308200b42a00607600040e42000c50300d8815580d400c2c101c044034131030300c20a503040d884280c05a0035a10305a0042d42c01441900012a03064038070240d030341c80e00c10154000c0b00c509000c0070142052080d2104160080d200204c4240b010a00c58181c580c148103030000003900400006019200703010190048192140d0054014004420340d41f8225440c0c40c405c03000b1900800d00500c00d1468022148008807038070303501803226104c0340d0074400c4170300582c3c000810014090031158941d1000c243d40740300380402544184a80600bd082605009041c0305a040c262085241000c40900c000340e007420b0f80b90751001a40c80d08001400c0c90400c0c0d80b00600c1c60f00003541d04000c00140741d5031000010340210069078020f40383c001d5940c0ba0442e0302503461511712510030720480c03049081c070060454000b011000c401c00803c04038101d000c40700040111401940300c13542d03041204400304142081303081c8a483c108646601046545400e401094480c0700b010342 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 906584820 1250 906583570 906583591
    0x9010807030c03170c0619060806011d0403120905010b1507030f0e060915040905180312151009170a0c14031207051b0a0602030d050405070801141e010509 68
    0x28004c28a11001903c90001e000001c80310b2078209540380305107044c031030500501c5103401d1490120b00a100025140d048030f40050400240144000440410f42030240c011400c01800c0464020701002e43d0050000940c01000000f640840400c01c024a842c905844444031840074445180469000b600039500703081c442c00e01c104480780820008003180b14015030f2a0f8050031400c400258801c41101400c1606e100e00410803450b1240802003031340c8002c3e8518411290700270072490074400703595105a60040360151080050300c1941000070396142c0360600000011701004402c00c10554a0040f071101c800303101d009090481040e85a420500015028440d810002040c041105031030802559005940084010783c030f40025280c001c1d11460074a0a0615480d8660240c03501b918250b1242c000300d0b8020380055180c101c18070380d031030040c2400a100f80c890f03000319800001d400d0710a01500c4d00c07110b0400210320030340c5061103107200700b01c08007000e58110581c20001031090362908802d050b0030004440c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 906586070 1250 906584820 906584843
    0x90507050318011509020403060f0209100e0a030b1510140d0908070b071707050f0d050a0603050601090b0108090105041101110307080a03020301050418050d030906020c0304030b0609010807030c03 86
    0x74955002d0040000041d5100d0b400303150005d036890090303000d07100343c83c46010306000003151110a0000d80c0a00009d5030344c0100c1e808944039545000e1407e10101c003501030701141540e652038940003a15075044590880c400c80c203603071400042c0f03400899116034030014104803990425504d03094510340241416510385580e1022283c082c4100e140c240e6541d542c1c058010503451800c058010076107401241403200400120001c180c5841c001c01c1940c40501030424030508140c4141c554501a110107417000d103240c3c0d034610f4044003207901400010701070807881c03a001c195030381100001041c244c80240a4440c503450318003400002080d02d04102400c1c00240307070075a107080e41c042099041d0f104140c00188440d00c0003032031000302505500914103e840c02c0701c3c104005c070542c0c01500d110288448005015401407a07030014854085d80c030400c3c02d2030180c240181841c1c18a8440c07031940e8400d03003043e0340f4010a00c0c2000002c1c0303001140d660240c0244409407640600d5550350540c2c0369001d002c002c06000b002d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 906587320 1250 906586070 906586111
    0x36071e14041806030602070302071d130602160c0b0a0f08040203070e2d0f060d03081b090d0b0a060b04030b132a050102010609022d0f04090609060905070503 69
    0x15000740019582105c001c55a4080615000e95540150b03c07660840d018249840340c40107655103071070b0748288403044140f01000b0f040e550351320003580042040000040040c42c20404035000e072603540041c000e0040c101b039990608880c064101050303012110208484101040300585010542400b21404416000d18a40f5081906181900315603032209000682d804c0190240c40300340001c2c0e0007004e0000b0404040d131a4481400850f401e100c40c0640851407480100d444007440c4001c00039010404603401c0d042800c5180060000343c100c2c1001d03180882e401003848060306141c400d40d0001d0800950091606280d0342e6a080300d124010030b080c0c06a041072240c8010b010200c102150100303078071200b1079401807800c009681e040d007203400745500540c40c001c40480c12890310310850b080c0001c84000d08907000d0183d41e1a001201403801001c07400d250510064843d0400c0d40c000d8800b0b81a507a0020540d5410b0100c4039044410551080807854104401d0002045d04501101e8102c11001c08034041201c05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 906588570 1250 906587320 906587369
    0xe0106030f170f12070e1c02010e0f04020c1506033706090b0711062e0312050304050d0e0109050609030705090a090c080c36071e1404 59
    0x1030841c00c0701c1c6601c0010300d07544e5014804641c0c9110b02155100c00d04070440c181c2c00d01c94040030812500c1c644051810b4540c000d90701680d00c40300040002081e01074a043c9400104017070703030049c000041c4164800001300b4000b24494415603401a010750007041c03481007007908405249045010040303a110100c81ca84468410142c4030200e69401c0a802d002480451404a0000e14115603450002d19000402e40e499280445c1e03540c09458881c3c0c001080002c018500c00a0f41d48403501d20484400c1070301c00000260300c5a01c401c0851201e0340b00d007501c900d440c2c00c1060403c100125003d04000766488142040d83e00050300307800b07890301640c035191140f2920005c04d282c0129038002c40e0388012084100032441056422098030184100ca034090003036540e011203991a02405103593380800300800d80c04103102441041c1c070a000d401381e1150010145050000d007030749030540701100020b042060700c1145100321010140300c460a40b804841001c10200741e0701c1140100e00511440a11400750408104072 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 906589820 1250 906588570 906588577
    0x50a12050d082a07030e0a14060903010f1b0f0503091f091403040609050405041104090323040e090d2a080d0b0315040506040206030a0603240e0106030f17 68
    0x1070802c1d103030198020409944003513001503404900080e000725800d4141e040c04031185c402c0390940f0510700804201002049821380140403220b405660310020254030501900681d68904100046d104451140306001829500140100f006001c001c00c140b01d00028000b07013000030200552411280401040f41d454040c15403441e0141040c240c50000d8a070300200400100101c42860b110000a03d64a8007031106890b011a4064010381c4251607008450420703401640c40c0310711903d032600c5d5580c00b420751400c080b00e002d07204590380807000c40c061040800c103200d40d54010000d42c0c02041c250808500c002c1c01e8001c0406041e0300300c948680a1048401118104031120307900400250300c80c800003444400603d00610801e101e07100b06043c03058030070b50442007a40104c0d0030902801503030362207809001c9158005080808041e43c0c07414000040b0742d10018101038460030700d4003201c495074440411070030354a038031820282d41e0345402ca0400000d440920280e201540c0441c1548500032107105c044150300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 906591070 1250 906589820 906589861
    0x7020a05270c0c0312060307060306030209040b060414040602030f0a0204052413080303091e0607051305040207050a050f0c0109030f140706020a05010c080105010504090f0b19050a12050d08 83
    0x1c0080b40100320507100e22001c5d0710a034010b404503200d1075a0f88400b201902e0843c031011350840c2c0e07901d02003400319800044250340220058804190740c1c8450201e00154032003103e0555800340d0100910090070703103141c51181c00110b0504150b023030604140c006904a80c3c041c002d051202d607840400792048039503900740d17485092140316071202c45598012070303501c0341c3c4116034000c0980200d414600840a4407c08400c94600780f800038609680c4110069413554048050b10b548400c1700440050507559a000802c042c0b445040034100e44c0115150080c600102225240c82c150090042c031105641d20a106004036900604a401d440103241403101621410712200c0c1414010400d02007051500080c410510702c1c03080008000008514404440142080c014280040e0040100304070403103581e0801f5440c0c02c2c441d04001038490750f10300000c981c640c04840024503007218800400440c504107100d48010079114005c190303007149595400b80c0368455a00f1300000d0050100100d84401120000e9070200e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 906592320 1250 906591070 906591073
    0xe090c04020301060e0f0d05031e0d060f06260c0f0706050103030c05070f050904030302090613061107091e0510121a06011e050c1204030807020a05270c0c 68
    0x1c1d612201d00a252000c0e031740e20b00d03000d00d203c44940c030380906040880c2482641c2200145040c010301c010701004845610052407100c20061100211100c4144100d0000f00350005c01c0300380ca540303400e0000d41341001006140081c580c05030404c0b560203001c00c1c40030341c1c001d20304540d0f030380e440d9000c2c02100d010b800307003641c042c0216290100110825410810f0001c00c1d0b80281c08a03412959595250003c0e030300180100740e08000150089400603000b034003c1c10240c0700040a42e82040480c101200e0a5200c0d0390280000684804011a40078010b0081e540900f440c04010301c405040c8001d40449a4040300c141054195261300003000342d19844000c2014002803102c010740d03a0a642081c00d80e0030000c2e00c041c0400030051021075080c0d030080c00440310460040d19942e070b480089002c10380d959001307624100e10a006400d0030085810700f100c02070014600c05ca400303d4485500b401030011104490304401e00982513042c05c6c2402103040300b0081c4407c50011081c1500c0d41d2810003e001d9400b0310641682075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 906593570 1250 906592320 906592327
    0x50106140f030703030c0b100b031303030b01050a020a020d1406010914071d120c030d05120a060302060f0307140a02010b120606060d02090316030c031a0f010e090c0402 74
    0x440115500141240da41265102800000c11040645404440c8401404201070f4a4001c0000e42903040d160380c4284850b81001c2140d41c1c509007d44241d000300e400c070002c5488811003070101501842100c10300102840e000e406d00408580280d582c07559018060f01c074420728540380c1b040140d22180358403484400740640f9480d50b0341c0c900580150038525a616001e222040001c0d004e03500c140144c01d8a40200c40c0c000050b12880e200340700210b4440c0f1020741041c05a50701504c0e41b514104400300c1103403550340c0ea0541c0d480c02c0402c11000d0001c00382001503d2800e0440400150303458030269403000c200c2e100c1c0c180d03407a00d0b000400d4802c6d80d00000c034000041000f0910800c025010b610010000c0b0042e154034200c00b42c0e4100c1d2035101d000c22150182e0004042c0010f1031000e4080d4050200204050304a0f032020300742a004041002c501d80c02160700c880003100c00d0040100417901d0148650a0994408141c02c107803d41241060301402410351444692002918a91080211554841300070b00110354 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 906594820 1250 906593570 906593579
    0x8040804051c11040b06121e070f2d1d0415090f05061c030e030f0d0f02060103050d0c020102101b0e062106010c170a0f02010c080f0c07050106 63
    0x1100102da04103848034010100ca55816040500400a414500030f14a41c0b40c411000000b061440e400703000a0801541c1e90801c0c0030b10b0351401c407881d000d10301a8a8007404a040c41e04010803100038903041000e80508441d48841040e031042590b407a0900301e050003590341d06c210b0f0a02d204440c51040c00c9034020f040c0104074040251507100e6205840140b00e090003600444000c5205880042d550980c0003051103113003080410948042400da5442032400b218160329060000340f44c1020000400c145400084800c600940c10007411030b1440c9150014040c82c0d031440c0ca40300d84a20940004a090080c618905030031603109120f080c00e044080b0b2000c1209080084140405020410070752001c6000e40c80403203070624214080d948003402206000c441c82010811124402c6009040c1906100104c2e8032040020143c00311803482454100c0001d0702d035111903030010602c00d410b40c602002d6902d040c1142c0c0760607520080640c0d000100c0103003214180c50b90142d48126100c1c80344003a02d80d52801c0300104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 906596070 1250 906594820 906594859
    0x60d08030a0f14040b0705030603010b030105010e09010c0f020712030516061a240a030e0a0303090605010509040f03030b0a170a050c060f030f060f0d12140c0d0804080405 75
    0x842ca0039a2050400205102400b8034055420584000d0000303484080092400c43c400d9005561168010300003040810800b0701190a407078080c3c00100031314280340c04008450b24244942c110760740c101d1904111440303040380b01079211421070045240c000d0144a24000f814024400c4800c2d2503840c0704415035a80c51400c044005242c04500b070a422010030103061034600c0c2c00301c030410400c0c4a1f0707040507509034090840700401d80d1000e510481496164405042504400c1c00a00c08007030198401242c214100c0c5891011940d050b00318502c20200d05040c400414400075040c02d035244c2c07506001404207584000502001441e0f44072070103110304040540c1c00c880000c80c060a1140c0300e1021603003d20000000c01c54240115800039075880703410700008040000410030360781c00c904050081008507000300040b40400515005c180c60150500c10f4210210381e010101e01000d94003c0b5045040482c00118070ba06d681003560513408000905006c2001d20840400300c07002020000c1c16101310004940140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 906597320 1250 906596070 906596081
    0x42102030d02010501140103090f02030304031a16050702240d02120a09080a1805090a0207030806040e100b011407030e0310021e0a12060303030608120c070e060d08030a 74
    0x4034041d0040c0c00c40804020700500a0314140d4610032171800c00041b01c0d10046000b000c6540007583c1c614052805280940c40c01d000a2006d5805240c2c25032101c0285000c2c034550600240c4101c0042503186051860182d2050503214804d84c100d403800540500d0a000d00380041c603035a00241210400558182031686c00d40c0280000744042c801c1c85080d0b40c2d4002840d08454440c403020b00304043c10008078400c1d5100e50140612401c070146a40a60707501c07080440c40002d41190a02e0025030b00155520034584c20600d19540110119804e200801410880c540c481c034603286020358558442e840c4418980c06042c2e4205826401051940c07500340034140203040000c115172040c02401141c1e2244c0510032280216070702c60640c0b40308002e280c0340c4001d20480c103070b00c9441c010f41003001407036810078641158010440250b0003550f0100d8401e040c19255414594078100030303100c042042207c0c1317040e140041400b07000c58443d4216013045036a0700d8003084d1004046c08004040c82c00020400c585122954080d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 906598570 1250 906597320 906597323
    0x70204060e06042f1c02071a010803131e03060e0307140d020703030f12020c07050306010b1c0b030313031a071412060319080304170922020421 63
    0x140045a00e884c0480060300400031004801c40412541e0581448001c00030240c0c6004c0c1d00345216500b07441566079089820440049491140f40c81c490004400b00580c0c56000d880300740040c61400701d22080d84008000c0503c103481d241990007504105c0d000308a88600d0045070032074010300060540c44031142d00c1e07520582080300d284280d0740d540000c5000008002e141e510807500104030460640e213060361440742403002c10081084003207903800d09201d036001409107a000c22005101840c20241050300b0710300140c011607101e030414001c41c00044400400f501d240b81c801c0c20300007114203602d00400d08601c1403020704400c0303a044c00000010898182403200300b64022107240e4040b6281c900080740c01580082da400b200e4441880080e0719044128801900104001c084514142d00c044010543c07203611b01d4142e51203400402084107001590b6003200e64038803040c031910315203500308000410151104407880508003425045440180681d030458000e00345032210082200c241e000d2400410000c00300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 906599820 1250 906598570 906598579
    0x121409030a061d16030507080d0215060a0b040909110306090709021309020708030103060b06090f10120e03040501020115031a070302090d290103120e0103090c1e06050310030611070204060e06 84
    0x200090b14230012a801c01862810740c050030840490070502d44601501909450744400514030016101f41e200000300010403082c031004c80c170407e9038100060340350812800769019070040002c0000544000c5005802d82c0c82c060f100588969000c0004003942c122608036014040c4005404800c0c084900007941c103c03480754006100491040040c080903006804010750003034074215003101c03c0d141c00e40d8908144d44072440c0c104800210264400300707464000101d001d030358200003401d10055a082c000c0c0045081c40c07410b110700d100d18554034010300c0b07089010b0340c00c1c808080300042450280f003601201e22520000b000440c40e0442030a02d9030800009111046040c01c003011076030316078283c0d180020304882d00b044100d15000301400742502d402045801d1039040680da200f01c00700080540d07203687c0c00780c101c0844240c4502c003841000c08020740260090004e100382802007000c40c40e1400b500c5c0080d654094008150107000c0010364241c1d02038090000c2d4002d04054002c211085e2141001d8441c1c801243d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 906601070 1250 906599820 906599833
    0x40302030910020a081905120a050702070608042622090b010e031b010c06090b27030306150417102909070203090d121409030a061d160305 61
    0x201039030b942141c0130380100303075800901481c0c600d09811020f1007100d81c15400c0843c540320410403c8080c182040760038591355075444092105040e030411299000e4603e50070009500c1c18207803103010f510342d20a110084201c800c00b001c40c602d80003103419039004a100718000c04c480410081c1254260b901e900440c00300519110340f80340e2545c4543c0120b041940090003901501d00ea01161821083c1851103030360501a4144030b10000500e00e104501c0c0c2d0f0343c050400407000d42040c02000c0320b0125646a804104602c01d000c4c0d010081c0c0110480c4d41142d0100d0781d10181507407146051904d40129808010180124014601c001030b011541c00e446104a5004000c00810103802e681d04200e0241510780b000b030b1441c1c02c604141003082d00c00d5041801401124101900c100004820b0090060122414a0007071003810a0381d030441e090307014034100c0020a40c200340d011404666118138840d0043c3c041d07034544c15840769004004011142290107070301942c810341d15034604403100c11410711040b03480f8403904 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 906602320 1250 906601070 906601099
    0x403020c090c070201300f0c020d080711160e0609010801021309050a0e190b060102070e150d0b01060207030c0f030c050d060f02180306161b06140403020309 69
    0x3030110342c41580c02d8a050307800c1042c1ca80044030607010410b280850b098008502610f060034520091400140003540858071801000f180800e4a244188510555008003c8948900d030005d410a40c031141c2480c12450046a068825181c0385403503450a10000cc1241c001c02d13882c1c81254442d11460b41542c0300420f590b81d541e6198202d1107008441889800c03407000600405032181c1050340c0104200102045540a8401c02d604122403d1588016695007000304010000940d50103503208400b40054140540b91a1801c0d10044c00107240301010800c404242c2d8881d5207440e08a64032a4100603414200c7da103400300a56030300b2035070100303880540d102132002654600300c5c09284150385e03110783c4c4444403d24000c1448030709203544808940c2641c85030075968140c40d50b84041c00b15a20b04d200e4105140c0c40d650185410803030054411000242c1f0781810410094100c0149018a50111a050020f200380d080a0380103016a082c0c41d01c1400c070600a002c01c8c19800030180c03044131422110400803a465 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 906603570 1250 906602320 906602329
    0x100507120c02041d0d050c010b04020c03090a141309051c090f09020f090f0d050313172a0303090301111e03101a09100c060b0d030816090810050403020c 67
    0xb00704c1000c0240d10400a503a00c080c0320310094024005501c1c000304069003441c0000301681c01c0084214041d500105507510b8901e4000c00510041085011503102e40078007a0206061164801025180b06c2e1a82d60201c2001010002558a15004400c0d903542071f9000d0340c018010360b458801d5411440c0c6060380420407400910841d880782d480c2403000e900d4003400000780300c0001c200984960b84500320501c1140400c130700b8070041c000650783c0c03081d0f07070105801c00c2d2003000c0040400c4410052907010401610007050640c0b0304900c001201c103a1040202c1450000070b155214455942d40c05500b441000b01c42401980c3c0039100c001c1c0f80c0c1d0031460701e59401007007030400c1d400300720b50461204440707000401103203940039541041c0c0011200e880b440d0400351030204040316819100340d000651074101c0720050100ca41329861465504942254118040d030324010410803000d44517000032800c44a43c1040240076880c854003c0030082c040e180b81040080d26030000740380441c3c042d005030140c4109015035207030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 906604820 1250 906603570 906603611
    0x1101081b0403020f1207240906120b0f040608071401030c1b0f12050c012a080907050d1203140f0403030e0f1606090509060f100507120c0204 62
    0x40035246034107103840c680811480310300344600306802910340000d00c00245010303c018409028100c1443c6d820a0341100203400c0c08803840c807074800300403840509000c4598010210000040c44480110b140a05000012428a030241080d60b000b8600200041c2030040070071a038046503012041c9a10382c0c0c5200340150140c0d01d42d403550100150340c000c27030003002546085c1070340c005500a40013214034403095922140c010b0340035481800030400114600044140c24013443c0b41d00c00301102c910355125000320b44041c051000c1c003a05024011036600240f2601c60401c0640e00920000313124140d0345503e810705030f21b10440d00e000c1070002070034080910b0403404030550040c001c508000c00103100b640d40342c50842c004c004101e10201c4501662480d000c8000c000c00148032803603401d40c80070b1120f929000000e04040c880c2d5002c0340c0120110003c2104540d00c0200301c000741542035900328050310001c0030407942c0307204240e401000ba15554203580d011652110400080a01c01c4e5030400c0001c0c005590042a41d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 906606070 1250 906604820 906604861
    0x110d090b0c040e0106081513140a06030c1202060c1b0111070303080109020d091403041701060b180303040b160210020f0a020f03010b090a14101d22110108 68
    0x34803c000410010f48a410f46903440300b01951800c2500d2807000001d0034200c548500030089036181c056030f1214042800400342c000c05669420800e00b441c3d071b690510850441e20030440d1a400003841102076403902c1c8111240301940c0000d0381e05a041d005401105801000380030f03400104c4035a5070341c0c9189400200d07003098a0b05915005041d031b00e4948118081e62199100b00c15090b15001d100307000425240e504025608808003540d00c0e1420a40817480c00d1000340f020440d5681495010042200c1041c100c81180078042d0000c3e034001b1084010a2842c403e039480b040c608200014014065040036960301c03440e5100721150840f0400c084822079841d20f0b1507059000382c1d08111008801860482400c000c000e80280010a0441d0444006503c2e40811260030a032a070300c03403165900b2081c8500646034440741424840c1762182c103204074030aa044be030001c2e552142c4d10300004034003802c0010030340c100f000c20350025080560b20103141c403000101410000c5400300300c411002c21000c00241020343d0050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 906607320 1250 906606070 906606089
    0x221100e010909020d0503070b0712020412140307080d060906090c020d0c061e05040506090d090e070e04051509100b0f130503030c0604051b0a1404110d090b0c04 71
    0x10703420071500b0401040614001c1340d1084d03509030020001403060028143d801d0082c900209245083c01c1c001d01040d004490018a540c8100b206100f0100d043e5503000707540c1e800c04144100190151901c610b14490b400003d003d0000124000084840e6500300d43c1c203440c404041403103929950364010040d503111220003005a008000e121a40038444c01a0840c0f49014141c082007181c401c0800019103180d42040400c00c607281c100300014000108503a68101000c14028110007003051030007003da103c1070003260020350416011600240c030600790041c0d2403600a008004078100301c41600e2503600550f11140c054440140060456058486a20103c43d0000c01d01480c01c0c01d8404941e41513480300c00004204482c0000100f00d0b43c80420151522040740d900900b80c44c1801e003481454814a0342c555220304069031f075507030131a88a0354802412120304004000c0020381402c0040c0c050f205506110000c00e0300070a1460b03030800c0c95044580501d004000c03409140d101c908000c0020721640c09020400c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 906608570 1250 906607320 906607349
    0x1630080c030f04030201061703210106020303160306260f0d050904020a12050f04140a0201020c01030903022b0905010203090f060901021906021e03070903021c06022110 74
    0x9982c0c100380c04541c018480c1c400004d0150315441c0005048896102d00c0c4810b078000300318040030007143c040b4881180f0800c0c0817038040e50302d0980003d65912004010f4808501c08980100c40f41c0c0c02034102070041c02417044650a5511b0101c0844401c0104074960f041512403101d032644089070200c0c05030240c0025940b8a441d2070f0800090001135030240c04000100184052600c01340c078524481c5038011010b0700fa011001b0300b414244141c5c3e0046014a031a80c50700074541c0a8010707030300060344030b03000d50080c240407489902c0360809a003002d940c0710080c4510200d4203162050710f800d000060020321159103c032401143c840300120390700d0180740d030001e41000011158080c47c1c900300000c1d048024052048403d1711034501d040950a0211010481d01c01d500402d0704001424402060241100d0015a903421071400000007441d106040c400079000d0b00f0309503400a00c2030681c00442d03c03607540041080d0b540b14604208600081c41031b200199482d40c0100c00301e0498240040b0020450f0702d950310601c0d030f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 906609820 1250 906608570 906608581
    0x70e09010b090d0b090a170f0d091401091202071d0a09050c1002030418090f02130209040e15100605030432030304030207051507081630080c03 63
    0x28a03500011009610085091001c0001280c120116100317004101c060704d400e04192030403012030200812007002900e01400901c0f0650240c105460700c1510800e00401c0c00d119078180a44a5001802c1c485e059508040c00c040c00e00048044100216141d03500302c4280c50f686036240c0301c0d036224581c6030b5903190f42240045500d2000b19048400c809006030159640c0301403182c00210082003101c001009a00040360810481d20254441150700d0402c0c40d042c000781a40f0303039031050400910341000344146408a030491019134241e0558086800250040080c03400c42c2185555403280d0100c405441cbd0910384c0007801e409103403c04041100d480780c542500313b4990355280d8041c4040c200d013410a4184400143e101c4a030040481c401012541c409541d076030525080007410203d50f500003500811003524410740d0310701481c3c11942c66503040010b05c2d03101c0036071404580706882c2000000d0540c40344a1003468402c01140f841c02e40c0c2c0201000c500680d5080366a003036505480803561f00b05000c1007800040c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 906611070 1250 906609820 906609839
    0xf01020733020601060f051921051302362806030311010b1011031b07080601090c020c010807050702100e010207090e03072d050a0b070e0901 62
    0x103080480a1800300c07844081c0c1128050710000381100400180c2c0100010400d06400c11809a00340607280b034041d2600011110000c618440c4014400c20000b010442002005e189100043c0a0440c41c0003488941004104860341d041d0001d0181d20411359a00b844450b41070603920301c1c00c4007150030b01c6c159400d031880d600158840f07001004080e01c90030034422169101c0c6c4d503140020400454480004e4030a046082c0100410031555200035140e1404072048040d94a000d540c29058081c3d151102281032840d00e0103096008184603000302c0c00c14416002404507005c202c0000341d40c903a03001c071031086c1c4c2d8074450031007911310320640b15002d40c10620b044c001551082e0b412544c4103a45042ca07920f058100d50100d5540101c820040c0001048020b03081c2c003660381417103140c009241a503c103000001420003100c3c1c4910503000b0040500d2007070f000d0a03444080422081c00c07403806c018070000c00c0240509081d62920103803e42200c806c4410070000d1512070180f0f2485050440150000040303a0800b2044e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 906612320 1250 906611070 906611099
    0x601060e0d0b0c090a03170315010309051203070203040b04170d050f030c090a030821010b0705030d2a0c0201020115180522140d0f0f0c06090b0903030708060f010207 73
    0x1150001d03988000480410315404600d40280e20180788150380b450444514061103270a21201410181030030f40d0754020a10001d0310072190104400c40e40c0e17030394071106420380ca1845a644900400c040c08640058038800b036407500007428040b1002e42e40032044001b400c941d58460f41d103401007901d07803e101003001001c240001e8001e5420191031981515103d840e0210f85401a0701c0b01000040d15400320b9034901140c0320114011310851200b035003011a16030f54036803240222800d040035559944e0007111404039940042c140944202c4403880c0c02c0c5503113140107103c4654410140d002d0342c2050840001c9101c050201000c0740c1000e8101a4134070020650325018010282183d4400c4d050380d207042da03c2c494505030003480f19209e540c0c0c00a2041ca0904c8060030151800b2040e82407103001c0c150050030942012a034503044580740f40c0314040702070504e4135a00511041101030301204c0020200010508000011402142a03448160855941001300a50281800b0350180140c102030401c100d40ba5003c08403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 906613570 1250 906612320 906612337
    0x9140402091e0a0807051309020f060a170c07030f030c020109080f04050f04020c21041d181c14040b0307050403020910030209181e0601060e0d0b0c 65
    0x54076040daa5000a400000440e191400364448021400040c0c500b9090351401041010007505e841d03840c00c000101c0348152820701c1003c2e903455550038011503851092408003484010302d4991901d81c3e58400030700c02c92509030700d58040c070130600201d00c4103c00d0781709481071540c4c10390f07440304c004644e2201140a05040300c1d040c0190740d00c80d0070181c001842c00001e030207400b0608600c56250703480e03c0100031040020052003400b031403040248144004000c20b141e16001101d0012001400c1c041d01d4503a41c40c03017240c1c461105816003610003a14860306801e880e0180b90400500350503000c50720851034581c03021480700d024020181549111942c010b4a0310700341c0d905155560743c2007513600da44011182e03000315100740008000040910842ca4110751041d00010000c81c4110314900315030120341d00d08006890080c0130005562084400d03030080250062040c0002045680c65080c0031042c0d0f51940280151408511950f510300c1e103505200400501c441c0d0031244280440e150b18408016980c01400c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 906614820 1250 906613570 906613579
    0x108010516032403150612020a122105031b0910120e030f07020301050f040804030803060f130615030e030315040e0a1203110c030904110903240c0a0914 67
    0x19000380810300001c0100003035005c0c00c1d5101000721141448400c44080d90015a0111071f06c05242c400f42c0c4451880320141c945800068a51080c1810078080e1104100d030480c6070030780d100e0305400840c1d03480b10285000e0440d020200001d20318600000c2c44d507009202038150464618054000c5040c890071191300702c9010030303800045501400b80100c1c1154441501c40e54442d400045040450409210340d41c2d104000714000307045800e00703994130515803040784400303400c4490100120b1025954840c40104c00c1d074009004c0038808003481070600213080544203515592114810801c0c00c50302a02404103081102800386146641d407008030742d03403940c40001281d0080c1d5240451503046500300b043c80082400f0701c540b00511910000c004003501c5180742d519880070824082030501c2000082a583d004004842c041801d405544103580d00c0e000303400d0740a506106514200c81c0c1425081c01510802d1401e5100d12001e80d039202c4030321084c0c42540c18001c0010140101048481c51464001e48907600c02403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 906616070 1250 906614820 906614861
    0xe09010b0901120f0615080103050f06010302060706020c0325060c1b0201031a0603010b0c120906071101122d140c1b01060b0c0d14031f05030a03020f06010801051603 73
    0x341c91b0032001489881c8074010030100c5005109101080011008141403034000b0281c940c15540400c0780750203416030007440e440c0c000c100e890200740c00340107603200070a2540200141d1004c3e07000c0c04882481041040e074000f403420b0b40200550b171003010000040510b00900b40d9040d80941e0045000340040004400d0f6260645494019961400011030081c070b43e40c004151110500e4007034504044401041146014041108d811241c4503d0f00390b40308503422488144d02d548035040165241800c00c500810202c0c5001080183c400010764490440e600c224080b0440340001140e40301180d01c850b51501e002a2a83c1c005110814031a00030300070300d200c2821061214031010091400d41c1c400784c000209941010844c40c41c0d140080020a03000842e07450306000c54104098821424030000e840f058582c00c5010b600d0b07941900417070f0141c00030103003d07049030f40803005418020746552481c1c1508100c0d00440740002004074050242030300808203116400c0302040c0584054008103404084000138202d800c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 906617320 1250 906616070 906616079
    0x40c290f07020f0d0809120c0a17010e0d03150501080112060905030c1b0112021c0b0103020c120301030614070e040c09091407020d02070e0c090301090c060e09010b0901120f06 77
    0x30101d109001c5c0c031401900e500c5d03811400802a8481540240c05065445100f0300b142c550f035007041c200200e8401720b1404144100f003c810324050300e80d90150a60030311501e03400c898152b03410ba0100c01060300511207140030540303072801143c200e0800e104080740245071040c1ca2011908542c41009458440c0c41100e148c04410f42d0568140100d000c04140400181c04288082d0b5800460107025100450811443c010780c03814041501c40300140e1802809555229000c05079020354119460351908000b203410011014041d031109900901049801074204070750708401c00c01b90102d150060301151504501003019100340001404001d400900300f206c0c402c400900d500091003465140c81000504075038610303001602070300e0003110a4001003190b1007940c042162880c00f940054025058071201e0341e40301d02040000307002d4640580041c0900340390500000d0340a800080d0015180002d6405254581c0d0b10403484800b402025151070220342140b0300c801411100c0d40c401c0461081c4110700260345500d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 906618570 1250 906617320 906617329
    0x1109130c020a0c080a050c060937092c120a030f0c020604061a0a030b062715010201060302130510080d0f03050a0c052709040c290f07020f 61
    0x550013500b06030032007941071081c404180701c3c070b280c04042510060314055009002c94000800c014004910011045020101140700540ca0714984083c04a10368803035262261080203003800301c2200d81000d0b9400704c40b4218002c00071004465182d2801402c0201c40800303032003607107a001100001c10155103007244c0c503005506221302d0720b00004a5004005600d45460048120359418003001100180304081800c941d0b07a103007504041d40d6201c2030421143d02c40501058050301d480e00071031400c4101c0ca503103035a641c0020000a208040346401207641001c900016400c0f15840d000294000c0c40071425480180000d80040703401ca1250950f1840c1103944194040c10103008500c1000007034000002c0c94502c5615000b5203401029032001040344a645000c0509039110760340381c500d081661035903000008482207203c00071405028002000c00d140510f0f2240c035040b017501409580c5403c0701e03415401801c072080811305281c90410058500310844c001043c160300300201c2284d0110760044480c4140c2c56 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 906619820 1250 906618570 906618593
    0x2030307080f0913092006040b390715050a0302070f0f060f14060307140a0305060709091a01090b220e090c030d08060906041113091109130c020a 64
    0x1e1381100054003140c6440c08136601c130b4210221b5030300340c0c800c0f540800243d90382c42c0480c1c0c1102c00500006a6411810480c1c1010001d45009980c4000010310b440c040c90010500e8000010303d03140540310200d8442407081035501403080f400d000281c040c45031010300b501075801400c05501810746408814500ea842c0350210301e101d0b008489454a4480090941c0224080c00d841048020846c0300a494000b0110340d44d58503d1084007d4080c49a040d000300b074484030485c0c00616000b0007581d03d40d19290a02a0240f20203128107a0b0b070074500702942800404040101100400594a4030302540c03400c00d0071081c580204144490f01c003024584800c7c508031295180c0300078002c0039400c10300361916040035070418540c200c14038003d40159030400201548042d51940c0510110f4148241d61900d00201e001020f91545c901652003000481c81c5150342080b85034070171640c8041c001e00c0043c0308540d14000303030b014144402e40c00440000d00c0310f00352801034104041e50000da2044507104a01c58403072000022 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 906621070 1250 906619820 906619849
    0x4060b010e030d0f080a09051906020403020d0606150c02030c13110d060311030606010c061a060a020604020a2c0a0b10180f030c050f0d02030f010b09090a02030307080f09 75
    0x101c11600420407181c0103c40c3c3e51b8444840035013002480031544501e0f880c0d000b2201c0c4a0070002010468508022695068030b000cae68010f0070300c9110441c2482e119000f00002d025801c80d07644013950100b6031074407407811000c403c0c2d400f030041d08060300960240550700e920120058401510740b4a11504642e009015048032082c103c000b1070180e1460600b4410592039011043c080e400c14410000140d1b00002d0700ad2459a0201c00043c8542189104003c00c4034103100c2c0541c0140000303012580e09a0004209000f58001c0f1428007020390f40708500000030101d45c1c000d20400c96484208641c804240000c00d5000b00100c1c00402c0091103040014a80c0b21032880b24004122810040032802c8850b10600c405030848058002d111429501c2e68089000b0030305c10188120b03c10b0400e00c01d5926940040d0356140c0d405000c581c600b03d006203c00d0f019104082005010745201c80000d0240303080015001c0e1401d8000d00035619040c250b8984010561001103005018881080142066100e0096114540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 906622320 1250 906621070 906621077
    0x12041809030e19030326010b07060905060708011d0601020c0f0a050306010e01030b070201060506180d020301050a1b050f1206150a0c0b010803070c091509020403060b030715050304060b010e030d 85
    0x15415881e002d0902c2400d2015505502600340a16550407441c51000b0b06540b02301030400d4803501a460240090580644000c105001b17010620640a81200a441c161102952000305104590700b505040050441d10130b401a48031802d01c0f00e942c1807114003440e00c40d0010302000b0300c2c0361b2a036010031700d440b2080e0b1258039104e24420042090180c0010200d400108520091280524103400a4400e0203000441500701c0303016040c0d00070564402c4000c040459029000748168031308616014010000303410042644a1039100d01420302d072150084440c1c80c3d220160b00d07400c001c1c40089404a2060080030030340c0214820042900410101020b006842c0040d40c5205c40f00c82c95240a0b00702e0881a40281060350081c001c80b800240100c02c1102070ba0380315840041c11403100158010440d495500906569100040c0802800030540001103200b03402d07000c40700781541da88259000000120500c0780044c0d002c0c404540000c02c29000200b000205240012180b0900400030f4141002d00030120040f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 906623570 1250 906622320 906622369
    0xc1704050f0102030a1d0d12020105040c060e030a170c1c0912020303030f0901021b1c05031b0307090914071706010f0e150c0303070212041809030e 65
    0x40e45018001044220402e10165080018001000d03200960b0a081c480c1c03c0c02501e80356081c141c84409424000a801c212481905500920064003e0100361425100d9605164020074018040ca840808568002d0002c00c00850603454002e0303809090441c60349203110030440c010b0588000c0111940ca04100d242e1400105000d0102130070704100c40c0e002d91100800d0081220240e44e02009882c1c1c003201c02c441201d91a9110722125009200b07e8440b10f8002440c00c1d0f0402440000044507a2554420314074800650000b0320256540e00040310322009030744007002c0104036a44000061500a0818200b139081140c890702c10b0310071b07514200c2c5844101d00e408002c00422030f500004106003011944034002090900e580001d01c2c50100c601a1420310892419062007a124408404104c50b098050583c40c3e41740c142c84a6100d41c001d88100740140f04403541c101c5d22550900441e4101c0f500d51000680003c2c0303051408015080115081e406e210030072500181c5074451725040070072440307a180c09140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 906624820 1250 906623570 906623579
    0x60317180306010f060c03110601060909230610030212040b060910030503161103030a020610080c01020d0e01020309180a18330c022b08060f010c1704 66
    0x30640c5028510500c2940001c0c010030a4031485840602030307175581d1030880a180e1141c101602da508107a8007010081c800c40740001707086640039900340c003a110ba4010a02c414503c0d00d5a501450201441d80960f812680010035003601d055103015141789141d04015003040b60300c40701141070f0078085406881d0000a20104161071903d011181d1340451a0480140c0c11411502d440b5a2400f4600e04800c000204422520600c0040d0184411000d0000c04484e600c4158450094940e80140d95a10721407080b04808a40c41c2004142100404010790080100740121030040303072002c0c1001003e07815070204110f4a41107450b4808101085200d01404d03480d20705041d40403004803104010440100b07001224180c0c00a20703d6103480c84154483d0a08442902181901c050b983c414402030034082841c16011019080e0041402031883e40c3d6022007244460240707045104604400f150b000014a150340081c1861030092850303500100103141c400c0b9061860ba880241155090381040d00b1044042010007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 906626070 1250 906624820 906624847
    0x118060602030a09091109121c1d01050f2701020c0307060c1101090b03100609120209190f0e0f1e030a0c05010b040c080f07020303090d1101060317 65
    0x14010040d6100540c5410416040204082010b02907010300d69102d0600000e00e00300282a00c12074500101880101403040b02d013556a00694175040341c0640a207801040d26038080d150600146250200c07044039114040011039460340714030344003500c2e0311003403050403145503147d04a8000803840082481e03001785a100064900f04000d103126100394070001c000e0284651100800441650228008528101030b00058600500c1070b004001210710210412141036030540e2200c2c1104d0050700c903035441c59225151800c94400d02e0714069000804000840d40202c0485a204800080c0c450001411451081c000082c0c0326040c80100041d881241803a400403030910590408031480441d1082200c401d8140c81d0300c0703028a620307085c103104032406d2800600c1001c1d08071f0030000d04010300421030141251000382905006070b0350700f49141d2180d000219600e0001080740e0140848031300901d540074a1810884070151f0b00c440001140d5243e500c00000160164180c6820030280c15407245c44040c10f0801c1c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 906627320 1250 906626070 906626081
    0x213021201061206092f0f2a0d080415020f070b13140d021b0a2d0b0a0e0f0310090302070902030a0618090809010c1110022103061c1a0118 61
    0x129144400c10848504543c0242240c051003100d151139121b110381d003180c032600c0e600d004a44140e80c1c000d0903150004294420b0f40540700b03910ce2400d60401c1001d140c500e000701d006200d00005c00030010801c1a000c40c2c04c02d950700b40c1c0f11300d00304250501400c4c5587c07154503039070042e91251001c1e8410002001a00c0c1c0500009a032018440d020310145440c00e000036040340d4051080450451903060008209041c252100ca400844ca00704d12a007140d681c4555001580b002041500040001070045c0052030064580e0003d008010000c040b0f615480c0441c2d0010031410000720250700c81d40c9030005085100380051032007104400c01c0010303807601e41030540c42c036a80070106058249180c00380703401c0082c140c24241e8002d40c00070303c0c040c40c4c8524503103456084d442c07141850365801500c08810303400d050307070028450300401603003540c20382802c020011040c82400161540c40d031101010790f10103140d852040c800644240514030300d035140319011100b605013050a070400f19803079603280c00c4141e034100140502c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 906628570 1250 906627320 906627401
    0xc07060f1e150e0421121109090105061612030e0a1406010501020607050d021b010f0501140406030f080d15060c0506130519020402130602030403021302120106120609 73
    0x141d401520705030b0f40c5e08003240c400a0441d4a00d1400b4003175020340c54402c1c410400503980d85036017080a038200d019207100980000c1e0050740314110480000c19103080003003d44004190388000c031602c0f04401e940d00607031402d21103841800c00d907070f0b14000e41c00d0800030030544508501800b49506030010700c401c02800d21805030001c0381958042e03810702c012954014110751180300e81810058944421340074108071440820700500207982440301c50300900c0142e9100604940d54014000d0030200e11800344029981c45220242000c4541071a55010402000c014824000c0c13903070f0009464001e1640ca00394680392030b00172000041e00c0d41d2401c0108102005155007208081c4a48410b0405565413195038000010b601c810309450303440001c0454843c1c0c1c050310307407409010007103101311601d400300250380b90031a1000f40d1041c10400c4000017041c040388219207030010844660b1403607a0038007406a40440711f08103242040e95035854005003d00c8548549900c901a0b15030380f4101484450464400400c88100b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 906629820 1250 906628570 906628589
    0x51611040f14150f090108011a19030b0c120c07030e0d1e1106030c130b0405010e310501170d090612060b0a0201051009050c07060f1e15 60
    0xc00302e03000a01603000550020419484150180d0444081505425413001150708448500000b10700b0303041c190440c0354082440710000e90501506010030244103132032030036015929080e4400b400816980200294080358003014903291960750040110008002c5810911084000c114403040540c006921003050b0320403280020490745070b0300d401c5281448843d02003a007220801c160410004481d0310847c03c03c0000707080d19224034141c0f06580095020f07554554482c03941180201d402c2c403001c4103a0f0f05440c0d040e510115080b40718001d00030701c404010403a40103420000c0c010721001380e20f80011101d00280b840003045551600292200709400f0442003c00c0d1340122801050990340401c034201191034901d020484200311a01500082286412180c80340c000081c24800a6405401c824000c80d55081c00c2c56410b0b541d8003003803048820a0b9580c100e00141040104081600b580200320b91321044180041c0d0040708011007441c0640009181c0502c0384c445d032030368106020003140280180304442 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 906631070 1250 906629820 906629831
    0x2030f070b0306060703030f0c030507030c110a06050712061203030c030b1e060702040e06090c030307080a03020a1e020a2303030105060708130308090406140d020f01051611040f 78
    0x1032075410070300000b8000c3e80240b0001c1001000e051107a0844031500c8041c00c0100100034041000801405003203030404c3c04a0f09000103902c032544243c4145543e050f80302d024000405055503402c1c0585000381c004400c01c82c00d4484d000681c0820f11038076008043c4140e100300d01610910300074060380c141c410301c0c5090525040f85401107071155003c00300c0c0002010000074411750140001101405450806908030349007810906e401c000001e6401e000d0721012007221898420f40c02016070b01d1054140051089001340711035103007940030313070007a00c42400b050030000080c199884202c030001c0c072502c11010041c0d00c800318440a201001c0501e00c5c806c081450b40711070000c00300204580d688018800d0714000c80c80007030a030040c00940780a6810000e2a52103865065560b81000300d20b90300604141c5100318541280090ba244038030034400001d000207000c219820714a48c0030405008030007014581886010011a4407460b565400c02e181c1d18031600c4161070840b803040600c002c88200c09041e41d0a82e1030078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 906632320 1250 906631070 906631079
    0x3040303050a230919080d060503030705280b090c011806020304182d0e0a120e04060911040603060b1305120c100302220f1701020c06100302030f07 65
    0xc400080c0a941c4407504030380c540c4809540503d4803c0e1510b403078960103408040f8170704000e0040003e044200300b415041c810581c85504054a078491100b00800a40c0098012100c0030038603840c134842c000c00501501c000300b08985640c41c895000312400c524540185482d0390302582c10100b103000088103990105495400c00c0d1005e503036031190b40951005190f070b04500c0946400c141d04800031a0b80c034051031601881203259801e80c041c0c030301c001403804181070a6a00906003c0094541d00c034139003010103803175040031740703030301030391041403018515800c13039204e040c00714204000c0d01504407155804000b959481c0e207003100080c1211169000705180a5041140300310901c08c004043c41503c10440700d0303284c951b02070a2820f01d482407210702103800c00c000c002d22400342034065001e0304c507111031402c003244040c6202c05010b0440180d8019600240c2005405000094203a410300190f422031500051901d80201c103c0d80c6801b50840e82c034100d11840f4501401141002d0149426401d4285c1c003c2c40000e040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 906633570 1250 906632320 906632351
    0x190c021804032106030203010608070608010603020c030301050d14010501081f050c09150c0118060b040219120b0a0308041509120303090c0506130f080f0a0f030e09010b03040303050a 80
    0x100101c01241c14020300206040c2c0740213503c80c1004550042c000c004c003503030720128280c850485102c2c1c407010031056000090070500a000b1282041d1800c2c0c0514616804c000800600c007580003000d441d0740f40034001e0107280207402d20620f40602920801004e0034035200403c912807840140004540600300020b01c19a032030b580080c0d40d0f41e10360499400c0f4200850b4050102280210310441030b0a40c01d04500102101c1e4200000b125540151014403a280e84041484140d100304015108034160020140001c0e503c111400d41c0355040c0f10002142040100780080e00100d6160415108550001010000c80d900e0820204c8040c1081c107010200c0c9141201c04001488150f0015044c1a160b11400f4200200700c501080606001415141c41c1c98500801310b8900c6058002d540303811070031040100300e00c8000644820049007410042c40d0015890f920081d00260499084050003000c2c1c4085580c0d40c0c0e441611400b0342140c840c0f003926450710342401002e803180a440c01110a10700120806001c84 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 906634820 1250 906633570 906633587
    0x90b460e03060105120316060606020111090d03031d030f040e0a0c140f040f081f020f0a030209060f04060203070323191809090506100b120903190c02180403 69
    0x1c00c81c2c003188605c24001d03100d400c5120300c01d882c14100480000320000c21000d90322040940c0c040c2c1d030003000103060006010b41c40d4803c0c0200585e1005030b40040000091003030300644507407c904208410100e85800f10301d0b1031b540140741406004d000110f4140860860251655440314001100703226100310000d01500d00140340c4265201c0c0c0c1d0740015400503c0903008102c600074170140700e018010303554502d1211303203800c1c231401150b80765040040b96400d000740038001e68844012844c4010705d441a444c5040d0025841106450340150081c800526110400750103400245000c0d000b42d9075841c0f19140c010b26400e0003112404050592584109032003074204140c03070340c171000040c4440e40c40a2110099034803880d49002c41c2700c1c414840720042941c018a401501a5900c51022201241ca0307803040701c4842c0400f40261884540c0030300944582d08610400036803c1a8600181c910f02030340302c0c015402141600000c10302062280303960030110b003004560102c4a804050080c5070504103940d00420022 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 906636070 1250 906634820 906634829
    0x230d17120a0203100513090c06030911010921050f0102390309010c030c020405090c100e09370603020f0420030603070b04030c060206010e0106090b460e030601 70
    0x2100041c0486d503060700e03605c4110f00c02c0d086000310381c400f07580749001005400381100444003040343c803400711925401507600c00e00751800c038010700c205900b03104c140394202015028203072050b104190200c507004800784000e0107041c4900d030305c0031441035950100d040c8900b0400030100c80031172481c403030b54840e80c0c0100640d030000800f40b1305980700d014542001c1341c1800120034040d600516000500103103410020756000c0c00d100a980490b0301041c61101960550031400116030080c060800080c0301250564a1441740019001958000c00b140e01890405411210388440100c0d070300c01c018401e51a01c95440a2020801c0b02c003800b10f00443c110483c001040b604000074036400101c0414481d40e01405a0000b41444d9155240c55903602c1c18181c018074a10320540700980a81000072070884008504a4141d5459441d0064602d29082d1040000d6108114026174150000c47c040b00542440d491b407929030325100c0e030f542481d0044c001054451003180c099241030003d060300c0102d041d2804940c030350444 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 906637320 1250 906636070 906636079
    0x5010c051504060b0402031503060604020408070e0c13080105100b07110111070803070503070b090111120a1d0c0109063612030f0206060307230d17120a02031005 71
    0x19265894080094400d0200495105e070010080100304402107411844103101141190030b20380765542404202d00c61802000301942116009010f0401c00000703042e00040400e569524002c12002d1020704603d00381c1160506944903810320152118000c803040c090a80c1100152504005580310012203c64080050500021103c007071801c01c0305004503002040f003001907940d10401c0340b4000340ca992204404450070072912011440080d0140f10700518180c00c0105c49180c1641e420000034070a40c0141140c40c0b031625042014085409180d042e4102040740c0014030340012180005001441c403a04150200031503030700300980c0005114400381c0f14505280d20400320300801c1807503501c401c04a0308552071084000c80b6210802d54401412201540c0b513509a90154441c50201501e030744140c402d407003e00f0b501c15040141203201b009051109a002400400d1010150342c138081140544040b1022003000880c42520700418101c1c25503200c445840c086156240000c00204254a10b000b1640107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 906638570 1250 906637320 906637363
    0x41406190b0a05090a02340f151104092009060a0507050712050f0303090c1e0a0b0a030b15180a030605010e060411070209010501030506010210050c0c0705010c05 71
    0xc0da10b629030a540036140242424a5500d41000c048029501400440b20b6504514102d0b0f9282c11920300d10808032032203a203089007550f841c0d8403103040200d26510b0903030f440003452000c0c0100c50b6003841440500d00361300000036112840c100d2400f0031030b00303000d43c0c000b629091040d0641c2c1c1c0482e142c04841d480b500c121092a251445039200b00ca5501401000404a102da4030001c500f4070700650b803038140399219108a48200c1e80d00d45002d0784030300007500e11044640c40b03000340c50100e00d080c005209801400070790380001181c20f200018200161a800095903140014900d0381155041c061101d00d85001d44496901c445c1998182c1d221f88600c020361605460040106480e0340c0c0c596441c040290342001082c025540c403010307801c0c41094140c0c2c8603131080d440d201b11300c410703400b0f54800d4030402a00100419466864000154054a00149468114003e00b91800b100c0f44c0b0501c01d03607000e541e01c501e000c0d48400c1d00208503480c1880e10b40141d410f011000c424000000c100165a00d6540144141201d8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 906639820 1250 906638570 906638591
    0x80a0e0a0209131401020318070b0403060914101506030c0203040504050702071715070c0b0402040e0715110f0613080a0306050d120e19030618050d0804140619 70
    0x10b503e1600c00000b4211805101d010b000c0c50015005940554402190121201b00558525a6405991080c6100210248820004a2095881004a0b5014820f03205e140d041d85040c084c1046002030f001900c0e01d5a8030b00c8650040c0c04000301102070103041c14100b102001d44c0c0d9020750380303014038460b0034443d0b91504001541603100f44180401880c1444051541400044075541c80f142603110141e00d00315400000362480744110a007000d0250040c07400340103600d4507003e100107041407030840c0f041072050000000b01a41c650035411541245a40e46010400c0390b0550309041564854100010341d1000041c0503405003140042d43d005075201404e0395441104080c19006840541d004560198400411006000d161402c80380407203000d540b00400c26070010b0402c40000341d01c450642100c40d5104d818030008116a00c880c1d4000441101072100b00d0442c3e44981c034001c030900e003040c000b0b80d60034140802c07c2180150072016a1030301000d00941d1800c1500360203071034014402c29644640380c58100d074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 906641070 1250 906639820 906639841
    0xb060301020c070e130b0103032d1b240e0c060705120d060305031315080103030f0c02040b1f08010e071d0105070b070809101a06030c0d05090a03080a0e0a0209 70
    0xc001686c0000c842c0c003650383d00d080291905a29450704803040301d11641c4c03018501281480104418055111094200e000c032090140c03060648204941a5180ca100000d0b140440300354460302d2417410001148042d4a071030014100402c5100c003500a1105100c0380000401c0130802c002d0006106202c1c58803498006a81c002030062139201030180c0c0400522441c02d000110640001e540340c2444900c401d00e10840100e40c600c1091002500082d01003190760b070f0403071143d0403004041d40003d002003601075005000440c407848004001131210f402d851184400360708607015500400c0c080104180c1458079107005403407421380b08176501140c82000b019800a0307004900340c800464001c81784290b01c0c034060700007500c04181690702c41c0a0b4401c0c007030581185029401030444940042140750f941205110610442d504090a981c08940c403e00044280c01181d00c2914071644182000780300381d03059810080c0c054a80039224a0003541000c0c1d00040352a070019081c44410b906540c0201c1c103540350002003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 906642320 1250 906641070 906641101
    0x4020d051f0209100809071a04080f030415020d1b021203030a1a0d03050f0f07020d0807020414010b03070e030f070e0f090d0801090b0301060506070305070b060301020c070e 76
    0x1440180100d0305001c03150055001c1d1051000640304103084264021083e24001c504903100300c40c80d84152014014a44130f13010040400ea10029010b0400d9210244681000c048845401082c0c0c40407030100007406a180e120b510b075003018000740c200c80c00034000003844000411800c03011204014203680454681e4006885180549029251241440003002c40940321404624a50340c03004283c00d138a602d410000d0050080e490b8591030b10300034000004005a030450040b84508801c28040303000075032030300f000c0c1d4100140304800a41d0341d05010b204200890750004100140e1495050050180d40502e03002ca9400078500c0c1044160a002c0000180c078040c81062070749a42d00500600080c2d02c112140013900800d080220003d0954681414560b10480e02034000001422140100324810f4164071050b4595800380000ca504c0d40c6a0001c135882d036010300e00440001c2d10001704042881070104603a03400980407802580380070401e20030550358000030701901d500e844d0804042440c00c0c031500c400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 906643570 1250 906642320 906642343
    0x171c08010603021c05190f060501270503060405060412180621111b060405030327010908120604060812090a050a120308150108010605030408070b0f061e0904020d05 72
    0x2e020510f809400c901b44508660120000603003413460700d4152030410b0003a101903c0303040c2d550380080c0c021794803514204410900714518150380c480011540351414440f03240300b94001c1c0300070070203030420303240c91305c010034101042000704981b156003c2c0200a42d85101c0c42120407910f0803001d07280c18081407900100341400c82071101c52a1a2400320707500c46000c06070103070316654200947c0c1c00c0c0a080425443c2c1d101114024101e802c03c000190321030402c00c0c4d41c00d80702c6145031904000420901340003402c444e000711064a01d00c00c00301d00c0000c18465a5102a03110f4002c0d602840582d203800310f0b855580803034000100c0403450110700e00c40d103a01c4100203070008207401800800696501d00c400d03082d5094810382030300022821000202c81072200c0c0c1d50b100384040182d40c0c50302a6840d12130100d559401c05042141c0740748c030401c0103002042d00c4520890082e54489003560701400e0860411281c1c1c2d41202014110700110110489107a4500d91802d41c81501560ed00c203140750380c0d1401904046c03a0080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 906644820 1250 906643570 906643627
    0xb1c0519060b0a03050c0f0a0e06090711060a1b1b03080603030f0d09020f0a0b04050f18040605060306130c1806081f050c030103211206171c0801060302 67
    0x810f121001a0421510409a4540786078185a005004823004d050096508101d6040d0100c6c25504101c0c00003a840780c444c1c07170181c0d424500510044c1c1402416544003413001c0c2c5030884a20a070103040b032200000c02490a00481c1c28088108a10344030300400005000d0040c0080068803a45050003181c2c80030340201c0750290740d41c0384558040300a20300100243d000d06c2c0c034500c06135080e05144040c070f13068500d200c600c0c3d42014038080130050840700134112643c000e211848800d140f51005c544140c0204c0c401c480c041058a8500280351910b4401800000350a05410040020940000310300050340c482583c0c11860391045416900641041d92101d600e6115005009042541da002c2040e4111810601030081d40c603504c040010358082800060942c02000b1028035032004504900070a812440c28240048146002e0110440b0181e80c0715070300d124640801428014801e1002c22240b082d00140301c9261802c00100070020a01401100c0a040d40006d64030b21030342d20941c00301818044282d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 906646070 1250 906644820 906644839
    0x28050417130806010603050907090e03132306130e0405030903070b030a061e0501081504020f121030120905010f0207060f032d0b1c0519060b 62
    0x1181d0807001c407141d104100c1030f4090b41c0c0c004586280729018260046a44000800b15941042c1d910300c0101031100e121242441304001418600c088034031514010481d41c040d080413460031500c80000d40700350034445403164070700304006071340301c40c2401c0e10303c050716004104410107607a07914000786984680701c16180c2c54400c411000520748680d034011031107030070031282c103118065031080740d0070100085080080e41d001c01c4030402d00255104849143e0320145032100e142c54a490b10021a0480c1d02100092580150005840c505d0403110141b01d07030004114240c07041c181c0d14085280341c01ca450006160074500a5180b5400200f0300a62810192504400008007050703109401030001c1080344266408213660b4481c0305460f070300102c0c1c4041242d07015120b10000101c07441084006042c40024000f18050b181039400e003400e24032a2510094440e0f20000410345134400801142c40d400784544805801440d100100180c0c000c210400a40342035008149800d0700c0d4a000000780c915130040035080312011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 906647320 1250 906646070 906646087
    0x2c010509131a040b16051e0d020706090302030c01110c030313230c0108070827010e061009050f07020d0f050d051e0a1401050f01050408032128050417 66
    0xc0d01c240d4090300c2c14003010034100c1c10060003036031b40740151441e402681141004c01680c10034101c00400d1824a01c01006280c036000d80d503a401180d08608040d00180d0002c161700070301d510b09100f218001032041140d00d0618100c505045d50320710004000d01040e06140160b0320030003400800f43e070320b0000300340d420291419220070159580d00b464280980010120404079651601582c0d407103004050728446070140310311494501e90480349078030b04000c0c0c542d0f030741106604c40801804298028040801c007908040d1600100038103441c0e005c0e1a41c05404003880900200980004440c09071207440d00b031601e490000c0340e500f42d80c40d014564039803200034101010814a40c60140c0c1172240030500910b502020340300c9015030b10450701c2d2400d840280e114800e0040c0203e1174803000d883c03410700051400c54601500c85242c507003950407003055500041b9000dd040361072480000381859104410704c0041d00c000c10340851000d84141034122145a45a07200040341c1401007500108201c1c8400b06d846a50340e0b010b1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 906648570 1250 906647320 906647333
    0x106090b040b0f212202030a0b04020f040f050f070201060e280507080402030d0e0a1412010c110c010c080a050c0a060c050d0614010e0603150a2c010509131a04 70
    0x1159600b61048200f800c0c0541c1780180c542e4049420340160003402543d40da030759030b09900c000140059902171303000c0b402c001d4296280d014060400362012400306550400700b00f024074504000e0000029a4105603081c0411038210304501c0d8001d180d800008080c0b04000c0c28002c126141e5003107020510b0900701007110558011402c44e000d648203400f114460b50454408403446605c12441e135034004a071440412504901045c0c41c088a02c009044603100e0007007000c420b00312102070038400c0c0810021032805150100c184601d500594080c00c00e4020500c007551403901034800c10b407040051120100c1d50200f5244100407104040340e01500130481c1924074100038185030002c50300c3c0003110f07040c00d0000c2030400c40c1741404014450180c541400b1080401d04000c2d03140c00060144844002e05240d8040d41d9842100b07201c000c01c00c81d080441108003107800e204100854040710350075800e0384001040310307494610b0401c4e4030031601c20340810340f02c0c054540988140e045a5140f504050020140800e1055 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 906649820 1250 906648570 906648637
    0x1009020415121b0e0f030a0f02030f0d050f03150a03320307020f031011070c21121b23120d02030411030307060e01050106090b040b0f 59
    0x10a40703804409049000904060350000d032480000f00010703d181c03841060143c8580000e00800078551400900e801e00444d10303042006134207483c5070710760000c0c21023507090501101c198000d801000c0d080a0403800c40281c11445402025100104004005207105000015001e64078000815001c141696800c200030017191100180c841401e60140b04207072142d40007090703507403003024030065410190fa540810485010fa15030780d5415000383d08060341d0600a51040200300e10f0300003960f9885e00118100280c1307807412900039603070b002250040e0490001c028034001110a80c8449a041d050f054400121111968074881400440392060000108441c040300701c8020707454000d441c020003010346000d030355506a0300300003034200d40c0802074002d40c00c0aa40003180c2c854092054043c4540c2100042440c40e84400010ba42d4940d4179103c0500351407085c051940101498a0036503130160800c040401c603441240700b012141400094030401610070070090b21141035203020210040076040c80344104448 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 906651070 1250 906649820 906649859
    0xc0910080d0f020613170702010e0d060204140105040e0f0a1b2a170f1c020702040b0306060a170f0616020706020111030f04060902060c01020406030501290310090204 73
    0x9844d00040001812000c221840d0f504480d00c030000d00100c00c801d0107660b001a0003a41001680da08100700c3d51100d21030019260300c5458010390f904d10b05440f4641c44011481981d040150821003004070110302089540c2200c1c041281d020b031901d406201100800760603c034100b000342800407800c3d0541e084170800e003004c0c00310201800ca00c040041c0f003641c0800c040c00010144d0034802400c410704914000070304401d0000141151508828805a50450a4220900d0003158000030b00204504250040c030008000130b80c0280000c2c145040016484219030040e40ba05a066002d001380c000e0f81000300c48048840041910080c1c1003203450000c088500c4140040984251240000e480c1d1051143e641454841c0403c0c0d415922418003000720024054401e4881580b42c8400101607514503005207207040c1850001070b52240380c0200503085d118160b0203450f480d00c15080d80800d04851f44030600503100000d202581d070381d0302c140e10308015560b0b5400c49040c0510102e404180401c580c804040c402 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 906652320 1250 906651070 906651073
    0x3011b0e010e060f0f130e0f01210201020717100509070312020c0904020103020c031c0219021b010c0507150c150b03100c03061805010603050708090c0910080d0f02 72
    0x10209024410035204d40552064840701c10840e8901c0640154050030f004540b02c00500c4607950303180441020030302c0940391000b01c084080d004115015050942c403024006c2c0064161500f441500080e455104610900c40c0503d0f0b03036901c10708144424003000c0383c00b00025500f003065003844048641d441c0140e0000301d4884c3c0c9100701c1c21044034000211a00300040040880714980d03500da004401940200d503941d8070910041c4581030888258031504000b034032500c580140c8071003440b000d551080540d0b000e40000d5400c5a92580a100c40e0040c281c3d010480a080001820300c10789030030703890460158004004031242036014402c0c164010403251a0b140581800004d403030185506900729000e0341041c2d641135122007030805001c1e01d540c200a5600c180b500340029101d50390451145000c00301541d221107580e9690040c00100c1d094030881d034012403d0300e00080d96150a1900f40d613107011100e5040d2084851a00281d1102c4446039080050720321031054a140390309040d80035061034290310b40000907 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 906653570 1250 906652320 906652337
    0x3120703141305210d0315141804050a0b090a111804021216091401140d142406010e01110d050d110c0a030201050a09020f0f03011b0e01 60
    0x4260818041d182d080b000644400d605500d40010410000504005030f0904504040c825900000074804283c04c02e036103031000f0560100300c4000450303030324298200750440411000c2c095001d450b04080400b416211504045031034885003007640c58120060402010401d80001700407005801003145642c0703038400c008040040001e40c0800c521a1684101100b8000800380010b0148c5030000c0160744004141040e40e0503006045104510101c6941202a40f80c0d02d40c4291018500114031540c01400c0f561801004400300314001514043c40600241c8120b090020540c021501030003207c40500292216540b01ba20180709a402c3d00021200c05021460501100700c030344d40180c2c500408046a4005840300d960240310030303101c80d004551204151a0344d404070211242160009050f070401d410028a8100c0e01460000c0c01c0d558020003c860b140d041c01d00350001030700c4809600903803400460b501083c0a291f040400d00402c000503208442d12000c01e4001000da4001e03107004044d00081e40d982c1c0c0d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 906654676 1106 906653570 906653597
    0x210108150f1e07050a02060a05010807030f150c031a0307030302030904020a02191a011a0d090f02040510230307030201030b01090902031f0501020d020c0907030b03120703 75
    0x1c50700010341c2d169030706e80401c01107502952100051200350b041c034564030740701c1006d840007d0003c00140908407c000b030b01c4802900150348102e0410095524100040c00f8200c1d2030002100106040c541342220f0070041460400d81e60175800071441d100b14442403000079800140004114080e020100030852940c04d040c6249074040c2d1110010141268861010404181d11080e101c0840b0000001980800030039070700c55025101e0000f074041c07041e0030301c1e00480d00d280c1002075019240404000500c2058070a81080d17840071030700c9502e4007207208508010740c854600b100e03503d903101110420056200f500b01207803100042c50f1490882d640c031035580040e80c00643d1442403884940a41403400c1c80030904c03110045c102440100382100300420f0180d114640600c405005d0b03c001c2c0e00141605000380c10507294050090111041100f40800c1c0e01e00907044401c04400281d840000b010 = true := by decide +kernel

theorem cover : BRFrame.Cov 906474820 906654676 := by
  have h0 := BRFrame.cov_init 906474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 906474820 ≤ n) (h2 : n < 906654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
