-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1760
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:34:40.75891+00:00
-- url     : https://prove2.me/submissions/9858ec29-8029-445e-8c46-4ce96bc949a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 316366906 ≤ n < 316546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 316368156 1250 316366906 316366913
    0x30207050c22061a070f1b0f050109080f0c010f020309090f1015020a02010f030f0f09021e0f0f01270302130902100e030c100302210108060a1104050d030c 68
    0x81e2000030714100b0701000d920b00c80c040c0855924080e01780050b10f0200c0c45001ea50070042c0a003848201140d10424052032035848004111120a02e805403a01007002540b0200324030b13000240c0130540064580c02480d910501600440324140035803000b1003584000c0c45080402c0d0744011010703100d6131101400201034500665000308041c0684d00800d401e034050846021003e0380070520080d00340e0282481a03640804c460304038001c2888001109080b4030308501c0756891581ca4010b042d2890080781d0895220308c0e1500045000440780456541c010f01d40b012080060030314070070b00c2003000c005040848807210451b0001a105007448405502c080d074900d414021031400840b4410180303a00351007080805034660200b501030009030143d10a11200303460006007030343c0420040c141c0c44405005003c40102c1c0a5011307003e50000a60040300c0d41d200c002e9401c0703250803854402d040300c110030001e240070b40301c0c2c40f5080002c0000c69012003140c2c004003c0891282ca480b500a06000c4c07190340c1e9544008100e05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 316369406 1250 316368156 316368161
    0xf1121010e06011202010c2d0b040501060b090a0608092404050601122d080d02070c05030c01050906220611010e0624060d0f0207120804020907030207050c22 69
    0xb044618010301c0018884c01503644100111420f40e0b005800021240601c000c0401602600132004104041403451004024030241103034040c0b4401d000034050b2300e40b03590841c0181d004105a85c0d4001e040c0c11420030425128290058100241e01c0030b443ca00240182c040a01d40c545925001c010310120041c00308119013080440d00503d800807548550b012140c1c0c455600600d1407045082c00c02c02c4100034220108044038080d6000e81c00800750350303102a800c540001075000300710256a00c841c1c00d1800200341c1004236200942c10f0059540514050881b400c21001e038100000200b0180030710110040b0700c10140f010300c00a40211b4485860900b2240c102e2425604000f40003810341e0410130174045040307801c10000c02459802450a50072121510200c0c084d030050b003c01c544114204003041406032034690003017a0f424000d466003d402078540300c05881c05182524001d420044d40c2c03001031900e612a03405449918880c50aa4001480311000a94803040001d101d444110a2445c9070000400e42c0c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 316370656 1250 316369406 316369409
    0x4090501050126030d0b030312040510180231020d0f0c02010b030607051c1b020c1005040e0c0904050f091e030f0c030c100609050c03040f1121010e0601 67
    0x15440c020020f9903980664803070280e40c0428a04a03103d90740444180d4007801510a2803101110fa41101e1038117041184d80c1c1c0c16582c446100c07607031400030380e03008544c4103218044101d0740241c581a00915100c0c04500a0600100c480c1c1108501c0100110102c0e450300060008840071400815100e8594541c00c085580f02071490303003903a161002002c0b190300c005c51000c0c0d0080850800c80d480340d002d9a1a0f400d069003400380c4010784c81c9003402348443c00420004c01a90651a58202d6501c13100c01c0341400005241000f4000205109100420004200401496001940d4840c650611100b48085401d0340c40558031410b90300b6100c001c1244400041210101c83c443c4020210080300341500c00540b244547c00407049c1e0300000140c03800f0503c004000300c410134843c0e2000c503402c051000a43c400200804c0c090010200c0c280800300d00700c0f081c26001d0300e000340d410030009417400704540d442011316603000c003e058128001c0703c040e2145503040400403412a410400200744040c1c821805400c10605 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 316371906 1250 316370656 316370699
    0x30a03020301060e0f090703050603010f060305010905160803040e040507050d03020a110303130302090916060917030f04060509130c1112031e04060912050a02010b040b2805040905010501 82
    0x1003480b49221391b10008140e80161480c1070000c0c2075101d03040031a015018032044079582c01e00303007000081003040544c0701d4032500f401a801d503100182441c2411038285402e2140359070b580c0c0284020b000c44080502d019420600c1207045900c45035640300800c81082d1440826805070700500c518200b4004000900c0149040440c040c61910303e580003c000c2030700090102034080d990610004002d80010070008807400304851503807030303029680c1000610085050040860041d86c0700c148030903c08002050360182a5002012401c160403ea01120380b5000b19401542c451654000080240403038800c91258040d26a90000121034465020f07180541203226454801030400800800002c1e0500c6001c11050200f401c482c1901d503400c0480107402951000340000080d0f0a5900715140c00074010f002d40d8800f0303002403101440d05e02c10031084541c1111500c0d000080302190002e1000002a039002c0c070b6040803d4010752a450703402084c21610400e030100c4807691b564005010714060b075099003484084 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 316373156 1250 316371906 316371919
    0x909040b0f090a020916030e2b020105040f020607020d0b0a0209120307050607230f090f0f010c0b1e01080a1406040f02040c090825080a050a110111030a03020301060e 73
    0xf030b54041051441c00130200300001d40c00181102001d4469005140c6040b03c81c4212901b20072445401031081040c580301c0740c0c58000502d600111345006004952003683c1041245549100c15000d21402d07601c54034080360300c510890203103400201c40951541c060040384a0050b2180d41d0507062081c01060500d149007503500c00d01041002520005d84180d000d01c4501c0d00c02100c0d480214143d509105946004d008004003040030f0304000f080b8009041500340450f403c000450710b51080c48142c1e403001c5003c078002141d04407035501040400c00416000041c1100316a403042c685441d42c00031074400e812030036043e080b440341c207c14001207545003089101c0701409802d09050a9851500040088200030300550b00c400c0c1034901c0c1d034050400300000385801c40540e1032584c043c0540c0644c4600300c0100b10b2074600c3c04030700842c2902c0e000170207180a83d070110050600300d802c0d4030341c840401518080da60420090441101249805101505d03260034940c0300903840f541007100140c055406048542d00405 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 316374406 1250 316373156 316373173
    0xc0d0206060409150f110d02030609010b0304030804020f1f0909050703020307020d031808030705070b0108031c0b04110403050d020c0904030914151605011a0d021002030909040b0f09 80
    0x40e605000c400c088051201d0020f001c17078000b261000508800303542054941408030f01610000800c0c1c00952084d5000c6034407041036a03c510900c6440e02043d50040c0010308104000790050411248820380b422005004050104d21a240c111b5100c0c5240120000101c403004108541d0074540210350300511542800e50840c03420410080d81c07244020003000030103407101d0480428001e03e402c440311040e04121503135941d1070820310140c01a4040541142c46118030000054601004001ea5403c1c142c1c1d40c040c2d401080800381428003500704142c00a6026079180448201e12110200400080d07210308050b2072050300810000e8280364200d20030718043c12005040000003540310f11840140c0b4108640d00000c0c04401001c52081201c051078405215000690402592503a0150442c0c2d50b100da0004c1c458600486008514403000d003d0440d04295242c0c3c1d003030014501009030000e080704905c112401c000c4010300040710950281c0f01078900105090510a505a0700f50280d90b00020030001841c225 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 316375656 1250 316374406 316374413
    0x10501030308040f0804320a0503070b090a080a030c022407030807022d0c01020a0b0f13060510030201030c050c150603010b0d0606060215190c140c0d0206060409 71
    0xb0000510003000c842c040c49841040040340300c162030140c208101c0440c01015581410358a0052a1200c03a00540c9400022400c0f45801c40800083e50b10140140400701d2500d82540030355080f00e4032944d40051301020100b0f000904010988000c0c3c081e0759103518400b041e00501c2031112307450a00c400b81700d42c0d82c1802c80c039100d8498100e545040c1d140c07400380456034407001c0813401c1c01410001c4038103410400c4010803016540c1540c81c4180d10405059a00403100300c00166900c075008a00100000d0307520740001c2d4410005502c443d40702e0001c840006804d030301640c40c40c040740e03821503007400f0103540c291041c415035074944039508010322103051180c80c00008000c0366540c1c0542c2d180da40d0306540c00c1d400154a5403403e40102816039030250202c040d15105140000240c4000d0142c80018811214030301400305806080d18081c60b0500545104494256050805080c0d020029410f00101912120942c006c007401001c00a0180014041e044002000203050901c05400304e40301f14240300002012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 316376906 1250 316375656 316375667
    0x6150316050f090301090302070503060115211e0e10060303081504270614060a1203050f03040f12050c0c09040c030c0803130501032721051b0105010303 67
    0x144001d040541e140c0031144101142441a60180b42d019420102800205030300012081d0954200b20240c41440e81c8400442c544c2145a02c12900003c41003840021184a16114440e181c00300100218180e4105040100340c0d180300c2c1d0148007220340e00c02e10401c864500b80300c115803a001d1548240300e0a80365490080404c400504400549a004c1d2180000c1d0381e030710390108090b8035610700c0740c3d0008501914813400c1040c0c0d001090b28110306000d030404c08907200d1030883d40300c1c4400401e0f404c00c0d681048100c0c1d8030070380c016400b10144181004108008110040514801d920034500c03003c1c1400c541c68280c0c45c0610841c058820300c03900344100349044402007092288668180c4840309240d4a6013860200b031020744d031015104043c1c116001c40e810034044014110110318080c040074503681d032001101203540c040030001501c1c0740512682c00102c0e4014411040c10b0281907032000340201d010085420000080c0c2510224030b0010389a509170b80740c0104442d1140600c80200115131441c0c074007404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 316378156 1250 316376906 316376941
    0x21b01120506040e0d030c0305010806071709070504020d270b01092c0105011505190e13061502070b0f03060103021b0303040c05090112050d05030703061d061503 71
    0x10110740703400016842c1c2e12144e0202d8030207a40081200c130071201200000d00208035841c0c180d80001e0400340045040e980001d1420300640c400c0d51440440d409184024a124801401c41281d03809410350004032030b9520f002904907200c1c400da0000d01116000d40442101c00041c01c0c200323001c1d0b070350390340c01c400b0408030401541100da40700000301d06503119040c00034402606032180c0b101c204100c5481841c1c4401540254140d511616178889605444034082c0d4a50081d41d0000700c0f07854440010445e018400c5400c410f0312130024042c00302207556149020b00362a242c0d00141c640c4600c007444001142d90401c56440106210202241703802440700d0050283d10004100e1030506400007800442c6c0c11240304541000c081c40000c4e0390312410140b80040045866100d0030b44245810400400e01e100501c820348019a402070080440d445580026241500010882c00074140d40d4030300011155949501c600c81c404000904130301341d00d441d00403ca03400d41b6180403c0380c801000d00400404001c1e8009004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 316379406 1250 316378156 316378187
    0xb010315050a2009040e0102040f090518030702040b120d03140c160209060d140a03030605041103040318051002010516030902010c17070c1404050f130212071d07021b01 74
    0x21341e10020440414050071900c9000d240e1580300140010311000181680d0082e1861140b0034400360710f54840780e841074900103080c2065504100054170041c5425031120080c04005408048006407030850241004440584140072a0325144001c1c0300320011088203900580c0241200d0030900264540820228901d000a00407000c20020444660300d29a010801c5540319040d0481912120000e5071581488201140400c1c10441c01248a00d0725025944d00301d4a8481c00a003599940d45046410314800004008050f02c00103000c100e507103942c6c1100a188001d6000031581d8109185001c608800b90f100340820103143c0501080181c0e0f01520088c01c454001288a0a58450f810a1030b01071040300d00080c040c002c01c0c0c1d030000d0950300104000729460f02c121002c00c070703d58a92a50071240c2c481150342400b180306018640c4010301e00341400d206d0941260049a42460326111001e001c411102c1071560248002403c0150741503040002200b07100710003001d05080f203d00c90000c2c00c911002d5aa28 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 316380656 1250 316379406 316379471
    0x6050403020603150603040f05011401030b061003090203060a020a090b040501080c180a12060b040501032d3011030316030212072006012306070b010315050a 69
    0x996000302400d40c800400400900d0340d507032400c281c90242200b02d10508d003100c003542880d24000c0e122444202040c1240e4001e4031803005c0b03075101c80800074418500034041080c15130380c400030802750301d0800801e407080f803151343c1c0103035103684030130024101c2d1049a0191180311810401401580d910503555500b041c1c901016948950100c8405030243e80150a11a0800100d010000c1c90800314108258024011001003007200e0000c010b1000740c034801d001c09010038404c481441910f0801c44042036040e507280e100e03000703105503c3d92007540c0c4105200c440d010810070400d10203c4070106100d188080c41003030400503040815040085d03280e00000380520403217800940005802da00031780440369103405200e421003c03454520303070151a1940503003000c0c10140d91441c0b00103501c440090700f28180c5c4c102082080ba852403450103c81106113140e034444e0016024481e8000042d200d000e02800f8512a1203c1060340380030102e884202c4400800b909144d90810210b030b0a456420801405401d02e5034055 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 316381906 1250 316380656 316380661
    0x9010f0605100c1703040c0306050f15010f140d050a0b1c020108040f0210033204060504020105040302030a0f060506042309070f06050705070f05181b0c0604050f060106050403020603 80
    0x350b00e008440c444004c1c0c016800004000030020305420260540e840b8110070015511100e0821022840840d05090a10780d00d140b03d580a41c01803840ca03500e2403452511310303511a661404114180c02081030301c1c03805501c4006001c10540540960003807410300740c81c0c0d070000101410209445405110010b13050001000201e41030110340c0862041c81a0041e2041030080b90380f100060040020b2000075940c5c080c441d03a07021480b1209211035200300c081501c081d15175129a01d03060010300c03005d4800c03030520108100010043c0c0b024416030b0760460181482e03000421990500c0410b031180204014443d900e020504041403982142c106281c1c000e10300029800d94640c103035545002000c0c0c001e050f115081c105d000a01c160705c9002840414421302c01e456401d551660082e1001c22513010b0943c0c400041102240e068403030f0800300c0e0f40024004028048207410426128107907000b8980f110041d0440010002440410861404003030b1841005042c15071407c0c1004025000354000240705a000101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 316383156 1250 316381906 316381913
    0x9010302090418030f0f0f1b0615030c0b033102061b070b030c04050d05010906051303030e0f07090b01020f0f1507020c0a0b1c05070809010f0605100c 66
    0x40d10344500019204104004000c1d04036105407400180450016a2a40c00030346414840c2c950710307041c40c11640f1031289032007281c0c0701620300c0100708941c0455400d08c6050040441c0090050700030408048642102e842d045051040c00c409407508071221868080050140a1020324040c00086c01d50305400e09188070790004424442c000762101a40c03082021071a12207a510300c040845140c52100111540c85a4035009090f140c00300316043c511004003448100084e080c003030fa107005610310400000500300c00790341e00c2d0022144195405440c3d0000b0031920001c15406200f00703600d440208000b00340c0400102501f0b0368540050283d900c1460721552418050b074020080c0c0403162000d00281c42c02c1072240440d5a40d1184040041013110480e400071541d0b45001154404092001814854007139083c448100e50344d42c006044080c501103003101e1109560400d109240c0248410390b500c0c1e2160815201003403c2d039041c49100c03884507290540401c0b6030703624176640b49040c503201e081019081e5041d04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 316384406 1250 316383156 316383161
    0x2030a120f1407090905040b011208070c0b09040c0c050c0f120709020901031805191a1302150c0601030b0c040e0109090203011a031005091603150b0303070314090103 73
    0x19a089903900300b80c020760414003100720b8103200720041d507194441c0c2039032440a0020344406503009040f03110a0001444042c0006040c02e02940c0a41d0070f0a20380f4205a80e800b60000543d1301800000c02c0c00300c0c8103020740c43c150080c15000544c501e00012109203d031900350326150401c6045100714021821240a03844a0140da00d004000c682503500c1c2c07944d01c51203d03006e136011014203800640b5041c001001d0100c800d21000400350046d0080040d100c0011a10100d8091814213031101c070f070752100c584502c100400200748142c1080308002c01c1b507411441809015454082ca000c0d0b403900500080c040110f00040c154112900030826440c10303101c504400a2034403668101000c1c5040351800419026603503000400c20602c2900204407440802c903e080c47c592000d00c80580c503030401288508100016004550400f6000d420b58084490481c00004400301d2640300700e809041008841880d0f01542c40b03004c1001c04240e02440c81c182c0c0568004162403240e101c0c003404888017044103070712a4408d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 316385656 1250 316384406 316384421
    0x3061112270a030503090c120d051810020d0206090d120b06091f0e04090305090915030106120c0812070215041d0405100c05030c0903011e0c080a0b0102030a12 70
    0xc5098410142031801c004002c0d0f801141d071b0b200035209140c0209054105250012446079100015007580d207111803088480e42e008540c001110003280c88010352580d14405602c030a500660020840d00d058060042c2c10503034020100100780c0c1010a0310800290030448502d200000d1400000321612100d001800354081e00c14000d80205051017561521609000c008048aa00e62200302080a012040005480100c00020006034041c0039400302401d018110030340103850f1821049800300541d0200c0c1c2124090380c000c408400100e40d840c018031485001c0c0002800c01013000d8a01e981604044404a1080c6c101c001e00400f2903003520300f454010801038034050200018110f02c4081c40000083c14000151810b5950b80516150107800e66140c1c07081002d84103a680359582550344600c001ca10940290350f0064240d501c8440c001003501244031103480d0300ea10410002600003a811004000080084c1700a2019103040349100e2a6030b000800e8543e0198a0301d800030500c000300720b00c0c10203001e88 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 316386906 1250 316385656 316385731
    0x20a0501150501020f01020c0c040c030f09112817160b1306050703080609090118080307080f01030b0f0411060d0603050d03020f03010b07050f030a0903061112 70
    0x24000c11030340065281c0508011200c0036400c85804200866145080348101e803c5c0807540c0d40f00b40c80010090611760082034136107115050000310612000c500078155041e441089403100740b03140d11a050703413400150712108001159030108420419021291054900340030741c01c0c86001e400c0011400c12010000e0120040c184242469a1544c2c0c840c0740f480c0b50080c031401c4055024000c80406c0d414401e006079003980760540d0360600c4580310041480b9002030081c080d00403a54882c40003c6003a12021940c502c0300348a8200701e5560700e040d00d030003802700502501c0301c0c006c42e0701c00b401000410b8038100c2c1c48d508110440004407842c2c445150090002d080c3c0c00940d50011030200e980703050510198000c9045a0044056480d1400c4410046080b40b040c01442604407009200512403442110090f16805109404442801b00c2c040036881c0b440e080016643c000521a00b03041c0b00300125401050340071621107a483c1c0c00c1a66400f01049074950040807100391f65070700141040020b011040840d4100744c13 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 316388156 1250 316386906 316386911
    0x307020d0507030c091b0809011112100f050306040b0601120e060f0703060602030412060b0306040b24010c0b1015030c0206090a02060906031f1502010b0f010f030c020a0501 76
    0x1440c206840b90700c10320003603c08016440b0b000a464200d0f006c0c5441903c05051060488200110291480c1c44068030b5402d11759a0364404003242c280c20380c0103084206c01c2d05112813042c6041d5881c2c002981c0c01d90405043c100246500300f00980b00080c0740c030b03040780d4031a10361001aa190b0340100d410080c01889004914140003601c0341d011404600f080c002c44075070100c40260f9858100980950320240b045200583c0200300411032204120154400288a1040800e03070040640002c2d14190b01500c0c19140c00d0742030414004011141207080e40b108244070404d01c5965844d6002038040006a0000b07804822aa1700194262520022a001605840e0109440c0704454880100100910075504000d84510804201224000980c0710071182d801408185410915400d2100e43d401c00b0342040040d01000b101d17030540607d080c12081c040e01202c06044880c001c0520b0080c01d49892309003040c007444454103480703443d0f40c1c081440380f03c40800c0d00300845d80c00ad070900f049207080f1070032034054542d51 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 316389406 1250 316388156 316388179
    0x7030e06071a250e0604091409070f030816060b030601080607030621030c0515040303021312020109030204023108010615021b010e030a0506010504151a0705030702 72
    0x4a801d188440040255031180c001c0d500e6000f0281024420081ca0082045100c80d40302c0040c03007540c00000c200700c0034004600b0943d80e40404001d6882d03080c04541003008080802032980c0c820491040280100d4100c01c070350074550789a4041d14480d01d000c1c1c480b46c40003854008140505a00b14403450600a02101c038151380d43c00c40b29884120a4800d00006403c2940000d007545201c00d55000c0b10405030380c560510140da80d010b98410020b031200300d561b030150b1075803201c1102d00300140310f03c15030080d203016a80e001d264440600c421100e40085c080000004040c0d40540da202c941e86081d25030540f80140d48080c0b021110030b118250b01d022101068140315455480134240451004481f00e0344000c2c080740381c0740c1d0750100d10021884407660040c1e01503e810b0004080b5210004038404040c181007450701c00d4100480d00304081e13040c05441550000e030040003142407074865110410401425007090030705240705020701c1d00b03000c6850301140d0300110700441807180502c00c490308560300604003803940 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 316390656 1250 316389406 316389413
    0xa0e0a0f15020a0206131e0302030c060f09030d0c02010b0d080d05010803030f04060b01140d1a01021606031104170a1103011107230102031807090e06010b07030e0607 73
    0x40610100448680004010003503030700ca03440c020f56400f465203401412840d1341c0c0404c440d070070030f462003402e80d410381c401c005800361081e000d03041a1210380280e004d503503600610340c0001e10340b01c000381c42403104118407010483c200c000401964050401d4007408905146202022402362071006495036000700c00d1400501081180b400400d0806140f031020b0015a13a28a1240d031280412035502d211942800c0000c0c001603456481045268414100031076151403400c41464140c005051061a85540c0c1c1c00001b414038a0300d81005020000b44018880c100b10714400c4582c40c1618071662040c07644880003e00070903541000da40c050b00080c81800e0384050a03034402130b92008a814180d410081e009070401075403e040c011400b04008001c00b2030300d4038513641e4807819000083d150207206481d0070b009040c8006004c3c002903001c5c00c04070025185030604079810700c0c01d20000f68482ca400614041d100303c0190350200744141142e05559036503031a1703580c40c141500d01d01008144541d10150000300c06080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 316391906 1250 316390656 316390673
    0x317040302010e04050103031b061107030c0519170d0212130b0703090f0b0606070b0702061b0705060a050601020f0d020d030c050711130e030c0a02030c090705040506030a0e0a 77
    0x803603000341d0311425030350b0502c0d06000c1191020300020f00041c0c1c01c003002d003401d45034115200c02c001e071145000080710349001860b001c241d0400d000c00c5000842400b21f0701c0a100707040002500c4090100401e0002e4130096a5001d00302c5032103c0121110000400e120b02c1c03100550741600e114800481102d915860f2059046c40300000700c400c22900c0c4881540030452040c070910840c003903107512443c0f10121094070340340e604094400402080d4440c0b802c01011000914080700c890103030f03519800611440c2800103a98900414905a49884010501c048030100790001038280c0c000f46007810000d080d494000c0101d06001e81454560701c07a108000c0303100350b602d900240c546001502590108032115050804480a104241c80a09810360b10700400c2c90034075022046400355000030030001164003842c00c40340e086030464140c0c1a5250000c1d14000250300303090126100b80001186c980c0e100b8074011801820b540540d0050a00900340071001913080c150f03e50041c6d684200000841c0c40780889881d000d50b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 316393156 1250 316391906 316391909
    0xe010504081b070b04060507080c1b090c1608091810030506010e060d032f03090406060806010206072a080912010c05040603050c0714070e0606030f070513031704 71
    0x2000303103180d907101c0d900c05000c901141aa1416050301e81703820310706241220103402100c0e0a48080740208000e214a4004210050502c2c148600c0d06407810400010000400401001140614030401440d031000c010340d5038007141d255000138441e489600c0440030502081148a42002155085042c0080012295002021280300b4011195580c2c2c841c4501c55402d41c0a40f5004d4005c2130355450704c1d00007070003035902030058409050440d590303913490b1f03e80069440301c02d102000c0d13036040042c12180c542800c4c040d8502800e8a0b0a022409090010000b940d074a001001201049402020f05044e01204521404201c0c040c80c0202d130380b1000c1307003400b01065110054283c882c03d005144000d5018060050300e880001c2925075604041c5031074019000743c14000d20454001c90304010200010740c181542004036000e02005040f13650031303c40c0400c075055002c1c0040c0e00c20081401000f80c500d440c3c107001c9034841010300c0d0550300c50384d008000002c80d400ca604001c0010f900085011319940c1500d01800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 316394406 1250 316393156 316393177
    0x807050613120b18150402100e0411090102010b030601050f06030703020403020301050709140a0302060f1c02040311130603210e03150915040503030604110c0109080301030303060e0906010312030e01050408 90
    0xb84e40f8403001076081e943e6440002d454918510b40340041c015240600100404200900300f0b10702c10000e2400040c202d65115a002040c82d8004c42c1e205050b5178244245040f00400368018244c5504050008100c2c01030380c1c8200344216000000100201d102c0c1d0160742c0215805402445035050568002d0f1005001b4007920044140c5403404407031524182d426501165000391a507807402d030381c0103d07041560f405051000791040007000e12500c3c0c0c1d007071880280002e60264900ea44688181420020300c0c0760403102d03040c061403d0030380038400300d040b403608451421203207006008004030700301c0141ca000c44015030103a410301500f94540300c400340450050b8030501419090702c40302200d4401c000d00c484804d4034080c040d944284006042800d06901515400f625100014103000025200d20709440c0300388001c0324261804001002096007500484014040d04100c15503d46002440e0a03a11a414400a4100340ca04040395101c00c0c0240d1040159400f407000030b000d0b0b860582801d400715408401c019 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 316395656 1250 316394406 316394431
    0x80703140a05091f08061021020415020a03050a03180b0f06130903080103110a0312031416050d050714040611120306010903121e1101060603060807050613120b 70
    0x20444c410316000a0042a21151554002c54075200e083c092100c0c11890f4800500071040c0020004181a44016006802c0308070301581e036901b020725080d002e950200b031002c15584420003130b0000a03005002d4404480c0c261600040d815000ca00f0a554070b000b4240c050103092840c42440740d0220440c91070380c0300300c5003520b024204c0348007402000d080320b100c840003400045000c401440050507032911440d050200400c0c101c1c84d15240d454030a24201c0e55540d00f40821b03940c4501d480f1340c1c0200c8005a910020b112499100c86a41d004080c09502c195001660710705c0d9542d000030340a50145050b004a40441d43d58a1745950b101c5601800050f172000402c4043e20550103038500180300c00b02281c1c418041a075036140b41c40e1565803034929a540c070070014414480b01c80076103203014406451243d002c1e01503945400320b00d803e8145507421202590003920415060400a10103841c8c0015060708649050b00d00a550311008a0309901410541d003100341201492494003041c80002d07041d42d03000d01c0c46010312 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 316396906 1250 316395656 316395679
    0x20c06070513030204020d060506160b0f100314010e07090903030605040504050d0c06110d05160903080406050c07170c01090e0114040905030d0e100f0612080703140a0509 75
    0x79299806406400c0324a010140320910040c141500500704000d03d980000c61101e4840001070942d800070138a0400751080000d0120501004600e10358000c006030128461a080c00404114040d201c0d000103040049030001e8030304840030944c800c203c01c800c01c4041d580a103445200f1000500710b10740c01940000d08000010030f0301e00d018856180155404002441000c05805054a08001c4100f0550310310399213030081111115410700915401c1d8200d100003032107142100300010380180c015003030000c201c2605d00600001d00008116400c1d503000303042c4a5150090102618508a13068003c000e0060005051a07050300000410f00302d114000d8842c0307151980c070b0340850741711040240b0440d0804e407980c06884c4650300f4254007810441c3c2c004c0069900d06090a50344409440001002c100c6991140c901034010341d100f4850300d00324048100044c08041d00d071211013100c0040011002d040740c0c4000030364030105401004102e90301c84200881546400c01c5480240458108188140c016440c1d2800d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 316398156 1250 316396906 316396921
    0xf03090612051012031209060212130f1704050d0b0a1b020c0411121006080601110c1315140a0f0302101d0301020409020c010b0a03021c0501020418020c06 68
    0x40c10b840f8070104400c0c5803c0c503180401044203507103a024140c080c480c00788664044402070f03020350041c1c1402001c001d07944811a050000315070000030a01080c000e590b480c458005490a114000d025810602603001d10040c0c658007043c1e4441c60303104541c000500314481d07041040c042c3c1c10520030306001504120240030340d00a0290f90a2100b8800010380000924041c0d42c81c10b0344c0321196041c0c0c032043c000e0900b140300320b0304c141c800b10a56142255960061080008540c007500b0030b0b40c01102840c04031019007095000d46e94070b050030310000c1d2007075080c041c0410814802d42cbc002410640c400c0ca40c400002e0340c1d4183c0046099554844501525000304049a00d120720010501181d9000e0900d82405580da41e01300c441680c1e86c1154000005036907143e05c502e6a00740080e10203030421560060382d07000000c01c5103085039803070b40302c2e44d00500e00d02008101682d6515401d4407518000c48141d07203082a0307440c06034024400d9070061901581c68034042150707800f20380d024000c2d000703074007049481980b07900d074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 316399406 1250 316398156 316398161
    0x12060a0509010b12090712030809060c0415030b120703140609030a120209030106090f020405040e07060f050c0f0a0843080403050102030103030e0306160509040b0d0f03090612 77
    0x3d9807241038401c1140344100080c5114a55000300344205441c01c107500c1d800f61b03180c5841d040c03009900082400040c88400003050119540060840700030514003481c210004a000400c031180c8001d06035110b251540c5a11000302d018048d40340501036a0001d5201d00d8039521070b40940d030780034070715101d210000b4002040020460300c0355405511000c07101c0f2654842280658000c041403038055407503107400a2181228005c20540141108001d600d036810003061004842d2100c422140d5540500d00402003240c0045503184a100c485ca010f42d99003a40b00d5000749804880c906407107191041c00104024060b9840c041d2103501c2410b4200380052203450049007400c010190005482040e4040303400e11040001020b9070054802d0038524101542c0fa08c406007280c000b40e00030350100e8000640c820003442d051000543c46403075600409e1600121440c003e11901440c005940560f55401c5a84c01c0ca03030361201090403c41d48454181e01102540c0340083c091b00d40d610614001c1498103007166071031100c03030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 316400656 1250 316399406 316399409
    0x6080f060f010909050a0b0403030c020c0a12020d030c080304030f0e041b1211030a0507020d05030c03010303030b0609100c02131812030b0a08030408060c0304031d0f0612060a050901 80
    0xc180c1c03810180d080040500080040d00c1003155641300d03205c17013403000640040c6010704c070390b000e0f480000e2400c400c3c1001a04104540340440d114495110050010200500f203d55803290180c880260171016464180c03002c4191940141007070303102100f00410554400032003136042c2c25030307990461120506803d00c420380790300309411490b0586d1512800c43e0940703e04404014004002d4000c5000901001030720a150300585154403416110000c0090890b0100a040240d407806e00e0210310318989040f20110900040c040101016142c8812614a80c0c804043c1c8050701d5000341a2440d51020400107801d001110108a00030300c0d03950340d503d62030788140c492080b1481d82c400041491440341e507111502001c00840d1441890780e1460001000e03103d00c0702d010083c284c00c0c8000c50b038403070501d94160319014000388031881c0c00d00d0030020080040e0f0b00c4505400b2144c0d22980d4410020b0740800040c4a904521001700d802c000003189100786020000051405220242c580010f8923844078180044c20009 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 316401906 1250 316400656 316400671
    0x1e01060905041e080f0408150108060412110c120109020a0503010209030703170d060303050409060b030c0904090c0306110702130b01020303070516020a151d1e03030d0e0106080f06 79
    0x40d0f001e50340100d03203402d02c8110341e030780b044100c1868000b400080081c80c2c1c105821001c11680403110701d4000902d00002c60f130141000130000c02480c80c05581d4200b84207203d101460410a8401d003580c0d200700100003414070050010b10f607140d00c11503d41064000c21102405070300c20810580000f4a0b4207062085505144020b40035010a038215122490456451130104405c1c0d40704105040c0f8070b040c18494070340554465541c5655451a044030740c01501c005030010040158200f0a0007060b1021174105c40b05084151f40c0407030751517002c3c200740b80c00085540c8044c155908060440c0c001c0c228440003003030b11074402c4404e015603021040c030020841c1c03100d40d100d0780507a00410101e6540c1c0d010f04040c200d10001c0c1d160b0780c82e2080c030310380c08074840b141240c0c05030907054504942a09441c2d0051610100b00c2c0041c501c040e6800c0c41c43d0006103c154103490303c21010600c0c1100c850300ca4409008175920b04c44184130500020401d014130754000c08484c4910507440c0660412800c20313140100f6a54040c408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 316403156 1250 316401906 316401923
    0x15010e01080a090f050a0807140606010c030f020a060e0d020d02030f0d0528050403031a0a0504110d11041e030c03080a030e010c030c0206010501090f090507020106081e0106090504 79
    0x16007000400c0280030180341035940544e92120f4000098041041d008020b1281c0700550b2200d0481c03501c07100c0c0c0c10780800b0181841e04600100305081e684140380350a10398142c589040e00c8000804181e080c801d044a000d04400e003040c0100c00d210000240701824500c50740e0845035000644030040b80c9074007460305440c112080801c40c800f2a284c0300d804c80da4002e0549040703140b500d90400a00d010790345000c0a01501140c17201d0420040c1905446404c07420312031941401c480304c0c5800000b41560b00913002d41403090fa80c0b6000120308450349004c1d03d0b50f00e0103102040104020801501109070403e20901210b01c280c0c001c141d2100d005081c6400480354007140913000d043c1140c2d58400c070b58101d00820f808150781d80b45181c1401c4800d004201d8003a00c0342d20005072000002c00024140380707058000c64140814030a040000140301c2c00700804849407090300040946030140100d02400b0f02d40c1c000300d158416140d00a090703210002181680384000c0d80204002503403800701206840c0c00f1078001c0c0540310b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 316404406 1250 316403156 316403161
    0x50a06060e061e1509120601061e08060d0c0510090f1e0b07020114033402030a0c06150f06030506030a03090522110d0b04090f021e041415010e0108 65
    0x8000328508800b0280400301d03410808030b9070210300500410224446071fa8040d10041218503080341c515609241c100c6110720f0515820318018022034800b6180602480c1100c1c00b01c401d1000420440c009804010902c00c0902100348000345400624001c0c4810940c0300000000d040250742c6213440941404c41405a045203002c925104d80c0c0c000b03810907814041c003074500d21101e005082c0214821540243ca0038258510141c4000070041200d44cd4200c000703481c050050741d01c1c3c0000039a03440c0851840c051aa0f20046d1030204080c10450050200400b05440081b0b110400300040506035201030303800708410340e952030400d0794404240c1c1b03020b0007040c0750403401d110a04021208540d102652000c0141d01d02c030f00c400721803c9074031820940c210b0070400706081929a0039401059920101101c09110109098460842442c081070009120340700d150b4104900d00c601c04005107000400074010060001c00d030750101c040820448224100440070070a0361055802914648504081a52030140f582d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 316405656 1250 316404406 316404409
    0x601030f08040f090905010b010c0b060609120a0b090f0d211404050f010c050403170a090806040506040c151727160608010308180d050a06060e061e 65
    0x3020300c9a0240c4401d6001c01002c6640e40c0c04080c0c02004115101000415001a0403c0b500716a000c80300213041040c40b1081001013a042204190040b03c11105d1565900703024000480c5c0702c400c0d0142e460349009945811042c4280c0808071882210542d040c0c80a0040324029580c0741c4c400d142031314011a11b071080c000040403a9182520074001869400100014800d07241e010000c07085408a849a100c10714408414101380030f20910f84d9154140507042500f10341d52558229000c03c9102e800d030201081c400552481211508020320a01c801d50701c903070030542007040e11240704903002e44851055440c0000c50045c082c80e2100001c6403a510383c500c0e442031802c286050070002d0f000382c2c0d0500f03560f90700103a14001c1303003070003020410f801004011080301e021200d00184056444081480000c4004001044101c000c0300c21141c0d050b40e80d000032415000c00203004c00b2100402030941d1196600e0002040055445003013036800e242c402c0c004644d070f00001c204516651800c400b09480414244a0a9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 316406906 1250 316405656 316405673
    0x504060b1803070602101e140402012721240513031d031e06040605010503032a1906050604051f060806310b04090f08031906090c0e04090203060103 65
    0x245580c2e8447c10703070144100703103580c11381d940c0700c50072401c4402c244280011583c114411007019020404030035490b0781c9050340c43c5141c071504e104124502040d58851b41103086003411f900c141c0c541c00b555407041c045000c866400f004c900409440c030980e01d44004a40307016450b02101d0907656059481030810b190344403a8180e0a400e0038181505841411813409010340c0b09204080414140e00042019181508041c400e803031040e030082d80250400c01c0310072640c81440e1102003081d011802030b00110742e101081c00346005008000b24a5007285403181d04204442900b00a006100803101400340d038030b40155400c0e0390b8864a00100c0702c4090300008001349402001c045174070010080c80b8940d108000041d401d5045c1580c0c4940f6426008000340710f207800010f1290783e10303001007a181000300400b00d40d40e400440701c0481c0094042c120100004511000f141070944096a050106002039079984e200007000d401c1c1202c1450200c1c9500d221940f080c00e00344205580d00390014011300d203e928540303610341d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 316408156 1250 316406906 316406921
    0x120608070521070503070b070b010906080d18151d03010b0913051507180e040503040308090303070203010603030207140640080a0b06101d01090504060b180307060210 73
    0x1880c0c043c80c200010103a5007400010001c000710840f581d83d4090501d45200b541d501600840c42c7d081c5003040034000000000f07110f40c00d90720f031801e0a400e15501c01515030020140303540001074000152402e401c42e181d02c040203c446504c840c02078962803110100300340c02d80c0d1521170001c1c0c100040703400058003c41c3d0303a0b03c41c801e1507001d101a2915080c141d5405100319508641c04000324a0100c01046603401c1742040d03100030f001005107110581800e0b0741e21501ca101d144000f0b0135004001c910081f56680c280101c44800760b00800801001d81c0e2031034003a4030f0b922503209007441c9183d4400610304504011040f102b4844060700c4040301c580c1c0d8080c002c41c40440c8001c40d8040004940803103c000091b078659800038010580c01000503034440d01d001d0707010110052900b1300841e40c1c0c0c041c4103c0b0641140381c00e0b2400340c0c04481d409946d003280d001240d01a40507880b040d481350800c8000100300d01d046008080360384030100f10380722000300f502c20305a507000d00f44a8800143d2281003c1c02e8440080d610008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 316409406 1250 316408156 316408219
    0xc0c010e1302030c04150207031505040201030e030c060f070f14030705092110090b04140f01062306070503030c0711040c030e1005060a05010818010c1206080705 71
    0x422600455011080f80c10864800d20280350001e0b040c001e0030031039aa00604042c0c0c40c4000c10195096a540b480c100314541461648a82c4420100301168041e800c0307411030300d9041e42100d0f1140f5112a009a44100a40d0b12040400582d0040b4a20503c5902d07200502205919444034140342e0000080240c0d000500040400009000003045603440d010030325035601540384102c605000c0c032200c550802040b1030f006d4450318a40400f80300054007000e90703d035100c3c0d04840031141b110084051941444107003800007441d9460901d020400603501c101000c000a000c40705044c070030104a040c80001d10510341c1c0a08140d10500c002740403002280e0041c03603868401d18428644410402c0801c054803140490341d0003286c1c031030038082c000880400c0402110480c0c0724091009007003c00100d00d07000e185018460401001e08000f07040710180b0f410a2142c004d84000070450a03441d210001c02200250061f485624200080042e40440c0080c24805652009010208220264818400e038805894100707 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 316410656 1250 316409406 316409419
    0x20c03191707030507060b0f010e0603270d080c030603072303070303050306031605091503030c03040e0709060503101211091006170112030323010602070306060b0c0c010e 75
    0x3107842a100354068508680310381c6405469441c80e1411b1000e49241d022014040c4095005000442e80d0100c2c406254040c19152140e883c1c681ca10484203149101c03027100d2044407a9440c00c0c800b6080000c079404030038119540c0b400203440c0d40d08010900d00c0191a42541a40140000c4c0f10409024086061030340d041c0f08441d8540f01b41c0000302c2d041a440c1da000b80d010480c08800c00800e41402c1c041d072110204141c0060140c0c60138400040d40000000d008140c011043c0303091401070780c40802c00c0b07800480200d012680c0705c1e5692075100355984000c4980c50005034040b4800034070340b402001980d0061490362501c607000e505000c09048840410041582c292903604406c40c80ca03200c05145600980714101e111164030300300280030302a0341803d811034030014020b100421261300390746235840d000d0f03626140c0412101502d080300030144c000301c0b840f051414907202c0000f40107600005d0319000c4070300c80c001c1880b03904c0c0d8400c400c414500804070407040c40d1b000145201d240b503106c4d00000c41c102030024130b072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 316411906 1250 316410656 316410683
    0x614030c13030c060906030507020a02030a031103040306050f0114100207030f08071b0e150105120c09091303120504050a020909120c0723280509040302061006020c0319 74
    0x11145035203ca40d11040c046007200134240102607050050940c00f54160008052107040c0364003281d556104144041c040107400071400f024100c06000321401107400840600075420000700c113400a400a224020040b040f4030311000c030390700f41010544843c0c581038019008403490b507100c4104102c10780c0300c2100c502504003d4100003c8202c2c02c000314000740b1940054626041611a400303511000c4c0155080e04c0040c031030400d56aa0100c2150030786100540e0380001621861480c0e240c600038841c400758407200c0c0c0410020012007800c203449409008c0d9403144807424000382120100c0b2400d4401810070340201c0300d81d2001d414120202d90b00141d021045a0048000c0902204242c0000c1203909a0782c1000f0800c10121004801031045100000710340481f42c41c56000040840700480c248041004600000c60610326200c041c0000030034000d00300c0b09103881c083c98002d4403a181204c0c0c0e4490020005e1011404601c00681d4401c0c096015004004001800e1000c07000c2c01700020044034406843c191 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 316413156 1250 316411906 316411913
    0x17030406060509040b15033c012d05060603130201020f0607020c0a09020a081f0e04060c0314150d1b0311010906030c020a06020a05120106050903070614030c1303 71
    0x4010748107a00400440d081d5050440040c800c0e4401601407620a0f40035807a4011842d040100084002e030814190914015103424210008d1040b4241c0c4e0000d940b03068100b1a10f140f502491018118103010140052508400804100d4030140c58040e003040d0706000180801c0c1a241281180300c0c01401240d00d0302d1100b0b178081d0725001c3c00321155401078000b088a900e0a00f001c0400d40068154038000350305241300004002e01518008221080c0701a103e01041191149040598040e180b04d00c0050601d2070681000b201500c8a0b40c000d1001a2520030b40100b02c05046002034017940603c01c804510360f100504004400e036452034240c03038601c070006440350407480000e1400e0096101e1210541060072000c000740c000c000715840441490305009803248955804601c0c5c030840e41e03111100503124640c04004a54034040e00c038076108440050400810095000f401800318080220b04561045841c0e038400c9030300703901d01009010700390818008258511901e0000d0042c540440c003500000a980343c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 316414406 1250 316413156 316413169
    0x70605041203111e0c01090b030c0706180501020d050f011211010302180301020d060303030e24040807080d06050a0803040b1b030c0a03170a090809010c0c05211603170304060605 78
    0x414103001c5c0d40901c00b03040b400d58001084100400308408503a00714038000c10800e0082c81620f05c01081c0c3c65071b400d01042911408500302e181c29410a000b10b448007904c1302e220005280541c0c1040c1c500e030303800000046102c9031a480a40c690340c0050b0040740000c2c104019000b94103d0300c001003044031101004241500e0903c060640c04200f04804500c061946c00c020701240e20840459205803c000340781c5400740014000e00d043d00d02c20700f210154641d11400c0402031800744040040800b800042c0306007210400350824016a0021a06220116030740d9200030350300d1040307204031095400140b06200f420b41c091081030203154031101c01c0d64503081c1158180741c00d1071200310342200821040182c0e4251441c80704046540903045090810048000383c075001010702031084541d041040c03a005c40720421540c182d07031000a080140c41e6010b0f2900720203681070040000c859010311803043d401480702c2a010b81164400b1a90004c2003252000c0b11060880480e5100030002d0b240d40c0c0c3c0342e0300c1c0084c00382c407440c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 316415656 1250 316414406 316414453
    0x1e33011407060501140a1d040501020d020a0c1221050c12040f110a030206040b0a120e150907050a1503061d090d08250c05030d0e07060504120311 64
    0xc8400043d80c3d81410341c2d0046894141d482c450003400340110a000c211030101010000040300d01030a0819611840c009002e4490815000300c4640040740c0301d03015981004803401a24072641c580d1410a100724012541c0869600051000810480da000c9030b503400b80e401140c00c01a914840c0703241c0100b10091251484041e541100d040b1031500c5024144114244140c0802c0022103a00362501d20b160001602c502890050920a010000b007100300c46000c0d1328061408550110180b0070790180360b00306500d07206031041c46200780c10400001603c6070703408200a0150b4034010203030340480d0709000400c118003c01c0e05501d01859500c480201d00c030002050880d541c404040b80841152400301900f0303040219010600040c000e00909000f807004003038000015185484d01c400b80707014610700d0200c5031480010300281241c000003884041290580e08162000d4003224101c4800030b03034640c0d0860705072156124118455404910040000e407260b00c0c07074500c4103401d204648001d03441c2c0201d6044c038400c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 316416906 1250 316415656 316415663
    0xb010e0901081f060509060402030a1d0f0d0903051506060403050f07141009051c02090a090b130b010603020334020105010f03170a020106030b1e33011407 68
    0x3e10035003201c5081c07002e903040b80b03e101031007400343c24079101c040740085601401452285130007000080d40355136590301049080355a880c0100e02ca15a410035a0f40310203142c511915240602d210050030140074040d180c00b241d5100000f014070358213414a9000b404809080c566101a00304000004200100f20701544445c101024108080c9040b03100038402501b40425805400c480c0e100382072480e080040b40c0200c0318183d84075440003c5120702c038040c0c414010320082d440000070007030000a0700942d01001c042c40c8603c00a01c095120005555581808654000d00d103001c01001440024801d030003840c3c1112400d00e205110784204414440114251518407504800700c441104516509019244c01440e0003c0101c5005040d503c903545061000b008401455000040c0d030003040303100758403020066030444021901ca040c00c0e0300d021808589610540000d40054000c2494900101422452134060301d00c0c03c0310300000700d0000030a00038400c4440d0306001c8210344a0390b4024000b001440445d21 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 316418156 1250 316416906 316416913
    0x50a03020c0a091b120b030703200405100303030e070f1205060a020301050f06071401050117120a0c03030b0d021c03120b010c020d05010605040f020702010e0409050c040b010e090108 80
    0x80041400b1200740b641e84000d052906266903240c0807121031800b480101020320344224110020b4142c03501501c50200c1564140c03060040000c14040e622101001d01d00c5860889030203602d0070000c02c0103480f400e5070302e4084408211002c000080c001e1b0702c0b01195aa420b01600ca015548090807169840c8542c4030f10031100d039030020402041000d2050b60780c00000082d046056505050101e42070f03010019400e0701452002840b0300c12700248449410700600d07100000e00c407660311a05405100350460a40c44030b14440e0080c2c0e2490107802e40c0903100c1d0b50a05503500c14980c0300a85040300070f40007074072140d074202c1030f220320f0b040260f1140040904440c090315040b1040300d40304d00d0001d00340c10706d451140902502d8000e84008603070380140d1001c0c031203404407901034642240b4200b49004241c0b81d400241d100741f0b0001200300754913140e00a1309846000341c032407211040380b45080c04190385a4000050850700001c0a16040d464a82c0c4004801101803514902c0e408500c0c01149200001b81c1141a1503070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 316419406 1250 316418156 316418173
    0x80a17071121010b04200901030609021810030903020d0c0609020411270303030f041403030108011a010203030f04080c0a0213021206060f0406030f022719031509030c050a0302 77
    0x240904022410217603010003600c0094422103006064100070040b24110000302601203030703c01e800c0600076012180f004c56907603002740100110b80c06c0e6080140c0c0201020350f51005800d010744980b5007402e0b05034010300f1400036032001c00c95240200c0c0da000c0f50710603038031903010000da2610b200c1d58510100910007103690381d011480094000d159003400c014207260580c1400300030b44010090329000780c1600d201c2917154075985040d0700708030404002800b181c031002c400024643c03015081020303080884020030801080d05801240c0303910003150360040081f518804200010440340003031602c2400c0100b5903026440690000e140301d00f1507048120780a4011946400714180708041c1500000200c031118a0f101d1460348001301800b891150b80f082c5641c51401e181d840106804542c02117040c0364190310341e02c81c0140c02e444640c030041803050055115a9100e000a01c0c081d4450040c3c2c1e412800c2010005424007200c8060540c0c00b40890400c014036144000103181000401c0b0568406e0b000b030035401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 316420656 1250 316419406 316419469
    0x2113120305060f0406060e0904020d021002030703200316020310090308040204050a0e15100e0c220503120c1029040c0f0c020a03021207060801080a170711 68
    0x681210070282c03040b480c5c2442040120381160460006100a07110460640d4540c00014945401c8003406504000c80d810544075640d07012000b00200f62007074450004005410300c200032a060241c032169410340c0300b0051a1950102a84190343c03191004040707401000c200c55101d402d40c0c08030032044020500382c400380821403400b07000f0a54003001d56041041081030004c2072695030712203882c250b500320320108003289201c40081d10882c01342c079403030a03080c46c207041000c00d1030b00ba07038409810303140040d1140391081d07400c000c01400340046540080041101440510720007072190701406c1410a41e1088080c3c402d6030301128000c10144100d100c1018400c0204400c5026506090302d032040c0c1b041d0319041c80c05074002d07040b51043c5407040303803860003000d42281440499240c800c580c202a5000c20141076010038040c00141e10011b8035160355584149176a80c4031010365072507a0b198000d11481e4600300030020200c16102901c00d942c02108510720400b228800b081e01d5421184508c0c2c00701c1c40701086039146 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 316421906 1250 316420656 316420669
    0x7030207080a0b0103080f070b0412031b0f030f0b0a06020c01090801090b040b07030e06180d08042001210207020a060c0506071103090301050a09110303211312030506 73
    0x50649801410b030105042e80c0306219044140070050220801007281e1840b1060441a69030035640b028010000d130900d81801d620b04015054044c0021341084014003183d824074600c000001d0454903072080d0310392250016800750400c1410352807169507030403c0c01404e581e040010380090071190043c210070f0101800040c040c0310107401c51800c507818480e189000075100f029a40d840768000716142c81a484464084024000d142122410381c071460040c404084600e4100c1d070346a040c84400ca92aa480c81d5500743c0341a041282c0240c079a911954030207400b600d480705510b8004030145012001e5885c601000745003d1000604075800540c0829540b0450821100b440c020f031a19042c603003404c1000356119603983c1c070001e000d50104a00b00c7c0d0f02403800c14081058a03a2003200400038061032520b000c00d180105010b0074283c03826005109100030034180881100c091540d03201021400010401303c0d80203e1034050000312050321101612070120308200d400c0c11141d01d03ea070380405c8504140041004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 316423156 1250 316421906 316421909
    0x203070e070f090f1811120a0e071a0706090215031f08100f0b0d110405010608040308041205040f0308030703060501090f030f0f0204060b120708040b070e040608030f07030207 77
    0x40c0200c0f0a028010400302c4ca03002c0044034115402c8592011180e001a006040b1010000461030700c0070401141046800c102d0911640604200f006241401030303e00382e6921103442100002c052042400d0031200010004103e00d03400f074403010943d01c04590108000004284030584041070110901010301480307144600d100666161b000d8031710781000c0324180c03904c2001410b003154030703034503501120500001d4004030704540d0001c2c02003041300c4150810041d03a80e40c602403544102c3c0b50000101da1640200300d01d501903a015070b52402d01c0d64a80d41d9078100041140d03c1d000038404280000150f00e00700b801d81102070762280310465100e007084180901940d07043e07004039061000d401d0060111041009a120483e500103107900c104d0005820300c050038440383c0310701941190602d403011500c00202c00041060307001c5600b0007071380f035a11000101d41000c0c00785c400528201641021400303e900c2580c845110301030040000a003281d984450750b255510465010810f01804a00302c000c2c503405010200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 316424406 1250 316423156 316423187
    0x108100f060b0301060f030b0406260106260c090a06030332160210050c06100302130c051b1c02071508220302151302010905040506010203070203070e07 67
    0x3072141070000400c268041405003004000c0c1102a4100e11480386d0007640ca004409481005010340700c0b5139025885000380400d01c8148081c82801c18030350f0b0144540c4044450b1405000c3c401785511898455618011510821a1080e4010341c1078560356440316a009040301807000483c00d2840ca0080d1042d0901d00048a1140f80c00c040d4550000c40150b139405581841c20107140e8076140559407a211958462000e50403242483c440c030a1503401000800200c400c1204072080396036078a841190300c90050000a412184010f100d90718500310b0780010202186c1401e0050500c60b40c024106155050400c040c40c090b400403980062242c011198142d00450034800381c1005401c1c5684441c2420340b0484a0040124000008500c0030800007400c44e40c1600c4001061000007a060084d42da803010f601004c481350841020402c0c07090f103080c00400c03080e81a101c54860303a1608007040010b000042c03080d41540010040440140c0d4240213005c0a0700b500e00e6032000c0380c2800c440c000d0401c801d484080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 316425656 1250 316424406 316424411
    0x307082a0405070f03150b07060903080609100b0702010302040306020c010c110c011d06040b18040f0902030c040902061306080a0c020c241902060412091512140108100f 74
    0x7020540c0d00252418a103002810b001c140c4448031b200e03020a09607642d210300c0d2810b00118184007000311130f03000001c41e14040ea680f1150380d1030b000200b20204000b030358504040017079600e0401c10809204e010b4109540141401070800340c0ea91140401da90026400c01c045941d904504c40a0340c1d0071038460003903a125540105035914200001a0484900541c030341d000010480c0c02101954a000c100c4004d0403201c101c075a221101548d011040b00c0d01c6003522445681008410030658006203d84007000c0e40080082c020340d032101040c4401028585000c0e070b0025810000d0b01c0e092040f004542c4000c10303581da01c0c1d01c95803030211104411940500480d0046403c50400030b091961405e241018034801c00324501d0012020f030002c44070354030079810301c1d07030303d41345c07003061143c050360300070a00c5486180620003001c42c192485500b21002c5c00c09000c0d80c04400750386050150494492520590203202041c000142e8800b120144901c20001742d10031902c6600400d0b1040880045015419603100c3d0400203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 316426906 1250 316425656 316425661
    0x16060906061a1b07030615091406100503191d0111030f0412030f090b16020609030301170c040e03030118050702060601122004051e0901060507020307082a0405 70
    0x8070341c2d5842072404140403652062a012207880d03040c00082c0080d0b52040303081040b00d0120740c440700760800c00d10400d0080b80c40d00c16240d043c0e5000c1000c80d4494131005080740c42c145410001900c00b03801c040d0901024404442902c5d0003820b42e0b200da51030007086446134000f903040b10030040d825112401c0160072146401c1c01030001d14041000083d0b00650303c1503541c0903411188508a00a001d002e10401e9014108034210f000e001c40b80c84a24000c031007486210307030b42d0203001000366683c40080c0c0e19101039900400040040107100c50030321010703d18032410f0701c80071a200b81c0000e060314003a21a041d5583c0000004109500b40313000c00305510484880140103515003600c2c01303525000c004213120f051100c290b09043e0018141e07401140c100e480c1c0464040c00304000c41c0c0c0d00c00660030501600c1e000b40082c00000184100c42d0355112500e10f002400c800700d41c0e003811400c072916041400704a03018418203034042610340c070a12401c61074043c0b2030100c2710b40060400750711011550706d000460003189003005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 316428156 1250 316426906 316426949
    0x10305070219151d0705040e0a0c03060501030c05062d1e030601020c01021b0d02012105010305010e15010314011418160506181c0f02120d050403060c03021606090606 73
    0x804004449040360009861000208d601d030034802015002000e2070006000801082010350ac00d9040e0382c01303280300146242d1100f0a202e61032040700d218400170b0306003136140030040d00c0c0b40c1500c91403c2c900324a421304100880c3c07803860070303c003a40078001c5941e0408820040c1d156410030010710030780e80900c003c10b09100c40344a091220342d0390441c03284c05101e240407032a007964020300c0c00302c071400c00b52180da01c075010304d9240c1c0030014542800102c4295082000716449900005184e030884c148100b42000d5903440c41e500d80349030582180105407155210380e06008904130501517244034800b01406151401c419040681c2045540a00d407464165601d205009640301c1c0e400782c590164160980103452510700000601c031401c8003442481e2480c207850700c14104048035441c40d0703410707109488601107441141e0100391100502544900010310510040020452941169100c611142401031501c0d0740a4090004105101c4060b01c07952b0b101c0020704200b110910800c0010a01010340d00d41480c20102c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 316429406 1250 316428156 316428163
    0x40b0303070807061802131509150e0405150907170106030b011403010605090702010f0f02091503100e0708040b0f07020303010501050f1201090e070b07050a02010305070219151d 78
    0x200075208940d24844140d0004a0705d9003580d5598004006e61b040b1020f2181400240c0424440070110320b207a071100148581e00c501494001c0e00c500051140601e007098440c1550341070080040c2c506110313004011000d0903c2d440d10500456100c009401c5950500065981c84118094600c80680c5018404c1000c121103500b580c0c1501c08580300c603103c107101c0d000000c3c050000c40d00300e180c1c070024000510051716015031000c9111403038040207000c000c040c4140d000890041c03000290f00715200e2514085001c0400d0001c50703102004180100910303403030780b040d10480b4000b191654082201d9205001c05c0c00005039440303038041d0007404007108038a4454002502c0780410301c1140c3c180034000c540c0080860014059030a50486440804020340e500d6107010007610312554094601c1c000c40e600880e81c00c034030318210386081d03820500910050409034011401408010a8501140140c6a100c0c6940750900400c0070807500584119a180707003000107107400c0324664119401c1c0c111840642e50210035011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 316430656 1250 316429406 316429417
    0x2306090a030c03120e01051906030f060b1201020a020c1e0102120307091d150307030f0b1806070c03030b0d0506010b0703052818060c1506180605040b03030708 70
    0x40c0780122540c010b030701e4141c03404021614035030000b9082c19105070220105500482c4034807a40c0c8140e5803407018483c1400e003141c4850201a0104090304206004500140c0020726070380800307044400c80c000005542d03802c98000c20f400400680203079500310f0240c5410a0941c02c62051031080400c54202d480c0080d5942012103102c00c1580700c00b1000030a40c80c00b441403000100410056501460541c11301034101da0070454801b0922280c00d8140d424600700018007809aa910901080002c1a140c85502e040103005011040748000411b024280392014090b0394014103891b00d5940c211030041c44d0140507204c803001c1e140e0103032420083e00004a14000386032411141c0c103064103556207a031820202c90511a01090400c03030006603134540600082d4000c607220000c9165200c1c40d0034407000001040e1405188920030004086c04e1000011074106000b003641c0c0600940001090740d07403007409034104058128045041e81d5590b204200c1402d02d405148040c1d00e00702c0266203007070700b03560380e0a02c00d000d00d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 316431906 1250 316430656 316430663
    0xa03030c020102060106091d0711250f032d020d0302010c030b0411040b0705030706110408100615050a09030b07090306110703080403081e16030b0a031112030f04032306090a 76
    0x8603408980081c0c020081c000e4214042c00545003c00f6140d002200a5881120240b002c02826900081c440300e01833030110940340e1100480001c414026160021010310503880e9840e50424180d1600503660001ca03c0f00340d0b403081e0004520428418009805c81d03564080c264015820503070420303c3d6484400445040d1200c00c1102501c500c0e090600c60f24501605000409507440c080c00c4c1404008024007030802c07503e00408071a40c010032445000242da9180c89642405c18000e0101803540c1c1c005d801030a42d0300d00038940600d80ba07680b0388526201000503107134803000c150300303581c14400d03c0218012400038413200340b80c03145000b401c0d540042030280014030240410103170b900403d400000e028601a0740d500c410504148500f00300f135000380000d0700d50b81c0c10000b10389095000d00c0f1508041c6801030842c1c0d0406009500261044203000035840d4190700301c1880d000c100000b00740300c51240085d0003e1405005545d004014003107501219001c1032480c909941c0c80341080020b2441d0000350801c0c00f660 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 316433156 1250 316431906 316431959
    0x6060503070c06200717040807060f0201091205190519031805030a02010506010e0906090a020f0405030102070602070605010b03010e01090b010e0303030a050a060510050d0203090c0a03030c02010206010609 90
    0xc0c20705000006000980d4181d407000301e120700894a1340000c5026042ca02e019060070010000e8491100c2031071b22a504c9056090380100000300002405203851554001e818000811309108640c1c80503941b001d400a040085000840c0114810f4801841c40380c80c40c1c038078244185016202011260310a0264070f1441c01c1680341e50225100c80982603d4030302c3e141c0d10500b129203c401018000e1301a12080320b1a0b400200300a02a10940c07801446e0b180c007420010340a0201921050b203060302941c001d03021444410f1040000140e180c80900c0109000c0d4001e020040c0c40e188031f072a0003c15500180c7c09810360400034001882206141803250b4111400c81c800003440c04075000c016204800d00c0f075440360f41800003204200c1c3c010904d800041c4140c403d100200507071600c3c0d0003040741001401401da00000c0050141c04191100c0364004c540002241c0101d41c4400c0440300041c0c030205140d082200001c11808c0100304550b0100b001901400d03071410701003041070820200700281030b40a440c05030b10390b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 316434406 1250 316433156 316433177
    0x8100603140a0c03140403050315040b010e09060102010e0f150f07080711010b040c080a05090303070f080405070302030d02150a050c1909050604152c0d03110105280606050307 77
    0x2070107170740102a2001c130320741001c0c85440c290401501980040314031116a46040028015034903061192914441050b1200c000003425601030081c0340d4030041c40c59065644c2d6049110248070308003c0440c144c1c10322401460304152514002a03c00b101a2202c000010940184900107401151607503114840e407038002500440e0500460141c82500c6046420510308805603200543c001c44081c814842c412003880315403618107038180d680c44215402d200003403000ba503a1254034800c41c01a03400a0003641100c071300035181e0700003a0524040c10a500056800920340d0110902e0481e0740a90200668804100a141404800c00584140096482d99807003004c042039500380100b80d540c0261074054401c50301d43d51245200c40c21236a504c5215000720f103162100b040096500881c413020000c4500105c40f600c581d5005010101365a08000ca040c07080600941441e62005d1248521824526100a800c01e0b08504880741102c48140e860800c0d6013072a400317000c1190840100c0760800014a00b049154 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 316435656 1250 316434406 316434431
    0x90d080c07080a050a0e120c060d02092e02071a0a110a03030c0e0603100b09030307050d03090b1806010b0906040302031603050c01050c0c1c0b0708100603140a 70
    0x52084001c018034034103000c288480d08a40c0700000d84410364541d25131742c86804a29003003001c1907a981244002c0e55024903034201190400e003025040c1d10110070005400c1200c4d44002940381040070940820351906107104902007110f041c8070320301600490000c0d0a032942080600c401c0c045c21560207030308062002450000084c402c40150414803000c4040d108404000d140c0140a07202521401d8000b40200c000840c09240000841e03018928405140fa6114a0300060b400341b500500151581400240108404900c09102d03650120600d80c4d80010b14107268a00140510800b41865001480980c5c4400c41440c00142c6103041d510410720854032008a400010513500c5603800081d05400741e82030310440201c0b5154001d09491160081d11028400c2c0d5004550b54003d0302c04041e02544021429001810f01010207402000300300e01040e03862016441d8404003001c26101d100c0000ca0500c2007044812441d00c06d20047c0c2054542030020381c1e0b90080a90b5880c5000e8010040340b81d40750701c2c81420 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 316436906 1250 316435656 316435681
    0x1a06121605070618030906022e090b01030b1e070e120c03071e05010f02070e060112020c031801031a120c0d1208011a030a230907050117090d08 63
    0x9140d00010130300c00c1c80000c243d080d51000800c6422004640450000b0941c00e00100f6921100318041c2c084010f03003500a402690780c071041603840580c0c00c1d40c1d80c2e09407000c80c3d8403147c218041e42c001d0340c40b203035582801d031424040c0c905280030103403071000c4140922810740c6e40060300203116a41200c42c1c03254081c0c5180c5403401c0c901880e0003103505d0310070364400084180d000d41001c044a80d00f04000c0702090741d02c20040d11141c0440c20102c006030400c040074043c0007000000960416010b06d040d0350650b08031824182260301c07a107180c030b00907440403681000b96a014116003111840c2032074140481e8900c05403101c001d00c1c000d07a445205194440301139592240401c064041d030710005100500184860519290f498549181d07400041c0d0518008240210b1840481c000c01c0700302040d0502e5030740c4004034000144501050440010300c3d00303601e0001c10100d001c802d0300070341508015200c0340d4607002c009000f4400306096480000c1296080003846000401e4160f8151040d080c50b0201c1d690b4521314605 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 316438156 1250 316436906 316436917
    0x7060c1401051306051b0406030b031e0a03050a02010e0106140306090a17160b0a021e0a0c201905040c1404030b07110307030e0a06050c070b16020301050a1a06121605 73
    0x1b8201400b042c000750b6280d064000b07840307203413003a000d8958140810301020001203606005001c4c42e848800ca450000703104200034881c00d00307503100016095070f80103403150075a5440d62000f000ca0300c0345c0c03a900c4214901400143e070400390040040c840741100796101921f1406181e116070600c140031a0079080380111a41da03640e07072070384a840b4414030724002500c1c000a4010341440c4c0003420724100341440c900070304001c0b034001d81880e1f240d280039006160787e00e110060881501c1d600c1c0c0f10b2007440d8034070305841d0390b0040c2e481300074050307070303441103030342090140422291102d4400d020002400003e01640262004803415250840c2001000307940e046000d1310200c0302581440c00070b110028144081c1944100302c0c50006604403424a00207940da0021601c0380034a010512043e0000300c7e00300300392404c050080440081c600e480100441580d00000e0841e0401c664103560b5603140c090140d400321003020301409640007296540d080c001518048081000001e0400346410710f5482c10b80c003124025410340e01f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 316439406 1250 316438156 316438201
    0x19080a17040c0e22151e09050607020a0201090909020102030906070605100b03160f1110050603070f0e070e0a21021003050919020d0507060c140105130605 68
    0x8007814186400980392015119081c41003660b140421502440d0a41e0b0040c0c09803142c0380b40e16070761529115441140441c104141009540c0d29940d243c00c82d494010160040b54070700001038118107810104e04001c4024514000c54120f000f074840140c1c4c001da0118140c90001d940003550452031720050b46548141e4044603842800800e410301040781a81000d442014030709107103030340540c1c0c503400c000890005032207507401c030b0307d12400c070350401842110030000b442e100f413502030b40d180ba84a40ca982482651041d0352100740e00d980c00c00c41c880c1002c020700c0d4010b01d10309030286409454405442c80d01b1070090520020841070543c9007a031503841000c0c0501406010040b1824107401030203800c008144800200d005118848881e41c980340644120b038410f100740d402904821710740792041000c0e41c10462007280d0203a2142d0601700401d01c20000301e0007904150712141510941c034140240300743c13100e0348080001e030306000c1003160b4480301d688660009640800041387d251901200140907203078a00740103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 316440656 1250 316439406 316439447
    0x40b07080909091614150d0f020c03071a07230f0f040312080c040920030108010c1704080a030c0c0b0702030306040b0a080a020f0315040f03090819080a 67
    0x110618002c01d48402018040c4e09040110b55580803900a1030078601d10140d021315042000c1003d242d1072002002d0102d00741e20300240080600e401181281c020310003603006a400880e10f003003004a40c0748002c182e05510450140d81d0320300b14000418103007515040b5001604015000c80752207207001c0c01c0d104414506070b921911000604002112908544825161221000c09025000c0d004510342405404103821891401341000280d0010300072501d61071001c411141c41e01c2007108414400b95018240340700000c0707403a405800c801022400a9194404000421401c6c04002944201100c1c0440381e1814040b600400102c0f09035860601444050005468401041480e41c1c1c04002944965030803a010006a6100310078000b00c04030a0040389600e510040340f40001d85000c52001c0a41c010050850f1080c140520441d40e42c004152011184260218540e40c105500040004007800c50310004100407a07601d0740000508840300c501814181002030401f840034403c100c0340c40c40c04a00c8600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 316441906 1250 316440656 316440661
    0x60f06060a090e040b040b0c1303060209180f0108010506031209010e0a15020d23040b0d02040f0b0403061a1c080d1515030e060c16060504030206160e06040b07080909 73
    0x240002d40119000c84070707d541e920008202e410081b0a4440a40d03610b01445001c60643d51030f10000d500c4513071865800b50880e102c03454041800c0c81e455100303030210031110f4400e501d080c0304207003900c2c000340c00e540c03094206408001d0125050307020386414a03024681070316034501007408079800c101d06030002c21510700501e8460805540016640034011490b03915070541d880c1010045a0401442075a1016501e0410041040900ca440582076500344071100510741030340c0ba0710340601045994070402d610800803030100180480c0f441000820300440052011151302c07a0002002501c20307000c00c7d07485030084170505007804030200541d032401038802006c00c90f00308500803108052041e4480d80c13410340790034505420454070a02503500421400001401c0c545c60b1000c00d0810b642141c0001d07225400306d07100c0e5902207250b6005980c02640260090400390405508401c1e041081080c142c051004801d051f07901600e451040b0b60884000b1510551140b0840ca004a040e10a108142d0b9011228405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 316443156 1250 316441906 316441913
    0xf060b0a15020109020f010e030304061d1903030206061503010512100c111c0509060c0c060d0b010315180f020705011a010207080c0a03020d1416050a08060f06060a090e04 75
    0xc0c44e6010b0003210000c1041035084011544021600b4000750942c2040c8400c010035230107400000c03010220403c44151480001000c20840200c0e41404418a803903010b08205058040c044030380c0001068a00c200390060b450208001c511041c4106400b940a03010340342640035003407101c4c09440402403010b2011000c0203000900d61180002e01802d54000c21050300f80d204144290401d9011051b1521ba05120f00c5404001c1e990b00140349100050080740480300155031050018000c1110180b000101c2050100006003154400c01489480d025031480030f01c5640ea1040c18240c140d402c80c9004541415181c8000020b8002c148009116609005c0009103005044c50104031099080c0d0881d86410340d926071042da00d000c810307034050b00030045031024001360500303031007480c03945002c1c111a000c10410440381620b4100c0c00c040107410403c0030300091060b490800090401400310304010210340c00d0810100c4907030400900300e944a00340010b03949000301e0107a40404010301400301700351180e141508 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 316444406 1250 316443156 316443161
    0xe0603150a0b040c0206100918050f16060203120c0d0e06040b010e061c150e0303090d110a1e0218070201020a0206060904031707120c050702041104030f060b0a150201 73
    0x250550f11031428180901003183c4009032040c0f26900201b03018008502d0a46500001c00c1403081c3d5181c9408084544030108004210f004c03c1c03d0200401084d0040800c80c448540c00d0060700540111340041008900903000c0d004015003245540d100b26131384100302c2445400800003078140070401c0c040d580c1040280000000c1c80b904076400c0e02c4809206075184c204020840400280e00e40b8100b50400000020850740103840040c2800410001007082c41c14101511310b40046410443c0760b40104042d6100d40c4d44107503019a22020f150003445420120303a1000d0300c091500e40718a88841e030010600055540e1070303003101c0209100e03440b940110b042030000203010f9448000490090f200b00c201181c039600340005c0e00e5200315015500d50301040070f0100c15164240780a8074680801c048606401400c2d07407980b0441040718000c1c3c90b01c3d80c2e181d84a00c144000d4400c503085c10113058001340700c1007001c901c070352090034030f896848800011030014250000b2224480c0f40c0240d100103042400600c02d598055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 316445656 1250 316444406 316444421
    0x50109020315040804030f230a03020d08160507170a02101104030305030103030e0a23011d0102030301053102121003080a1b0b0405070e01090e070e0603150a 69
    0xd40a03aa402c0050309901001803038161001812448200320070004201440e14003c8014030440c0b22840448400e250021004001180b40d01c3c00c0c0c001034508000c254040140c040080c0c22410b140c400c62400795140310b0120b60f1460300b20203000f00015000c0c100060ba050b40c0c01c5400c02c0380300d00e5480381d8403007900943e110030454520450514203880c4070f030520624425501100d60540d56641b9582c00c5030780464001030092201c42d004a0780a01c0030910345840340c81d895580090403595003440804400060090081c0e00c1a00c0780e00c00f20510b0486940d90210483c0c0c103649003550b00e03803c0304a00015401d03a42c0000c03100243d00149450700b03c0d8250000f0340051180b4034007940c6091140d242e511641800141901c80184010000c1044000c0c03503001d140345580b80414a09030211800341900c0c0c00d01241c401301d6040781c0c241c00c1007000303008100910800c00e0141108010800041e441e1010003541c0e0712442c01ba41300320800043c00030704d0981c0d0403c080d160401680e02805120308110041d000030b400f24 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 316446906 1250 316445656 316445659
    0x4121a0c0307081e01090b0d0213020d1409060f0414060721020a08060909030d020f0c0d1809050c0904020c0c0a0b070b0402060702010215071107050d21020f070305010902 75
    0x2007002c02d01c40316920300c441003084813a6800f50810303481e201e0041c0c0141105512590800c003042417007409a0307515058100132010880015130341c0c810807240d03107084601041c0c0c00380121550109020400000141c1da9900203001e090b180d82175241c60508500112400560030750f14410603082010300b42d404000c0f101101580b2008060005913542100c00b6030040e0307115940041e40381800140b032460154801ca130090030ba24207032841c1c403240c00004c10585e84104040d07078034400006401160b0300e1081041e82c01c550030500e06a0368a010140c00d506d426203151155800c0b540e1280c012850003001c8100700c8518400040086543e10400c2000d02e0701c80c03440d100d13000e10664144400045400c0010f046400300e0f5404135160500d551558200300b43c0340c000c5c10059046206a03902c80304500031143c450b50041c25192203204a080d04000311903d450b036541c102c1c0d8040c10b051302c80c20340029191010040745081d91038284c0320440c01c1050803071500042c0075120f211803140c00c6c1e0020500c8030661101940c02d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 316448156 1250 316446906 316446917
    0x1170a0b01090905010303171803070506040b09060f0a02030a0204091a03010c0e15160f0b010e0601031a0d030c080d021804050103020d0201051e1218010e0304121a0c0307 75
    0x40d00e003562030403140244409400310303075401c0235040b80b40030300400240d00c813090f030765403164000303034a015549940c1003404c08071050b030f206605100511041601450707110701950010320b03041c0f40c8512000429900607088a40051300440404d0784000c50f901554050f150300401008001c0d0030074501a080c0d001e145089010303519040081d41c030b01c0d1150418041c40d49001e0042e04a4409009081340c660b4844850480c841e07260b94081c100252500c00c50040040c001d82c01c14005504025000328651005030003070341410318100c40c60403020820044c00e2400d000c2295940b4400c2d00c2410141d54000c0c440c40020032680d40010139000c101e15079405428104100f00c508405d4080d031005210441d0020b020195008000002010066200d00002d081c00784603480c9260950f2401119070607940c21443d1070380048544001000300c980790b0740c0566000416418002c3c0309088482c1c500030780346d1040b4054580ca1080e600c0782d003001d0050111081540b20720071410f11541d07141c40180382140340c00c1900c40100041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 316449406 1250 316448156 316448159
    0x1713030e041406060906071407050312070f0308091f0e010b01030905071205030412061a03030a0804060c031e0b030705030a0507060e040b1002010f0b0a0305031801170a0b0109 77
    0x41c0340c440e1442101d08141c01e40000e489150800400d0b40000501d00c1e404001048900002500d00c84c401542358044801854000d04204c10182018128185081c0e40903040c0310603404505c0602b8100a031503011b0809241c1a1140810305042c1081418800c600d0110000d80c1482e000d01039202016603604500204400d42c425001101620207c40340a0300682c4032035070a10034811070409100f2814400c0f02180d19103a40d40c0040e0b40e54144030f100c02c0d40c515a96030325480e0101528192000c0c501c5e0121702451800d004584060701c07290340500041c10303c9640b851183c09960207544459600c0f010395401218900000901501400031441c01900900070181e00194a0030000345071980345901202810400d814403070f04607900c412800e10395a020b40c5580848103151030f240380203201c0060f036500214880c01402c0c01502904c80203641c0340c0c0a0000c0f1f09041000c41c3d4003106946445500d0280c0b50102c0c480030300102d0700e02c4035059201000d14603000a0103000740c2c4580c04601c802d902a2039a500b4070f0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 316450656 1250 316449406 316449409
    0x3060f07032013090f0c02030405092d100e0606030a0b01032007051204080312090a020d1203060e06030705191a0c06010e060109120201020708070807140d0c05060a1713030e 76
    0xc81c4030317146c0c00300581c0c02800140031500d40145602c0c0e125081e4a40381d02c1d1001090040c2c5e0a0013205004107602609880c14082c000005180d9080900031441c5010200e0500c07102188041c44010b103107900075a035038441903180da0b1080d0402400303c00786200050300d00c4442440c0b042c00d60301800f07080b1841e110b0405080714011044040d18101d80c00b0101460904001c50000920708000404007045c6000c3c1608110040c1d4900f4440d082440c02a21200c0566440c40c2d405030171501d0301c4c1c10640400040b54100a42d90b90000703841404c1c0c0f0025113210f42038030020740001c0c0208146810407514040c3c92402201d2001206018050340b004400c00c4501300c1c2d80c0d0303050503c1c154006a414900103140080309103c1070408900c0c4809192040c41218100c56903566840d09103600b54000c3c1080e60006041081203d0b80012000041c0204903981c2140344103c0d900c401d04c0c0403092241c076004070700218441813030038000c11031000381c41311300b0800c2c0d01d091034825401040c400030769130110023042080002648a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 316451906 1250 316450656 316450661
    0xb09030d180b010e04080f0301090c080f0115120b090103050f06070f0507081b01050901050a061a040e0c07050f0705150702030604031101180507030b0603060f07032013090f 76
    0x41d9904090910303866403c01c0032200726103400500c203442000302080b17161440401d00307000f14001c10b540e900001d00b100d0070b81001480500007819028080200a00511281418541e09903d036245800d1071104240c0300d11100f0042c2544013060365100704014000400e0050218590102d024940c06a03452942c0d11141078507108945c0c82054000740c3c0c00e0014400090301e085c02080030501c0c040901401c0012400c0950a440b0100c80b03801603a51500c091041400b064040d182c050041c1c400c0d59807a2070700604840503680500c1c4107041d1a14006408030b060300703444104603019075800005a8004c04020305409586c4d90441c8034145c01070f0f2500032803104244101c01580d0300c00b80c1c000c010b401d2503113494030301306d82c181c0700400c140700307103540c2c4115030b10f0b08450303040c68207218501c00d0020301481c0d803840c2404103220ba001848180a40c0009040004e0300701c000300c19541c0302d2294240025160000820b4a4400c800c2480c8854100300008150030b804080f4100b907002c441c0c41100c02d1100519110b1035509 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 316453156 1250 316451906 316451951
    0x1060b09010810181a0409060b1e0f0f010908070b070507062d0210090f0b130209040b090a080403142107060b04110412030806010f08180a0b09030d 65
    0x540c4500001806602081c0317402c02d0304031100d000001075002800c500010100d03004500b040325080e549080094040c20904d40a060440c610480200008204804290950440d1001910900b201c100b01405680120300b108040d001c0341040351001034941d4183c21480e0311543d42030342c16205401000070700e24495032519503620b0703800300b0704808508240250040324070303000092401d40c0130340000701c95032507168865011003500404c5072101c10455030402d9a1110700150020701788409030755016015032211449150410340c045810360031544c400860314100140d20a0090400600090020602ca80310351140d0050202c082550000d90586050040d0f140145a003110a000180840b4010070310325480401c40e11005000840c40384002c0010600c50740c0250403801109001584000c149544000b68130341c03040c801e00701420041c0c200ea0000d450390400802c2c28040502d0b16000180d12a8180038a803681d0b46e001842508034108a124191290001101000c15619100b482ea0046980c4495103a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 316454406 1250 316453156 316453169
    0xc030f1b0a210c050a03050c03010617070504120305040501021b300703030f14090a090b03030c0d031e051603020a090e130b06040912030b0a0801060b09010810 70
    0xa10300801c402058a00804a03080b010040b141d00405004400a50040041582d40e070358440d0740d91480c0d2000541243c001801c5203400d84010b00040c0402c82d0880c41d40e01c6040d03d074500c01611551812002c45083c403a50b001880f110f9001d500c400109504000035005840d426001d8980d11107810000742c8112a00a05c281d6004064003a024421228041d1455111015540e20701420540220040c648400b550080340050340e2100c10481d9981d102e50000c4104401d81d0305a450002814002910300b1024015180311681d140c0f01729074961b034204203d40514840340255001440040c0340a00240a5005105003511550215403e12001d51040368400e0003070104d03450b05103c0043c0110025080091600180300c07032044041008065042142d1052a15020b4046181d9191604484400f40548254000c80c00c080402c800201144108804c452152400041170414180040c256103003030340c0409069440c1070800329006452100410806900780c907468099150704d6103c016100003845204d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 316455656 1250 316454406 316454461
    0xb030f0d0302041d2e0b070803160c0302030a050f092205090109080417120705010507120603151e0608071a071a04050a080301060509030706030606120b030106030602030c030f 77
    0x141d070030403101c005030550400c40c043d0f01795140d40c41e41c0c000642540310b0507060710441c2010042210b62241c04c0301c20103000f1061b02d03124401035016900079541c0c0c000c1c04618800d0050100721030307400008039030036100d035224014580c01c01980c030403000c03d0002a90700b42c400e40b00b0742001c0c001071156505001d40c90f50141d001e429540f070b0a28001103c800c41c040012000300e00d01030b0031005c001e0915440040c0402500500002405003014100034022000300c545042195040650400105500140f41000b0403115200810109407540261409812002040e10110f00d07007180400c1242e00080c18000350303401404210507207854082ea03c42c543c02008001003c440d030403800920100714907545660030a20030001c6541911607a5a50461500240c00c0355001800100e21003069290802880b001440a42004c10106007000e100418811a00380500328543d10f0f0001e10b00d95407004d40c400401560800d000b1900ea00340590b0b4450309500c02c1c2c1340849240c20131000700b081712400b000018880d05410124 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 316456906 1250 316455656 316455691
    0x1806040b0909370209030f030c060609011508060d080c010c0806090609040212030702060703030b0918060105100e030a24060810090f0b100f0f0e01090b030f0d0302041d 74
    0x1440304590b462121081044e03002e11490145071020000307c101e40a145002d542c0f54044a05501e02e8910b009012900c1800c0070001080402844184072024048502e048166503440001182e40d151075001c00418408001500c000da001040d070290f406110300390350b03c0803507489040801c15070000a0300c500e540b20f812940403a005142102c501010043c0d1241902c1c10854a41c00244003604041000d8000c40d4031003440400601d0100041e0307a0000022200780350311251132a20540d54801405058011007040230304000b00d42c007604a0040307200004048414550396450007080c0e0460040d0078000c1c0d41c0750701c1210070384c1140e50300800090394648001461210721144001c006130210795016a08040301d240b60001146926150310302c240c1c0d00740d0b840840686000301c403580d400251784c8803040c4e84004007000c1c0f000c01c1907c8072150440e49181e001081c12203414000a090400ca1a01c03203c40d881450a100300030f9402d60042c01c100c1d0541d00314a0462542140d0544070a1005c4039a00d40c0a92131540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 316458156 1250 316456906 316456981
    0xa0b0301111b070f030b010f06050a021c05070516060206060a03081602010e040207050f060901020721050c0601080106061403090a0318120605060907140f1806040b0909 74
    0x309030425684030790864850f96540c084541c1881c11582054415405040061000302441d2800b08000d1a20349071040c0381100565000391100c1c0740300e02980388443c1004140c41c21a10a1080d9035000d1b23000010350b9085265480c0300014004070307201d90340260040100181d07861030718441d4101242c2c1c000803554030780001901c0700d20304010305035800c9041c000441e202d0034040e10f9034805403003650f1060f4000c05071080c01c044403d181c03c0000300801016801040108006094401150300000da460011925000036003c251164014100b180c0c0c4d0512603a400080e0b07404054010508036059034a500400c5129041850003c5c80100d4042c0c2450380401440341c006031042405002c06111160140e40054840500c41031080316428151452a00c800c02c3c803845290060360b168007d445405c082c007100c140c41c04881c0c081d0007040300c91210010080703060300040f4220300300501c0c0e5140c000e01c203076a101d0320341c0442e801e15044540100d000300021400200c1401115495080d0700a90340f0002008040864 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 316459406 1250 316458156 316458187
    0x51512040312060b0c16090b0a06051e0a020a0b0a14010513061703040e0c030403080103020909010f1d100c050d1a09101a0a051c0e0d05030a0b030111 66
    0x2a00030440c0d0303180c0001602008a00240011503d011701820001d0721150f00b84d0b44d1101c1c240c000343d030034501d041c903400303043e40d0713002d658104980d40360a08035200c0c14a080f10004265400c41c1c0b052210500013101d4000590100c0c890342400c0c49100444000d8035039010b0101180c1a100d8580700c0081300b4001840035140ca07107001c0041001900c1c0c081207032519500f00041808407401d0b0170390660f10104091060031940c1745070742d9221910806450452a26490082c11050103200280c02040c40c3e0000c146644421340210110302080c1900b80309500c40c0040342060340080000315400c5000c0c00c007a8101e03401c0f040c0200e82503006a40d036560f0601003e8210350006020714504020414000c00c0e681400707884d47c20b845442105040d4420001c1c515180000e160080d0343c0c00f0603d0103000810cc640d800940041c10307105204c1106426600004294680400414001d0404c00305e0b072068400e0702c50702d250f01400540c40b81194000030301c0811140c005043c2680e4000703d1225190a003485451400398015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 316460656 1250 316459406 316459427
    0x50a0504050904020d020307060e0f0409050705060304080408010507050a081e0114040e0106080109030e09190f1d1c021209040507021615020105070903110d2603010515120403 77
    0x7445404100c2c3d1710341c00240b81002d0360b40711002103044031948080e1480c00b20144201c49000b0758050040d4100350b507401d0349408603400b41e1445654044040307414045170340c0c1620090b0101c080204128108808040c260360030001c04400020701c914000380f00c030f402c088000500750440c10b0180c6241e07420001180c03450203140500540265440c581d0030580310090107100d000b03041c20703000050710b00782d10f040c010700f01565203903040d0142e00d8250600c038190800196000111007040030024190003d2070801010b0300d00e01241441083c2c134040420700701d60001c14110701481c40c40c00958078100d0134a100340c2c2c40c1d20703005141542603402030000e908a810700ba0000d0381d00100d070384144d03800c0304404030030959001da081e0484a020603101e08d030042800d03024071500d40c0100d154145410300c94a141d455840160805021034050040c60b2a103000b00030301700215082020306030380599000006490400c0064009108007480744000d8080d02a05200400850320310003200094096241e4840c3c03020340310710455 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 316461906 1250 316460656 316460659
    0x10605122e060e061c031403040201210f1a010c020105090f0a180c020c0907180e1305060c181c020a0f03050c011107060c020616060e0d050a050405090402 68
    0x810508910328507003841948081c1c9000102988a801c00340c1c248007201e80d489601e1100f10740d9950b80302c0007103a0020402c110310040a141a61f5039074841c401214851141d008a41400d0011440742d0641d905540284000a6440104020005c801c424000f0348034104020f42c0d0110b503031103c8035000740d40300c0e200921039804003819076055005954040342400802d60f10100c0200c6401d041c010400055004114100700c86100508110b0b07080000114183c1c80607101c9428405800b030303181000401400d0000c0140344035000480c091501c01f1400906415004049446001c0c202c00a0500710380300b07083d514503546030383e9007044034480e44050080103000ea0503c020100c406134009001a130791440c0c0040600f5090800004a91842c5001890300400060756410f10100c00710f10306a0405c0090b4440c00c0b998a403500510440103400403a40621405001c00c001c030101c02c03c140c0c180f00c02e42d00035000180c030403001c0303e801d9010404110341034043c00703050300b00142c02000100410b160406e20700360402d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 316463156 1250 316461906 316461973
    0x1803050406030f0b0607050106060f050405031216050709020c150408030606070224090f01030513080a120515010f090f0e10081e0c100206010e0c0403140304050301060512 75
    0x7100c10003c4d40d031b0f0f00001d90449103a9100c1c1001e10540b40e210001411850729805c1050806042000007501e46c0d0b09400080b00e00b07032010031038940600005130000c981d00d4108040d110780c40e0f25000c4480c0a98000c0d000481c00d841000001c21000000070f080c50310a54101039000d00716101c1c14100020b5911401042e40d20884100400c410b501d0359640e01e2588681401c0e09650310304010701800380046000218905140c41d00b010001e5401390741401c0c059065010315225515421072030b094640103e140f2640300302c6460841048034686411a008007080340076243c141d450501040b08860220385409101c81403410f61004000e03d031521078103160004040c05e0340030360050302d501c64503141600740d100215003880e03008802e5103440340030310207201218425118442c1d010034042000e561104180304806104c036181c4001410360101d5810380c0c0185501c210414031883c0c026500d1582c03a002401a1403181d4a01640002d252500c94000c5001030070361380241c0178010701da01da0030803000c0c8804005400d800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 316464406 1250 316463156 316463171
    0x612070b0903030708040f050a141309080c0106031b0812041721130503193207090f05193605010f090b040210020307050703030908011803050406030f 66
    0xc505d10080d20203001e00a81c0304100034500801c011010003194450806840110003401a580300c1c0400c09000c281091008a4242024500900d8501c1814400c2c002c0394030b8880b01004009042102c0c1c2414034111084038081a00c4101013515072a801c0b10240c3c1c0f00100f040f0403c90f44100a002c11000c40301001581c1d08400395001e049030751140f03103c02482410b400a92802002c2c83c4c9a04840a8002a002808070305030020505a0035410390f980078000c13400082071107042100090086440c4011601c80a086000720a50341e59100d0303440c02649511800c0041040c128440352280901c2400320101c4aa401040c04800710b00402542404a00104010f205036442c1440e10b248818960103103684000e00d080c90b070030041d007121408003d0420181c01d00308500080344c402c10b825504150119840c105583c0c03802001d910b54411010000d000d8060541d0000500d0380001d0300c0011151000000c0c440d2848001038206105142100100401c20500062004500c81d40c440495080350100000340007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 316465656 1250 316464406 316464413
    0x2405040e0a0f0e010510050111010f09140d02010902030c01050a030b030708030405100806090103060209131103180a0c14040204050d080d20071e02040914060612070b09030307 77
    0x24108580307880109464031580c0403900071500c6011408100d07403000f0412801c0c0030743d20084101c0c80c2e2180e01d0401200c4154189003200c00e502c07680c0803e545036010030802000345401c04001518000032501409000c000100a600600840c05c0d416802400b51150007a803800541c1e080d0021030b0140100340d686c000510b020b4404002c500003400040009540300c624002c10003541120240801f0f04000d2410207200103919450342d89415039038014000b580303400b02c503004104220300d1215610f61050030b1180100c1c41010740d500540c06000c031640c214011f403012040040c4c0c1c82c020480001c1c420a804501080160713250000c1d00d0200c80020005460700366600700080100c00e0b0b0b011305070f903e10800141c164440c1c586100e0401545102589071010020030010004070f07010740030000d814404102e088107080110f120841441035030042041110b1a19820036541101040038030900702d00c18000401c03840d15104940420b00c0300068001d0503a1420440d841115401c1000c1d8039425201c14007203c1c001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 316466906 1250 316465656 316465679
    0x170c010e0609010518030409230106030213050402040503060a0e122814071115070b04020901060305090c040e0f010c020303220f080901090305060109020705010b030106240504 77
    0x321540000c05403810035580329030841300050b140d0080c3e002d80c40701031704e07983c0000710a5808940c01204000792068580d00305c4000000030030002000d065071003002281d1960164080c0c502d43c01e03007021140c1d01d00e0b126024031003288500c0c0142541039022a002a0107031015401c40d180d91503040341510000102101c5e103075100e421082403013061880c0070020301480011000100400c11907481c10200c40c62948000a4092181140103001c1c004500c5000115031140220300502c004001c3ca116510340203420440f21040094504901c1110840d00004840b4032a00540b402030802e00080c10780004c00c00c4c20007005000040340d0706443c1c010034000441d81c072402c1c030030340d00c0406080d0051681d9142c210070103134207288038152040d2003c0540142d60042039030f00c040610041c0d031081c0d030b5031759039800388006a9000d012540700409c6131081e000003007400c2044c1d801818025215100901411207241c08150a8a006000b50141c03802c0104519124a03c210341a07031024066081039440c160310352081001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 316468156 1250 316466906 316466921
    0x906040e25030902040b1801030308040c0503070303120f0b091602100f05090f0d1d04180302010f0c0512073b0a0506031512010b0a0f0302010813050a170c01 69
    0x483e594a40c3c14003941444d000b5800c4001084400c4482c40b41098101c0c002d286060001030100500e034400101000103e018080140900034202c2c3c00d015564a0010001d0280403040c01c00c8608080480078155603a003d51841360b85c0040030070020395120000820103000031010f0004510550101c1c0748001a03a2280100c101d01c000e801044506c0e0070024a850900310000c6c1980981c4400240c1c15242d0b8000c03c05203248034402468100146a0000113000c0d203081c40ca480b0713030b9801c200100020540c056100340f82c55510b0900a000c8401c2402040d507050040c03441204003882484d001a0013a03109a00700040740c28829401c02c0b40c1c1513218005001c070880030649009842d94001020030601c0c0442d018001000b040322828039500e018007142c0c40b0002d061140c1800f803061910381554040c1d083d0811407500d000034123480c1d4a203907036003070400c2c0781a207500c002e9021401c1080411280001d080d4254031050b00000244108141591460f0140d90a0b090800c40070000f88603c1040d010203004003071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 316469406 1250 316468156 316468231
    0x10815011209060b090106050c0a0813080f061807080316051603050a0501110c03090f03030405040e060615070308040f02040908040803190806010f110708120a02010f020906040e 78
    0x601320080d401401140c1c40107811078803d01c0010b01c44556820b00010f08022510341c401c2120340c40b103160044602c5805281e4000f000180280030010039848070018a00e40300701c488410080240c10020401a101d511030b014054840d0030400103042c15515015034008030b0741c41a422181004000340400948180b02d4000321348130341040b10303001c0602c0000d0240502010042d11190b207000f000c4a496130396403240c9000c5500501c103e012038110b5960a10030354005000c0600280400d00d00d80c40004d840d158101d950343c4c8985a40713614503044071000800d0f01d0389140c0c19110136646031a81e40710212010484001207034099111000321001a499401070001407031088005c6072100c4a00c04403242d0200182000c5082002d100c00304141607902c4460060303200e0503428150078020101203000c1c14604181c001c4070b65072060081500908c44118000c0405070210b50080040c103c560300600240e20804900e1948010103010600c214583c8410b17140d0800c82c80f03505510011000628090205504180340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 316470656 1250 316469406 316469411
    0x30409020f0703120c051206030a1b081507140c0106120f020f040b09150105071416150e090c0d050a051e06060409050603030c070311041a01081501120906 68
    0x4201030f084000400d5011003048240051740c42200c0c014502c0c09a80f070443c03042d840035000304580b134900b400040c19440e007022403819460080c852004146183d8420790030f036449000f030104d401c1c0c0d030841c501034001c01e80741d500e21030520311a0984881c40d400c141c21203c030320b540c0e2f1040090416911545607481500c50400340d41c0024881c01040000078860705824019414020084560307550580300d5a070203c1044002c192000415004035036034010000001c000c0340d0600500511054005540c00d4002103441c038a902140e150400038051443c50a801004910304007100400e40c5010400036610101400c50a0f04001860245000f80c0c3c2042e41e580340040d03511810b0215071048110205207100c4844903003107040c01c1c6203001c908507100d0b40c441c800a81c2c3e0341d200451040d0707905004440071b0300b03100001c0380c5a194403410320610201000c00218401e81c40e11043d0144100f0040c00155480e605846840d1296141c280c44041c8402c1e0144013810054000100c0104610b1441500a4503010381d000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 316471906 1250 316470656 316470667
    0x5031e070e0a061508040c0519050616300c080906030a06050a120b060d0c1505031e04050c0f030f03121501080105090c0c0102160302030304110901050a060c05030409020f 75
    0x1404c81c01c811050b00314080020390000c10011a01c1064002d085510644411040000c0121203044060031500304580c41000007850f1811001800c0035241ca2900400410960900032501d041ba8025000710281620b103032035248440a6024030b40c10900f0034000c0002038036022a2200240c0554401c80e0501c416036076842040c000e07810544d074084007074014010900d214104a442e41c40f242c03200100064410b14040c03000714104502c1824881c000c105081c0b0f40d50315580c40c55009402c4d074200711140c805d8591103103500011a0454485580529002405809071b9034201040c0004c4415100c02a0b070103109050800345407000c204001c2a003911000f00c02c160394100458044948140c1d080400e040182440044c01103030360345030b040e9403c6401c09070b0141e507a009142240c1d000e4001c4448070080c228007054a0b00c141a0003000461040d40300e01201d9406014060410003800800e01615170802d140c0507061044a001701210040140120102c138181680c0e0405a41030744d1085040a004000101b02d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 316473156 1250 316471906 316471919
    0x70626040f170a110609070b030a060306020f030411010905090a230114030c091012051002040f05120d05030c090303070c080d0914010806042a03061a0405031e070e0a06 74
    0x80c4d002c13440803201d024000504001242d0340e5101000e0103401a00c1e0380000209800ca004c550244004640c03103c8195160354491509620541003142c003590503040182c0908034541c410020102a80d400805040a94441c1303a480001403414029080b58180039070380c03410070314003230b886014000d04050b105082c400c48444145403c0803494143c450098400200707006414014515030b1003920004015180960805d06200380341420174180d00d21910710000340824031540c480800303001c3d100141c80700011079401c0380c10259a640e00014180014009002040100d403030303400104580600142102d05180342e03515200484d401c154010313a4aa4008544094500d400c1001000103100c80c044100b0940341c0000007038842035000b005640700350790b40c07012a611180e0280504d402c0f0506c622161600e800c0f500c01c05401444940250210102030303640c0c413902400802c00300c0d010b550b03002e40688a22a0241050301600303000701440845230050010110b0346402d10044c0600c00c0b600410081450341c507100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 316474406 1250 316473156 316473167
    0x20c0d0b071202070b0402040c120218010806060a0206012114031909030b04020d08040b0307080105011b05030f13121b1508070c0c0909080903070626040f170a 70
    0x2d0345019a0760050140b00007003110701200c1e80d409501a2030200762029109000c8aa60600490b0b01c00b149102089110711400400c21010744c40000b07890b440182c4c0c495404100b03a070b010380606180141c2c81031005206512100700210760300780c80e800f0300d4036442050b5658100315100800c65401554800f00b040c208912404007005081102d86c105850303028259102c2e40c003180300060002c0c1c01032035411000b40820850000f1a402084e041d8a915142d0400060043c80d0072002e1040c50700003040550b24849042c00400c0d080082ca0703000b8000d5142c00e40c0540e003844030390400d00d0000003c20300200000b440780c10203491949401e01c0380c0c04480d1000002001d100e03400ba5107801c11210000b600c40b0340d108190b0040365080d00b05c025400c0c0501314451501d06010560255041030780224206050001040320710780241840403002c030181c40c9503030f4075a00204c1d4403c0c08070a0b0203508403a2581480803241180c0d06480d0401d00030b0904000901550311094045000d5032414581580c000400c003003202ea024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 316475656 1250 316474406 316474427
    0x40605030a0515030a060b0105071e120908190f05013312030516050d020c03060a140415020706060e3304020c1501030302031b030307090b0703020c0d0b07 68
    0xf40083c26a00c5505008245d50780d2070100c1c0105816907401e42c402d140c0e80140d0070b0710a4260b00103601c000c0b0500284605a00c80054a0704561595800d070380e0f4405140220602401d60f8103540040103101e240e603d0480700080d1034901994500e540d0131210010403c00c0c081d040b011202c032a0355008090322141c1100c07840480720007610718401400d0b002d1146031070b56130f141000240c0520b006902c403600c103501039074646a2000000d0540c0f01e92140140c030310780c0206050424140032400d0711308039a59110440d0030307a4201d5a41942210503074000030b0008002c41c132180e04402c640c031001410010b99a4800c0126112900880c01024400c41048030310310b0341d503403c2c088401902c412803035013250700488107402c204071666031071143d0b03000b00f00c480e02408200050010041060010341e900d5a40e401d01944907405200803e0a285202500380d9018000008036030084c40a941c0b140c60381032505100040d240c000d03060031021401084040203550340d80da044c105e00c080c0100c030008101d050016014160340e801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 316476906 1250 316475656 316475671
    0x60a02070203122208060a0e0303040b0c0310080613021002030901170a0e03040b090102010c0804080901140c0105070906121107021003020f0c010902090c04080604060f0f02040605030a05 82
    0x401038400140c81c086000c2d20781c0e50300c88808580f101c110b0340140e403458480b4544000c0b180340f101c0001643c40f500061b00307401180303180010010408055495a180c3c03100b190042c01c41403502012a2108a40d04029548900c828415120305c1da105d00307409060490540301c130846900000c01c41c0c010342c03070442c01c41c05005410740001c51500c1170300c10019100c02444290302c80000660b82c00510744400039080855070240c00815a50340742e8803140f01c1440750300201d0007540150310380503100030303807038003c8440e54015034215540c5818400048011503240c0040401496240c0e424810700100a03001d0003180d000303000648601200a0410381c00500f8283c542d150001500c0c1004c40340114110004119207001d60151005d07a80d1290000f4250040c1c0318000c80303202052400107005070115019440021990f100300c4044d845030310f80c0c41c0c1d402001e00943c040c2401640004c00450001031035640310400c0b12010700b20201708411940706000c2241c0056011001117000001005100180b034810f0541c040c20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 316478156 1250 316476906 316476911
    0x5030d050c100902040b060706020d050609011a03250c02040c030510090b030313060809011b21110f0d05011a0403021309080d09030206070e0f041526060a 68
    0x1140724641d40c0c0030100710a001103552a603622003952180d80103070740200c401912080d07442a41c5c0c50110020b5102203c1c40031040e107000086282c2d0324000900c07504856030740b14502d42c040e000801030400c0d5800036140290005146400750000d207441c00c119580503c07141c4500082c100240103100039250303410308200805141404003e545590024000305540300f28000140748d40159002c40d1031840350b6291038100c1c148408000501c15404071740b161207148600001c0c010341035810540b4441d610103800c110041244c1ea0395500a0841c002c64040c0c0403101d8a80c08039507299480d604640c16440686082401040012605140170560040701d00412651842c000c003901c081d0601c0780c1900550000034452100050001541d40858002c074600c660030120150b903402050101c28010603c001c401c03400344c003e04000648180c012542c05058803005400e15101c02c103501d040000505c00c103600e000c14040360310000306180c03141380e500f00c0000016000d0040c00b200803c03800c0d403a154000b09010032090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 316479406 1250 316478156 316478167
    0x50f0a05040e040c21170c0307050712050d0c0f0b0a0b0927070e0703022d1b061e0601142205030d020a11010c1209060905010302090f0f0301150f05030d05 68
    0x140d20710342005071b0600c05686603440e020490743c598150300c11401c000e0541c3c03042c040c0c0414054000c0e400141c10307a1041d0100c69658441000940d14111f5044000d042d0032441ea1541c004035030030409041d407250070920300085070b00348580000c00e46070b420380d01c64047c10850042e1503c000083c141d09031030400841c4c02041c02514105a01c914220004c00d180105500481c90809500c1010b410f85201c420341101e07145050341504610f0015000401d980c1c020f1a00c10141d6002c2102c00f01d07005004002c4542d10300110281c00c00e9520080d035004d04030f81d04100101207180d000c0368070710018003c50a1000800d440000c1108008100f1b41540e0f00404c0c46038105c0d0f05404541ca07000204800c013580e12450010100c100c008c016109000001c1020380300c40c880e10240388400c0d0f403103085003003519078035101c0010913030700d4800440880c000c1014554001c080c4118a8540b441c2c41440103000010041c00402d411041e61802801c045680e4408412200060f0047c402031900740881080501c4c20f14142c0e0412 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 316480656 1250 316479406 316479413
    0x40605090a0902010207150507050d0806031915060f1a0405061204060914010f05070807090b07080f07140d0819180209010602070603150501050f0a05040e040c21 71
    0x40001c0c0203958840e54440300501164001e00400008007030b0851f0340d0060010010000d0890350002e001159540900d4650841182c024122980a848e01600900020005170301070303180b5160b031640c103886200c10240d4000d103500690103000c0103010308292405a80e46072050309900614a170098418002090005001a4450341c09649a40040d20b410780aa902c1c0d078100180140040e8102600450b02070b1042152000305410002c0001c881c0f420030003507a03035141005c4405503801d4405071b001810555041294603c6c43e0301420b440c3d80140103140c58821602c802c460f081d40562800c0f204103104481c44030032a041032100f84940010340c280506a072400c035000c000d5442003031801c036000030b6841c0741180030041c000030740403000b581c01b034018462541c503404041d5071a080380c8205c0000034201801c0180744040303e1184411100f06840303440c02c5c0403101540c450280c02c154903640400100740800241d80000c0018240a2801744040c040107030304080c084e80c0316144c0c014603800d0280485141e803000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 316481906 1250 316480656 316480669
    0xf0313090f020a1704140a110f030f100c02030903160e0a06050108010b0c0f0a05100608030708030c2d07060f05090d050306150409060f0609030c0e06040e0118020906040605 76
    0x780501351812901c40c0c1d0f81d80c5040038100382c1c0b54883d2046803144808100401004102c01940e50900700d5481e4101c14048080560390500180c03060744642100e0071896141d40c4940280341d0303540d0780340181e80c02c200f22040881d15002c82021801d0540380f40c07801c20852130b0b07810b1030002c3d005040d900c4140a000c1c100000601010130600c03032011101c2001540410010042c071030341c0c50396040030059440c000c0d80d03800d0482c0e0301c104540c1124013003403519100040b1120000708449201d80e0002c4d02c18110790b0703050000c0300300d40c000302d1206101709110078074041007030001446002d100340a1f01c0010303103030603007810a0f0044801315120265080d2070700e030500c01100400102000d1400442c0391940d42c80c0d54580c0401d0310b844c256a48a03940d0a03001c0b401040c455000e030410819106201030040340c0380e581e140c0440744035005200250030b6080701c07007040c44a003000c00c84d410f6002501800120f403081c148980f01c2d0841d004080031030210795008140b0030440c900f0ba0465034201c041141c050014905040000d00c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 316483156 1250 316481906 316481927
    0xa02210c011d04050f01031509020d1506030203060f0106030b0109080312070203090d0507080f030f07030e0a05101211040602030426030304030207060e01020a0b15030f0313090f020a 80
    0x500800752041242007800007800030310b48101400a00c844d0400ca04a42c3c004032003800704840b0764050100d01080000300788549540c180e0010901c942e1f280c038076201e0140c88010191841880c0761143e00110240c0c404110181c09688407001300000d035850100000c0844440441c03542c1001100041004250703000020390314080711405070f964194550035030507442e40c86298420354224101c8020301c030900c42e001c6030b244112510041a40c181500040f00544c892180d050100310510061011202181c400d07004903001d0000507007816078154448000401003241d2580da40d0020302c1c03440010480041070b00071b02800c55440240c1c05e00741410f1180c00780d103038000c03030003454942d8001410030a0040841a1030010344000102940d03600d040604009485494500507400811100b0040407019440040d0707503002d030341d0000b20058181c0c41d8009580c0084a44600b1154913200703c0e000000c00410500003041c1c00c1d120301c0f01e0080014500980c00e815101804040f00904e4414000321107200c1e0400101720 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 316484406 1250 316483156 316483159
    0x1150804080c0f16050f09070c1e0602280f020303010b0c0c180f0f040f0b040615090b0a050405091903091805040c24050a09030b090a02210c 62
    0xa4660100c2950780c1d182210040e041045882403014200c03600c1c1c84d8000300d00c1900c4c401e0700c203802031103102c0090003800071003070300e098001030360134003010000c601002d01c00f9072a58602d03400706010032100d0300c0e00b01c140e8209840c044c0e442540c91115815032020070503c1c0908003028100300865182c103a101944a010510a50342d4010000442d421032031003e10a054100340014203050382d00a1000d41e000a038003007156003801c1c0c4540b5801040c1c2400c1203400f07441c805c07a80b00500b0081a040742e80c410f0000311001d04200c5049485200c4103814400c03940c84400a04041a000502c00c076034070303041104960b01948060f0107249401e086c405403c1c0081850300240503070b406d0011100d9410f02c0c044034004056071000c0c070030b030b08401780b200203a0400d170300918003c030701640418101c80c0d214078925180b005800e40b1960780320a01c4441c10384e024055005411810a076003482524140c1d2500c078440c041c40101d8000e01c0d5078010030a21000c601c0e10000c10864420581c465500110000d5119981e07071040200c1075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 316485656 1250 316484406 316484423
    0xb090402010f110a0c0b18060c0c131d10050c120a05041403030103121d090403030c03021308060603101514031c030518061018021204030206090601150804 68
    0x1a43e083c0341000300c0680142c0c0b02c040030154640d5900f6940c000c0d003000b9003107090114000c445620750b14182080d228200b000102920200e62020204803040c401c036042016200e8445641a183d000882180c1d00758507400805813141d0344031403404900303c440080201510680c14010401001001c01aa5130b121001c0c640000700380d191400c3c202e4041c4409008918075100000c0007101300302815038014501e101c95200c180d2000c08070140045101900341c01035401c101940c0c00140820701c00d400074071110916003001440c0c0310700d24004c4031601c002500000361b281d01030801c1c40750354101004400d80c0c640d00c0b030b1401c000c1440c105005581c0080c161040058102c4505118503407940d052140620b0395003021594110b4050000e409406404110341d1191030340301034440a00c007243c000c95014071441d10b41d00024902401c00d460301c003610b404010800f2485509118230740e0300c050b8000c216409203020350000d000c60b03d0208078161074414141c0240c141e0b016010852014140c101c000301d60420b43c1711126 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 316486906 1250 316485656 316485677
    0xe0105010f2108070f0c060804030512070e04060f031b050904380f060d030f0f110322080a0f0b06040207020d0c170105060a0303300b040b090402010f 66
    0x802c1c10700c0208a9019100d483c0000d00b0b9000c000e91384400e030b146a8440c00004200f96aa4030b01030b5081c040803100a00403403010031500b02070007049500c03da804603040c144100a82c400390086421548603070418044003c50400c107000b441904000503c00c0c0800095a0040504100200d9500e04010b4002000c82d4018a0b94442c0781c10308410000c80303692503503a074114201c0700011703101d90504c042d2000034076822102c01040c01410000401e203005a00f42d202c001c074071030300040b0032030b43d901c03c1e06451402c02100d80c01d5050609401e100408074003030202c0c00c0ca000f03c450300403030000f0200e055011104c2544202c40620000c1c9d4542002c07002c0e1500800d021201750f507030310086800780c03080c028000d44c0001d844c8040740800c114400041d00303881420705658085541c49044030300301e40c1c4c20760f440781e441000070100300000380c40340b0030014110b10003031444010079640600210348681c43d80004800c0070340301d2240113001d0410344200d4000c400111440d0045d401c0540010301a1405d224403030b020460043c05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 316488156 1250 316486906 316486949
    0x3030c0e0910062a08040501030e0307020a0e100e090d0e0d050c0904020f130e0c100212070609080307050901020d051204030e04060506040306050604060602070315020307120606020d02010e0105010f 87
    0x29103803800c00380f800103c03282c2980c17603c081203500c039001c0d40d4086864030850b00184103001060340ca4942e40900401c403030b6402d291420404810041140e1038071740c07054002003500ca15002d203a600484902d802000b425141e0f0314064843c0a05065041c001c01c0d0860021001c40c00000c5c017100c66080690300c010481e15140041b4044824900041c1d420002100039248410300640c803002c1c50101c5a010780309405640010030021100401711b410050348010b11691412200c500100b802911401001690001d06c0e51001da09030001c5608402041c8041541e00c600e58062124495401031460318529290341c01100d5041d042020b00051300300301c1c038518002c2440c0c4841d407045000d0000100200c0d252179032480c2030000340000f1a0302c94007407800d0080c001001ca00009000054030741c02441c40d0ba0501c05036032810002d4100070441d90401006406291301418188100c1000c0c0c2110380c0079142030034200070b02074251200010000040d0780f401c801009440001490601030f6800e6803007101b5107609641 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 316489406 1250 316488156 316488197
    0x3060c0301090c032a020606040b130b13180506070810060f0905121006080c0f28060f1d0915010201060315050105090708040302060703051f0303030c0e091006 70
    0x500c100e40310350702c149240b0701c0c26000c1c01704007881455402c607606075581400b8041680c011551641d000b25104901d85500f02468201030a100350141444041710702031031249013551a003040c2ca04a01600c01500014004184001c1d03a215200b41440046030404170200c0c3c2200525118180c10024501c20030141d86209900740801840c0090a480586144030201525040c01c0049a5095450403100241c03000011030f0400c541c020060012098035411028419105006a00a008102041c09070041e40880c990300e48080c0c030507991124001107402c00301520204404c0d641e440c0141d1070041c1643c141e82c444400a91042e8081003403104a80002c00507030140000b508014001034510852080107071495004504856040321290910703141c58400780c90304070060754041c2c016001000002c050078002d0b004a40c1004c0c0d5055890b5600303c0300365520f010200a50012000642c81c2e00080a0050340321070000106071048510344541e0038514020703928082c00e4482c01c0d051260308401c0d100c0038041e54 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 316490656 1250 316489406 316489421
    0x408070b010e07020d033b06040c050f0d0f021302040305010203090a0606121106090607080a02010f0b040606080f0a11070606030605010b03040816080f0a02150603060c0301090c03 79
    0x500d00016961120a00b400e00c5004856071401031080c25643d81c2d08030312a020700a41c1030b030310325007125414259654032560b141100c1d9003200c00802160350b1014800301000a0f5216a00840f1364900351400c210401c2265080e60180034440e0310000c83e031401190390301c04121035050781215003100020780c403140340c0c0103070003554009403495201004001003042d01207071042c5070500c284000c005903034448100301540c480802c000340240b4076501004215040800c014554000020b1019013444d40d5640c030742100794401001d07100141d459680d51001e080c40381c0a04401600b04513818400c2908000008200305130061810440007401d00114140054503401180648031081c90150344150500f0403001030702c0e0350f04c011600c3e1860400005640c418a0069074092940700049914201c00340204c0c1c07440c0218604161030440d420001c04500c492103500410b0190440c0e0007034245125044807159410b6001001c0302e0284d000070013007290640c0386d4400c5a0660b0031011000440981d140320803401403224 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 316491906 1250 316490656 316490663
    0x2125050d1d0a1d060306090607050c012901080a1a01051c090c03140114040807060e0706030f110f091306050603072703020a05060901120f050405150709030b040807 72
    0x21410114100b60443c2000c2404615505024450388805051598508080b1829400c5400640100780540e10480003080102c0f110700011800055020038501d00e030700135aa0812800d9900c0440d64010b503084091190300800c3e690082000440301c00c241080b03c0e860000542c108000015034404d80440f40c0382010410840e010100189030b503d2504000d0320f8038030b00040d42c2c940f26556071030443d11814060783c00d4031010801d000b04030fa212560740e9980c3e40c109040803035049448090900d07807180e080089000900d9541d90100c0c4012052220800f141c0840840c92002941002000c01c40200c01c0700300d403102c1ca000d840401c825460072684070000e101035000103070311034000030600c0b40c40c0781d120b01d440045da0001c1c1c0c4d0211581c446038014441d40e0140b444000e41003414580100002d01e018070103020780c00c8040c1000c68a40e44500d4015003141c481c0c101814801c0d0381d8000303000500c1020480181002841611207805051410028154403c503200c020074900403000050300300038103482a5a4800e50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 316493156 1250 316491906 316491919
    0x30601030b0a031401020405090a060617090f1b040f02181504080114040b0a1503030f050c060c12010806010f0e0c0c030a0909051b04172125050d1d 65
    0x1811104c0c98081e45c09842040d01c110b081c070020448800c09881201c080f64500e4807001102c1c0c000c01329800c1000c40052007262607004080c095047c40c0010300a0022a0740740d144c5035034000485034204011a0018150750003124818002005030400580e010070304d200d011611070040c103101c43c031100c0e49842141c01c002c00075420807901046188000441074012481030005402958518442d0405c4410400340004182403545040000c2800340207503651001041c07805a24000c00f000700d10b4904081980d030b420040d180050000d4000c85881c00700c07030142008101621455250010030500031055000c1c440c5450304c4417010414500f03502044880ca602610262510303011140805000b00d60184140b0903000d080c072000860b180fa24449403810010366445841c107040c2000c45a0305550b080c41c0000e00d092040d440800312042d003001011344030440c035082c01a0f4501d01d0004141180d002245024855402d0f45a06800a040410720150f254810b181004001d009090306504c034004018441d60842c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 316494406 1250 316493156 316493183
    0x160f02030f010213090c1205071112040305010c020304060206012d03150506061c0515060f0d0e0102071e03021204080a050106050607021f0203040503150105091308030601030b0a03 79
    0x40040d006403021004c04402c14507001d82e00d10b56042501c0700c1100350000100808222030002d8511351085420031345a2510a1420000c6200240303410500401001072410128082007040802d003d0b00c26140481e00c050341c1043e01c0e0100203175480c0d03018010700c00d16401c0602443c000d14400c0c0350036001e50391000040c512899503400c006413448080404201c145041100081782424a034048a20b600e504481f81c451200c2c4401d9444000c14001c1c20501200507040019095a9a188060601281b0403c8056518802d0506c0c42d03049540d17003030000200d64014007240b8081100101c11a0242901440c1d00c8000307811841c0407410195420480070100c40c0109011504400c0040c40740c000d00d1048000f0403415840760708020a50082c810000c0d03001c4403801002c201c90381501c0c1c425409a503240101d9003429110300001c0d003000c505d001c5009074910b0300001002945000c4402980054020f807408007482900d45912001e880003c219505064031140310705816200c031100e400c000d5030800c101031080c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 316495656 1250 316494406 316494433
    0x30c150a020f070e22050c04020c030417010e0d0306080c0d1a040309050a0b04050f060a09030506040308040b0f190b060403020d05060115080c070b0a090b04030201061a0a05160f0203 80
    0x90701658240c4803080b045600c00310240c0b03004039008801e86c11000801c030350b8124000300b00c0654401102e00b840c41c0400e002c00034007030003618600c4100c41210f4001080c411840f03442140741040d8130b0030703c00405040c554208403040d0301140b0030410100c04e440d0420200104d05000d42000002884081d854500e00304000a06a22808003015190225910118036a0f2000402c1d014010b40c0103143d4401c0c1c9040c42400c0c9480d05800402119082d400c0c00d404e41980e80d11014182031f0115000d03800701d14800100410003504400d401c1e8402e82c0114001102e0800d00d0400b40c50101110101c510342e903681a80700c849a40715026600150b900825980040000307103030140e145c060138800c42e82318080d5001412400d40c01040c038148210101000681071004031f072210111840c001d400d00d02069981c0043c0c2c4081001e40e02d0b130500c82e034001c0d000492500d10744800e85c000003035140130154502c2406e00000c80416032150440308070040032114070f0720450745805c080305810100d200c000d5251181040c0c06198 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 316496906 1250 316495656 316495679
    0x50306131401020c060a020703021c05090a150f0e0f030304081c0507030f0309060908031302090f060105181507050601090e03040e07122403050606030c150a020f07 72
    0x5500c600155101040c000381c00600b81d002c0e40481c0440c68100310005020380c0065405050300c1c078020710441760410048031802c0c070810918080c940c0002c500040d1080141000b0341c290009043e50b202c1c03500c0300300741e0007402000c1e004a03403035413130800c044140410075076030b90032507944003800004050b00d6031550358100e87d591b10940848680340754040d0650519069009200b130b10101601070b100c03401503111052049005040c086d20442c5c0d442e59601c028000315107000059803040b88940c04106041d50300d4010030820a00c01050f181c0001400804c020950340d008081c0d8900844030549500310501050001700e0780d922001e02000100004904076051007000a0034504880c100c076030400205000102a03030701ca08c200d0241440b420b40c0c02d404503403003178410065054110400340c4002041c0e003142c1208801c40c10261a00600328541c00030520a00200707000f29508400200d0091816010442c01301c3c0d9199400180001143c0020611001142c024082201501c0c1a20300b62058980c40f042003280 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 316498156 1250 316496906 316496941
    0x1d01020a0e0324010509040629011101150b07030903020612041e170c1c021b0a05130c022b0f020f0606040b04020d0509010f05100303050306010c0804050306 69
    0x10910503041c0d1103100324050711240e864590b2074404102c10340e0805080c0304001e82c01807c203c44960b500d04484400c844410759202c501e410003038000c001d00c10f65800050201e42c2450811500384d03d4079108051207425002c00c07404540701841c0d0382d515920305040998842203913a01c0179402c09800101d5044840c44442f41500c240d10800401c3c502100240c0c1d0051000ca4080000b030144040c1d100c415084602a000350021075911001c036004401d004070642007666070703540204050381c0400310b411000d4540c224528020041a41c400c40700e01e2400c1c00103501e42c401d440c4a15500e0f41d5801c02030008a10074821000b060a905172900c809040c01070300e1031542e1603181e00720400070366a0007040300020700c08a80c1070f4401e1035400c0108065203840080100800040c0d0f800381d4403503800c00c00c24440c1c58007070041a01c241c01d0340000007644074038130184405540c2c4c0100202c055112880b42803000036045000c0c0c0b90400d0f000c0ca8402d24040480c68109014402e40c3c00032545807080c4010810000d00104110f803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 316499406 1250 316498156 316498159
    0x20f0102100218090f0f060d0609080d1a01020307080409020a020313080d140702010c020f1f03020c010c090302090712020d020309010e0f0105060312030a1b0519170402041d01020a0e 80
    0x2d22a075480c8001100620240c94540e60850b15001003485854001b10234010980118000a0100700a80d12440c050340102c010f900141c3d129298050302d03040c8084e55036004c0c1c0007030000d140750100716503500c0c1152050b8003458100e40d5010422030b41e041c0c400c006031045294245d07005c22441e40c551031590b035604018040c000000d0b40e407010310003482c43c9110580e901c0d5035040e1a213410700082c071f60030045a142d600401507001203450444858104a0042c100100904c6440041e9a6a0030700e6a13542950700742882c2e441072081204081005854101c403803a031082e031a00d4002d407401c031100c10ad400a8030402c82c04640660020003840300d1000c5c1907000301042e200c204c0848000552001206098980403601039030715800900c140841050688010b542c4a180550b0005440450b000a565080302034007041002400c080303560141181c100e500303044100807508052101180c070501c1c0c2460110001c0009025030b854a40c20078040070341800310101c01c2614002035440395031001c80100b0340c42c208980c1d00d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 316500656 1250 316499406 316499419
    0x32205031e07050117040618080f090108060a0f180b03010603060f051806161b06090b070503040c05060f13030b0a0b090405030a08060102160e0103020117070c020f0102100218 77
    0x2815030040b58407144040e8005d1006641c3e9407107460380f80013017041810050b4070b086032902020000c1c1001e0020015526103603646900c8002e4000010000c0200a013124000c2041c95401d000b82440c441c40c40703080b100c4140909404880a6041034060841c180c4580d07090b40c03d084001c402c220540d00101405030b0418400c102541e50300147d080c81103200101101c254115802050381d9460801e01c0a40500d00c50400702c078282c0100c0e041024071541004103481c0e240d914102c81b0200a0105022a045092031030a2800e6041ca40c8508040c8449807040074429400084e14485039006081a5078031810419844d92080d90b030303414209000c203803c982128203149450303c1c00f202460f014000a006a0f0010015030500300b1110b001d13507200714003030945811b62007641808083c2d10340c40800c00c005070010310400c3c0c0640d40355100142a403451010311004030052142009140703588050700340803140e01242d0310000074a8a0f40140c0c00c05960f0701e48507818030700015501020040c841c0c0c50010240c41a00ca5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 316501906 1250 316500656 316500659
    0x20601091103071d010e130f0606170114010c08030a0b030106080a050703060906060503030412020114030f07081f1e060305010302010206040b0c040506040e0703050117032205031e07 80
    0x880550340b204848103c0030480c91406110b0901c0d4400c0920902103042c1003900d480382046000072030258020036003c41c078039101c400280703408045001c0c1c0f500130131290402d1880c92166030710410a18805016400d0422400c40398500142c2c818040d00c4001600242e07030f2070356070916030000340242c42041419806903003041e00010b6031040000f400c0c20666000701c05068034070f085555100c0a0541c42e42d003034440586480d0007040581d014001080109180300e004240145944005090240300408000582c0014410084415000803032a584850759103003000c2550303607550541c0d0511543c4e29030845403610380d071030210310801300e0711626554070b0100b112500e4443e43c880d0101c003950790034040240140c100001080001e445884204c1d0442c6020340d1141c1001d88440114003290000d03440450151209014805c1c41038041c466140503180e01c21400c0040501c01510941e40d200e0710306400081c180002d09401c802c4c0040410001030480141607403000307440e16002c0340c4244c0e4484541040c60045180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 316503156 1250 316501906 316501931
    0x2091309210c060b030f0115140603010506090402030405250f050a14010c080405041505011e1b0203070e040c0321020c120a0c06090f05010c0b0c0c1c02060109 70
    0x103030594032103000c1e511490307542e02c1661144054403050340000c1e098071a00600c0e80045500f0300036148620b680c50030454281e07240400f02600307000b440920038040c0104100502007070315a51f044400620b000d55000d40d5a40311440c1c1186030211544110407441043c0c00c800490010035500c110807954295080402aa110300c1008041038292144401c05141480a0501940991001110076005007602030410b607491000c1400d039480030076145000500c521081c0129030b000860400d03054504034281070700e4246140301a143c40510003102115000140c410070031503504201c1d85010304440000500701e42460314203290315000c1c03808200d803900e03264405c1564090400e0981d00c5680c1c100c4d070007025201c16060600807074041d46d400382c041c24010681180085030b164040c11009128907a50303184240d207864005109410b050304070504209103642c0040108442040c0140c02403011420b1030b036186005058146041c1c2c100e65402c1d281980303251410032854000c52000e048401192050101c20300400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 316504406 1250 316503156 316503203
    0x6010f2405070f050714220905150c1306020102090102070302151c09022701031209150f110f0604171902060402040b091312090909150e01091703070302091309 70
    0x54840c0082070b601f030540c0c0c2c0c10259410001110780078030195664030780461aa0240764804071070080c0c1100000403190703104001d40910303500030880b61000314200524100003d486036200d100283c0714400346100c842803424180708031019401002100b40c1c54850041c85038026003a032800580c844d20300b003001d0003030590908003150070480c441d00041c001ca81c00d641e40e240700010598582d80c01c01207844004628504000305004100c2c00c02c1e01d464201d0701d81448004d101d1080066031540c80c2d04100380e401600507000030242d4210741c2c0b10041096003145011072020034040c0c000080c6c0c61a1140c1a00400d1035000310710300e40584d0080e64103100b15002d01c1c0500a05c820141c401c010f81c800407008000108000d03a03042c41201c0440d14106e1203066551420302c00b610700f0210300755244040016202c1564500740b02c1c7d0342c0c8400c0e00c44001e0000d45402e07260750020306d08c140701d94102c0d03400000c001615030b8072079411250400320090a046100d0b00f10340728507000b17010b6604204d8542c0c40350501c140c81402c081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 316505656 1250 316504406 316504429
    0x1401050d0519080706021b060c0a140918100f08010902010c03201b0414090c060a030207020301050a0504020f01020114072a0503070506010f2405070f050714 69
    0x4004000b40302003810080c20b0003101c140c038460340070700400300003480d20b0009144103950021482640e140d0b054080303080401c040c20f00f5042a030100026074201c1d8201c03000e440c851f60071804e503907280c00d038680c0803500c504801d40c40800d00000c02400c1024007580d61420909440004494801c181c3d1030b404490f080300e40300c000107804a4130074500722001038800e64042d0640c600b440c44000c000321300081e82c3d901d818800400c030042c403480d00d4050019030806100d1150008402107000e03980d4144040c0407070300c0e1440c00700c20030700407040080ca45000382c3c0681c04503620164007800030007440c80c0840f2800018501920704070320410100124020661050040310719091402c10032100c03d071219081a20032040241181514461071100003d2102e60034029004490044014607590012440e005041c0801600f021500300801c0000f800500c0341c05d00c9044001010125800d00510003038415600c2e4020314600038609840c00c8540707010440d0200707480d0111480024140310303191300c0754100080e48401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 316506906 1250 316505656 316505663
    0x3060816051c06020c010504030201060918020a06140f0d0c11010b090c03060f03010f020c01061205030306010c03200c0108060f06031b0f0c0318060a021e1c031401050d 74
    0x102107004070b003544010110300050780318160052406441c0c40100d806e50720103c4040c2c0150b550b4507000c0254210078001c860440c11002207001070f81d0b5295000444000c240d01408040103008074240c0c0d01d0000090856040c0c2080e514081e4983c0c9981e2902400b50054074401800184d60008030040c03244140150000360310002d0041e03480d5500d81c200e000741e0b500014160380e401070505090341c4250301d082c441c03140c2e100503005000da5100c0c00206081d095401e15440f022800031906400e60100700040700b6203403c0f0303409107020030801000381412501c610301041003202080d41c04051030307108880091f810036145021b884070100c2d13540740780c200451251110002c640007441000042d0400001d1241000310511240d406420300d600c116045000790004000b50081d80d100017400001c5807010690351980d80b0b0100e5502d0f10b0582c540e18025203070400d46609030703005c24988840a08030b0b0000d01c50341d5080b003001070701110380c1901c0400c000c01410116884140e5850040d001003400e0901e040c20b485002d40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 316508156 1250 316506906 316506919
    0xa0503060d05010b19051c0203100906060f080d0f020303060a1208071b0801050f0103020f010302071112070e0c04060903080a03090b10080607030e0c040c050f0a0306081605 76
    0x22054103206000c6140c41c0100e81035580d84070181c1c603d40e00c4603006018070151002c0030320414180014414981c1516102d00c3c603c5d00400c0b0010700580e00020017400f40c9040300c501161320ba00f685040c0019041c103030050b103c0c1c074511000c0400c003420000340d08602003c281d9110424003012480c2681c80b44026078540b500102109407e00c1900c0f91039940d1300c03030144266121403030001d554030351070548150038030001c0d00205140000c000344102406046d030000078120380301035103500d5940021610061052190f050540214020060040000e030802410320060140c610b00c008807152961910010301855045181c5003001c14511540001620300b035900d10303190742c10340b542161200d0306690850600c0501300368940031403e000608082d4800d0080c108130b450105070a062003c81411b02c14000d0054080516144071841c05807000600400031340000e540008091601c2c0c0402c07940c0c1c0c45641500485600006051008683e140d44480c040711030b0380301a40c034410002e100f052620b4910303100d1242c1c0000b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 316509406 1250 316508156 316508161
    0x41e081206040b0d21050f040b0712020f0a020d1e03080a0606030905030304260c01060603060b130e060d05120702010e09010f030b07030e01090302070f0f0308041a07081603090b0a0503 81
    0x1003105e540d80c00c0961a40c05d007242040700d68002d241041d070003504540781656010071400c1c104041300289a481185d1030010b080500002490656540224500a03104000000340d1ba07003403042c100c4140d44800240301c4d02d18403100c1c150401503d40001992007541d05454182c0009103240329100e508180d940c028085c515540f916103c6000410802e00000018801c00600a000f03060501c000c280300b01c02d03003001007a407d26256003d000c07941c541d4807030003d44000b009465400341c0d000c1801e10079520444010b11050b110000030400c00c450420f40103006125548001908082000c081d010680c0b003681c40a11000460080c8240d05d642881140c106451040d814000550b41c8011b10364011200c2c540040c4004e8900715850a40341c5052041d0003503080404140706900140a0810241c042955030700c00c0076156a443d054203201718401c01c100c000321090101c041015117030484100c2c54220360620b44507184205d0409031221904000c80200e405d101c1c0c002004102c3e8415160b405410751103c43c11a07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 316510656 1250 316509406 316509443
    0xf0105100903060f180c1a030105030a1506050409080301030606060f0c06230127020306011704080702220b0102150a15030605010f06080603010b09041e081206040b0d 73
    0x2030414805207a00c03161143c0c1ca81540408907175407401c00a002d25002c501c8246003140b0340b00011030300424202e101608100522240d200000c0c1c1c510000d51100304064a820b079980600e00078401d41c0c000d55401410440080180f05407034002d0b41c1640e0240008003c1b9a40e200b80691300e500c03010203d07801040202003c40701103195940003203040d00054000e407880060400e00c4c1407100c60b09070403407080680302e82906805840c91142e80000010291421860350500030000ba200d401c25611681b0501039143c00202005240c40590b0320740c95001d0003000a050058004205060b104000700f444d542c5440146a410361002803030b03429070103005d0940c41050315203e2124003d045082c141c1100b80364038880c0000054a60312426008220340e2480101c0d0380e042201c010b00c008000340c602d51207a8140241680c46a844140c843d0f0807079070005c0210551041c001501c00c85a00300c2d074014110203000b0a0104800051080d074a01c200c0044402704841c1850408001810110f5000036016621035410f00914 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 316511906 1250 316510656 316510661
    0x10c0905012c28060512060f030606041a040228032c031e030709050a0e070e120a11042f160b090a02090702070605030708060409120201050f010510090306 68
    0x40c544103114801041e006043c6602c064009902c000001a400580c0c48140101c0440303c64100c1d00031203220380484009000030b40e4a040150116100702e6403a40c03107400d5079640c0840708144e154049c0c0290340715585254040f0004000c02c0b403a10301854007c1e524400d20f40f1903c10390000700c0b241c0b44034030380c1c0d00e000c15100910141903403460515888100419411311080304c00f0089039107a451841640c0b03250191005240d003400e54130980c00b82104140911600603260802a404107442c68140c141d001d2520018608000f8882c0b207070301074011238000d90144601200014540c10003603c05009080b1007400c0610800d079215858410b5005040019041c0c024000080201d0b40800000510051503600cbe00c3c2d44221054902088540c01101500c0c1141090303080c0c15803144450010700700c61490080081c00c0d0b0300c0300070425005c111300b440c00500290f58035400300d035200b500110100c5041c54040c9000c6d000306400d4904074018103111000080620700b100904100419540c0c2c0c43c3d2400d882d59a51801 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 316513156 1250 316511906 316511929
    0x70f020706050d110d05040c0902160809030114041406070f0203090906010201200c070509070804110d140d02070b0408070308030a060b0a020d0807020102041223010c0905012c 77
    0x242240c03107000d40f0080440075401741c044045545400501c0341441d00e40602031441c1580100045401802050103d5802c8225150740507044001a5a14a51200064010070056030b034082d440f240e01d01840b0902101e0300100c3d00c12240341e000c584c02c3d03491340f00058074a13102c05103a040060344100018201400c10300522900110180004500c00701c01d847d41d5044090141103140c0107c101040c11030f2144810000c4000421040c1c03400000c0b41004440100301400040c40940401d001c007880c1f1040b52100100511465040741074400750a0003c04001c0d03e40314201c0072000140708020011480800c4402240c084420700030003010303100c2ca1035030750051507007008014072882039640600043d0041010010301c08641c2c00d6001d490306682c074603030151000384068480340031684103006c24840035840c20585c004090b08585549100c2c2854400c14410200ca850810060b5007047d403a01e03c226048800b01080c0d4001344c0340c44a406101809610b10941e11980208850f4201034108807941081d01c030010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 316514406 1250 316513156 316513177
    0x1501051f0e130906050c030601050421120807020c0a051f03060f0e1b030402030604030509030c030a140f010912030e0a0f030206010303080a021c0e030c0105040b070305070f02070605 80
    0x920072074800000b9120310008039a801020b0701d400901d0200b000521600d544220703c414080d04609003030000074a0b9004500454400004403030ad628411080e41685800503544001c3e07083e80d80c2e602d10bd00500b40b141c1a5148005840b9250740c0369444d1400320311250a6030401740c24130549140e4404244c02d10888624070809240c0c0e21440803c000d001d4000001c041c0c943d102c80c2030f55508101e1210507845000805001d1007420a1080c040103071341c04a103158220340c15140c035030b40302c2480340006800c04620341e10003685845021961030402001c1c0e521801e402c3c5c0c410b4240c030514168041c001d803d81e0800da600600c0b0294500800700064000d620005500049504a1f0308441c0690340303e0038140d60286050300564010340041041580c0441c185500400c0400150b0514091703e141d400b0303408030310325442802500c5000c0150101d40130416200f092032004003d1281e81800c0c05c06909105081d100e56000904045c001010540a2211105c0f05405603000b44101ca02d008001c40c1c803a00055180b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 316515656 1250 316514406 316514417
    0x109030503030c070c061d0d030302120f0402150c34180507141903020c01140f07020d0918090602030a1a0f100311040305030a020f1501051f 62
    0x11000c90030800c0034521400580b07009036500d0169041410404103668061000c004032100c0111241c14244c0c05000140b5054401024041075850203a0103400f03500084840c3d0b04540c1c041020211014486500460090310709000740e884d007120191803403146a00c20640c0350b00030004412109030228410b80c5110a1100441c842000c4800c15075a01c2600c1d484201c0c0441c0c404c0f140d440104d181e110f10358001090f4103040071580441400758031507005407204c0b400024412801f000c2858000e4040322903c5000e20001c05c040744100030540b200580554044c80003d02400c001040240000380703445140919488184c00686001180613601c07011000441c10381e03880e030035080c0001e03c99001942c0162612600400e907a400b4080751003205043c4c041a5214032128411280c00762582170300b84188003203034174000c40da51104a1017079006205592005100340700000d6804502e43c2d0114107004090b04075025900c00e000404c030000101102030044c503500890b59055502d43d500d504c81c0c018544005814030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 316516906 1250 316515656 316515659
    0x603060609090907140a0e0a1518020a0801050414180a1203051e10050111070e041a0a020c070e070309120816031103061207080a03051e0702090c090109 67
    0x2c6661440306852120559120110500501001510380741588400b96004004503203403480703030400782c68060007520003030369110340721402e81c0da507052240041d10101401401c852500320020000b58081c140c18000640110b0010900307250602401041d844510741c5061326440315030a050104a50a07104c09442c412034800c0c000152580551550800719a1000207003480d2818050034600c0000342c0041520100340f080084003007642030720130140e071030038030b402c0003449504641c480c81c2c00000c1d00140f039010221000c000402c0f0790703240741c100b403040b00c140141d070745d40c8035600004264050004654400c0d00044c60900a26856040b081da120801e840c0110b007503080303501c5400400041c5042000018400003c01940503000d00d000004840705140421035018403601d200e5280c000901110f01c540f200301a035000342c07103080124001502a036815181c190720245000340995110f813003900748052010004080000f4070005443d406a005000d10f0625520046220320591289410b030b030500a01600 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 316518156 1250 316516906 316516909
    0xa1701080c060c03250309050924150c0606030708150112020402040b07030924090b09150301060306051e1c1b0303021f0516140910020a060c08010609050603060609 72
    0x3510b0502010f80000514a05c4803401c00602444450700418000c92010f41446030b070080b60895083e580c0c003141200c02d003a904a0b4002160002d001c0000c2103a40e0000c6480c2c00120004103810340104001c40c1120790842e52074518a888034964900c841d0803e044030b0042040c1c1d0a11140f0b00c141074402400145010f0302c941341c0380e0140d0030880040e0001412910b040c4000507001280041c00702e40005a081c1c0360b8010303c0024191030700d60152241c0c2c20b10100c5c00d4426602c1d6006144407481003140019220341e110803008000348481d1142d20700c10402300890f181d04a000046034001d6810191403440c040340381490296541d0303240d00048900c0c260131107524040d001e41ea80c01708081c0d44070380c0c064201940c158620640a04811060040c1c1602d058140101c6c541c5d2540d1010032000c0504200c95611042c07100b000040c0a00002c0c10380200b030440e00b0100d05079000c180d0058241c85800e00300844c020622044070003000900503140480c0b0203031400e101d9071600a0141d0b030700040080c04145400c41050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 316519406 1250 316518156 316518187
    0x10312080a11120f0c2706090406291801110708030c0a0213020f03281b0810060518030106031a180d05190e0d080a1701080c060c03 58
    0x110441d5083c1008010300c14a0384507404019000080668014142910080b1740501c0d00c450354200c1c18034202c800f1141c6596207588080d1032011500030801c01440b90703207240041c000052003807200c42180f00328205680c070403104000d5070041c026410000110300801401507510045050a94a0601c5500c1c40020340d00b404100400c65986940c005d009103002a02c10f04c40007044111100030368a00500c0a034001d007803404192603103c0d21500d1031102d246d0f094204440302d1240542140609810b114200042042c0e00e0b6440c40c1000c0700384d1342c043c11a40c2d100d00700d0201108a00800d00060b5040003001044031407032034130100c5244020b0002034619039a64501c00c03080380800021020170318a00030070442030180829061040c1c5020054280303010f0380900100540f0070100703070340304407550340c105440b04511404500c880c001d0040d0451078141d5140c14000400c0d0030030511400000c00341c240d109900640c0604050403205c3c003600604a82e5104410420680c0005640d05050320042c40541d040141d0b80c07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 316520656 1250 316519406 316519417
    0xa0c020d20040b01021903051308060c18040b010c020f1504080a0201021204060807080c07060e060402090115021905010e06070306090501140f0409022421010312080a11 74
    0x8803020010700c00358002d0205441c5041070180c1075400581c0003006032007404034820400caa141c034000d0381e00c082c0100c01401d042e0454020310004e119040c2080201c940c40c40c01026404180300480ba0740d181003800b0401514406840700c1e000582c02d40f840c2e0010b003000b184100c04020000c103829070341d03641102c5410054209a21100890b0303c1030b09000107658041c800b200301c0e2080042401e01e410b04240c0042d11005c800761070801004007950008600307132807180566030125400601408441f074040b13400f580d41c080039982030b40714040c440700006418010040540c003214550b0041c000c291042a03895201c401500750545095403142c9100c05806c0d414030140e8444c620680b400074480342040c003524210355050b084101c9004c07455214003480d0707070703540c0b5005083c00c0121400300d00c07440c0e6840420844441100041540000c0016000d01500d840e000f078803885d410050f03013480e40b044c1a034100c1600c0e202803101602400c600d400721014039100d002c950381e12500c0882c0114241000d41018946580039 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 316521906 1250 316520656 316520693
    0x421020601051302030912070204020f0a0509192d08060f040b1e042a0b0405120111160309080303010f06020105150109050d05010f06080c0102210a0c020d 68
    0x1180180141e00d0060800080107001883c210b05600d0040d0000c0da55a1034062042104000480c0160443d91180c045580490000c45100c0e219103403040041c3c0250485003030340c1e118a038000d18040d208030b501c400351400c950362081c89d045e2407c582007041202c2c0c6142c0810a640078400000071500500802119000385650b041138030141c50241441c4000100c050700580c3d401c441c02e9642d400e411b103000e410941041c0c014000c15005035450095003040800341c841400214081c000001783c00f040c0d200640102c60050310300083ea0702c2030b40303541c500300c641c80c4201007411402401314020003880181076840c0e580c071a00b007105c1c00a071100240c0d89190400d034001c410342c03c8055803d000c555030a0048c250032010002038019040480380021f88001c04038010540101d01780e038106804d018094010006514446104001b255280d02100ea1034011061403c1d001d40700f1544a4140c030020b46240342d1042e0707080e032101d070b080142c880c400f1190620215000d9038040c402c1003a00c0040360010078180c128130382 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 316523156 1250 316521906 316521913
    0x51b070b0c060f04020d080a0309120f0e06070203191401020325080f0105100201020409090c0303020106050a0b09040c0c240c0504050904081303080a050c100501080312042102 77
    0x10705801d21890018020416200c60344000c0a0000684510680c0011543d00041d60754484d03080c0d510840080050321805000c0c801c809080c660007a030821910301c0b60004aa0302c2c540c40050000034444d40e407080740d81c000c0d00759005400518a41908408904040784214800a811800308406a081e600151480952100042074925842c6600004d90950009a041a00c050315003000c08550000c0140724203802184522540b0310000d1003035040b1005007400d15000c21008a4500304030341d00d20018041140590302e800c50105031403420480d440111000490b00070f292a1924050101504001000c0030501040703294280010700a09071a0074070055103c4090026000e1180751025681502c8c0da02c405c1c4442000107001300d0b00c560440c15446a04000840e681d03543d41c0c0a060940d0760b403580090000d031008611920f281c2e80c000014001c154402c01141c40c900f8541e4444001c44000380720301081688104401e241800c00188001d0b4000e028040c0c84001d2801c41401c520102c0030402d03038000681 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 316524406 1250 316523156 316523167
    0xa03110a0807080a050105090a0e100c2601080d030b030c0409030c0b0c03060102030904051b0307050c06060a0f091e0e0102070b180a0f081c0f0b0d12051b070b 70
    0xa60043c14143d104510880510042d45000007042544002900603001c0f1611082e000100c104100700313007840ca034804642040020301070342e030080c0010442080400042008046403500c503491031240b0381aa02d80a01505c2c81c141040c80c04e50082c5004007030786405015441d039510240d980c920880c0750380c81c00707601d5803d10400c103880c01c44075211008103026101a82031042c8411360340d000042c2da80c842c60603280010305481e5010043c0310078584117101101103034000100110141d0000187c00034070f118000311412a01e404080068159407070080a038000b880c5c28040004140c0380e04542c0030726041803030a01540300c00a9001050300c000e681d9400c040e030340000d141b0301001007041f0819800a400c21074030200705125040c841d194410088003030f00303403d04418280c2c10300045008486440100c443e155100401c075002c0341c0b0141c10b500005443c514607040300740050b41424600c061100d6440002e407407120000d10020782d85600f10381c00d0001061400300551242c100c2c00c0001a0241007050176194581 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 316525656 1250 316524406 316524421
    0xe0d050309010c110d0c02131803080108010e030706020a030b040c0509010906140d1d0307030822260702030102040f030b280209060904090b090d02210a03110a08 71
    0x1224083d21038001c00c140c0c41e500622003500801d4003440c03605246800280181c081c0001102402550600800540384c8201d1112465a070310355050054031170348443c8800d80c0d9032400c2500700c8510400346a00703174104000e000c00094a9078002d101124444c100040e403d82d06601044c11070351051100004a01c000584180f2582c00c070503684018840d514006002045c080706204190007089064008035440320f00c10720300c1c0d5000000d008121056031080703a0b00c540e62030400606a1000742c56031103400d80340030b03c40c2a64080d0414441c2940360404c05c0c3d0014984801d440701d0000308480a040ca03050428412040142d40a00003040100001c03110029428154104040f0707060010300454400c084034242004030074032241271101c455111601c0144c4645031b00c000300e4070900c62104444e901034500b541e10408c014041802ca4054809002120562881e40740c00340d0303036400c0d50301040200100d007131034918658528200170017400100e032401203407065825402c3c10003600583c0d40c1b680407641180401c0480e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 316526906 1250 316525656 316525661
    0xf21040501110408071e0b0307050d0c08040b04020f03070b0c010504060b040e070b0904110c032a1009080d0c080708070516061802062a0604050606130e0d05030901 72
    0x12842e0b00310405140a00c0c0c65502651002c007441400c0302420880912540342c882c10f017442c8000c0c2600748071103507689440300380204140e00080c00300e4522490228502e10051088400522a0b035011340e04010948841d020032080360a103d1007554944281c1e800801c440c1c00c178102030080306038040c001140c03d0501e07251420aa400c8101d41d180103902c0c01ca81e0032401d40c4001340fa8001c03102809000c41d43c54041d0800704e406000c80207a000c417000d10008101510100010050800c0d101018940041d40101c4c00c08400d1034506010148155000c0b104a1091b80700340d900c49100c503842014460320780342c0c0784c2141c0c0c1e047d541120103840c04110f4901c10400d8003074020840c568803451030b140c400d14007490341414039600003000701c016103010b607071700a6041c040d0300020b54502202e4005241c0c1e03840b182d94000a41c5203200305250280c969614480d040a1180d001680600640e4450050010303a900c42003809040701d2010f000c01a040c1d1074611410f1810814041703034043c00d105550307184e66171a1040c1e03224207 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 316528156 1250 316526906 316526921
    0x2010c0201140906012c010b04090e0106030b1803091f0f021203150f03011b021605090403030209030a06020706060509060118050907030204030b010803041d09030904020f21040501 79
    0x8440c0c01c1c2d40402628540200d0f070b142c191040304825501e806e01003189090b00111000a010b00c1d00071141c004505c5030a0701e800350003201c516070802c0c085002d6500c901c80c20b0b1455031000410300e541c81000315a180c14003090100f00141c505044906100441c00003440424130b50003110b446c0039a0780b4030b018030030f5072100c03041a5041050000701070514241207018a5444018204140007550340b00a400d01c1c0c1c2d420a9088010030024020301010141201345d4034040c214803201d4015100300c04048032020801074141d8104c880060000040c0d66131600d01780c020398030800303005505006091360301e00000c0851000e84640c900a0038001380341070a24052142c520f00291502d8188004081140c51007801c00380500103507071080d2520840d9440e8044250040e01654200400c22080000080b07107404000015008443d00321001c4102e980410b00031096004083d2282069030b082040009060300742a0020700ca01704400c002c44c1d03d044030328445120300c10350001c18801000704060600090140034040c1e000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 316529406 1250 316528156 316528181
    0xe0f03010908070c050904050307030f090e090d02010c020d120b040209120a05071a07030e130e0c0405070504050102061f12120210230603030712180603050601050a0503151002010c0201 81
    0x200c1c0e0342007903108c4079944e0090400003002c000084080e0b0301076611903081c84004000c00c2e001c0c5407032400c0128400e500d44146400f02d9006601e80280001c100384002082e1940c0c0c0c00a403940c0000c035641ea410140502001c0043c1c0ea049074007000301c03c030145c613408104181000c84401900000510f481c0c140d007441069400309100c1d0740311342014103040c5031002c11070b800c3da40e00d8107100c0c00c5180d0350000706180e0307802c3c00c0240c41c4003440c04406c0030101201099507060080212020001c96070760500c240e48034001d0780103c0e4010f81c001d4000440310b1854440e0201c2290f4600c03c0c00c0c0c03065a48507140f1403501001d10046842e840c0c9100c040c01519010081c8400f5945400d509000001c036104064810b01035181e1088034001014010a059450a0045880395a0030030725026040282030006441c2e040074101c05a2800c9500c43c0000e410343c03107442505c1c02100142d482c94542221844115280d8101411080c1d54884e94294841030b5036a001c0c0c912013209403600040354480004d000642100c183c01c8114 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 316530656 1250 316529406 316529419
    0x601180b130e010308311202040605090a0608150c030106080a0e0d2a1101050d0e0607080702070e0403080a0209370e040b0c0c160b0d0606050a0f0e0f03010908070c05 73
    0xa00b07004107031400341954000d01d940b000e1f404a500024000d0401ca80c420303500001050107006031070f441c0c0c5d0030190584480b441200c405c60100c4a0500d160001120305800200041c8010301240784503181c1290415007a034030200e040d180f01441c4608002202c05e03540041104540084100d0b14042840c9211000c40300b02c00030350030f07150348910200c0c01450806038104440000c45200c80304003640039010300c480800482c1d40341d250200018003405029a500c00240c13088241c001184880d403c44144982c3d0301d55128110341e241d40444102940051607030692102106c2410300d050105002e40030100d114114054103e8241d1105903091010540c00004048894400304000319164001c0c01d50002094114030340d83d80b0034004030b6401d100080d040d00203038000c0309800080b4502c07490084c1c1103030404031404002080d5036100560322403007003001d6180031400150710400b003640201450044c0c90350180c00c0d10540c0f40c000c00001e08440f602c1d03604a4800f0004240d1100703004050700800050301054800c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 316531906 1250 316530656 316530727
    0x712060e04121103040b030108060615270d0204020d0f1b0509060a09170f0c04061508280207110d02031b030a140f060601180b130e010308 61
    0x10024100c5403400b104050196460218958040800c00c0760000c061801441c1d07140d58503621000d88400042e80c0d40c13071040b28000c80308100142c4190890311084e028440c550010402c0c2030180365201c0ba46110070303601409000c10b01000d6200c0d4002850000e0120b240060a4507621031594101c5400c1c0100702000000303032504e00c54141e00041140c0e08000125845926219a100c080340c69200d1340e000340c0c084031030f800103c881b5040005440d58070341880c0419200108956000d02c0211400c0b4842c08400000b6a1a200d440d01d014001e22504a00d01180003015104054103040c1d20001c0c170031301e041803194006141c400b441070174002c242e80c0c0081100e00140b001d040d600040c0d23881100c1c0520842801164203100043d940402c4000f4015511440b41e101101d003660003507440c0e401c61025442c0c01c0c064400040c071103600c07419096210a1300740d140395003400e040c041541c4098104840325100b5a800d0030002c904400c1e90006a40214415007005564042c0c481030b484c22940b83c0240c076080ca0000c1c886 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 316533156 1250 316531906 316531913
    0x5010507020c0d0b0a06170d032405010c0f02031c0801090603121b0f0305030a0f090c0603020c0f01051003052b1d0d03030605040c020f0613030c08030712060e04 71
    0x26000d40f02d81c116400050300d403542c20000c0c000742003d0b8072072440044031030030761244d418001c15107820780f4903243c4040010004801c50000300d8450920049650802d681e030501041d03001c0c030700403a2007038042c3d110381081e036a890380460b241058543e5200d09000303443e481040955405800c0602400006800340015447c0d40d540308d000300d40d050195000d00c40810340035040408030004209009405c504044402c0d544c0c0d042c040c10640c030a5807291511820250200c10403801e40c098201c500764428030350364110b45004000c50094121740303c051170034040c40521a030511030034003900340100742c03100c0d500c0c003007514600d4480d00e02303110b08424890000349a0444481104461001e0001c0c00c124207011542242d9100c1090090030400c0032990300c4106150300405050745688581c0903030302c00f510100b01c0103540700d1003660f540e00015401521688884000352040040002d00903d980c03203420240041d09203561441d050360411980c0e100001c600c150781711518046405144000d041c200c1e45294242407544 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 316534406 1250 316533156 316533169
    0x1009060b10111b010215040c0509070e09070810080f06060f01090608040f0201141207030c1b200d0303020d06090e1005041b2d0506030a0908041a030405010507020c 72
    0xa0100c10340d8500c1c6150545d00a000c500d20b910106645035816290601c1c0020000c55203009890082e880c02c00080c8505002d800c2c94617a0b0040103140103008d594000d421941c1c07600c000e110070165011400300107041d0078100700d842e0310b0b01d5071440079000b00e15000e0103000e03001004925081c100444000e0801000e5003000a00e81c00c0340c2c002d84010385071005400142c2d89548410704040e840240000e45e40540f800030340400c0d00170100c554041c4022040458200d41c401c820000c01400c0f03a1042c4030000000c0c1001010207142c0000342c041c041032042240004021100c1544183c0100e600010341c103031141a684500400340c0321140c8100100558240d481c1c0e62440001d40b100b1202d5503070310100701480300d8114000100d5014294912110b5118031140751624000018034440d484c514100c410904c40c0104e50303074141c540c040c08039801c590b00d1017004005801c0e80142502c01003c10400400c009484000c2d104003840c691501780e549003418605036017100c400400580854004038085003a039175801 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 316535656 1250 316534406 316534423
    0x51006030c05070b010909050d02010c021002090a09090c0911040608010e0402040902030d020c18070c170f13180e0d0309031e0206041718121009060b1011 68
    0x3440d001805406421007580c140c0305444000d4107000407100000782c0d411041d007203050400d02c0b80c1c0c155500c0100180c4264241c0e80b004c0245400b607000224440385040440d03010305118400100708519032640e4109041c101e0350070b68010f42d241c40001c0d40a011489060245450302d0b0107400180780f409140041c01001d100040c02040700c5000e004004c6815503845400c10000c8035002070680e02d03040034071180655200108040607005d605201003005812201104a520800702a02d505451050a660324071401c4901e840000c8151000d1207490746003a18407018080f20000211003040c001d0078810134a2410230801d21707041440e814551f0881c0202004136403900d001e14141000b1901403400c1c5810b541c00528403903010040c081190a60120301e90010750640074600410f1250300301e910088000186210f040985a1000e05002c41c080071803c0210403442044e0440040d50030803004e060b0040309540a02c03000350348607902c1d0032640b94140707440000340003055160b0600d074907800400100103440318a43d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 316536906 1250 316535656 316535669
    0x20f0103050a1401081c05040e070e061e18030102090a090f0204050619180b12042f03060105061611040e0a0302030d050708010e18030405030f070305100510 69
    0x1c80022481d002c1e11a0030142e4860300380c0e00007214541e103800f98190b03074450070b60158510300c2240504088050044003243d06031511000202d00c982d03500346050701c24400510040350860740820031a08580613004000341d10b9240c001040d641e840c1d2041c02d800b034000078841c40e60f201c0c0e4170400c50103406a0380d50089404546450b18082413205007a06200c0c000d00640d4409500300e04001100185800100300c40354102c0141d48407461489800d0b0322607020003a080c06500950901000382074640c21541c400b0741e81c0244907180d142280d42414007a1364004881c401c02d0655030248000300081480d0622815024160a0380d00900b00a40d1b500018444410010f01410418160b00f520981d5151508410b0001061504440f00b00160740b43c025580c0d80114071000750300349007601003007a062240011034103d0310b1a036101e0300c080e00c42c0d1200b090981c0d0380d40c6008629100420001031142c0781807148141c0740c070705000646149807442c03c000b0b0418520022010005280c5020003940034030442810058411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 316538156 1250 316536906 316536911
    0x110a03090503131d010b072a090e150a1a0103090206070f1b0506120f0601020a14010204060201060b0c0d0c0516141c0203190804030b01090501051c020f0103 69
    0x80d0300302030381188a208400c411080e050000800e078800030044140024104c0410b81400fa0f81c4c0c0c00303240300789020b00000108484800400c0d0381c400941881816400e403007820340102d8440d500c007900c41c12201d020243d10075070740040c02400e180131165440c01c1d92190301d000c4144441c0d00030401096140a140140505260341c2e400c403103055407108019140030b980d0058203254116034600b00010071088080c45001c42c07000c00c06000c2482d0502d001600c0c0b6840140e0480c3c402c540314031a01c041e10000080ca030b00d04502c41c101c140b001140401083c05184d445e4100016559401c00c00002d0a58410b41c01c1000840c2d820002c036442c402c0000360a148240007840e007000c0d4000f0b01d1030304d58204050702031012140d141c5103601165020a8030a06004203500302c0e00002403900e2078000c0c240c00482c1c498041c1d45078016609200350142001d0200c4a541e1088108914243e01d0f07a6858200c0750702030700700400c904d40d903038018001400c0c15011502c944190742043c4a5180071a4000396140c0028220702d0304140c1c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 316539406 1250 316538156 316538171
    0x18060c0706021306080402121203010b0903011b05180901030203032d040906090509190b0a0e0f0a03030b0a0e040615171b12030306041d060a050f0703110a03 69
    0x1107a5040c0c94498425404015802e55540030007040c4190548040e441065020f04c400121500007078004003400b18031440300d042da880c003024050141c0007400080d07015501c490000760003124021501031000342d19140e064551910f0b00ac821112040c8400c001d0044021000600243e035001064a26041c03503034112102c400b0301072034810080c506650030b210840d07001003408101d4510301d4100038103071040c21100700311a0b511000280d945510010840d1030074400001d0b060b010940d01d000b1140e2020458801103407444500411900d082c0e07900004401382d8004403030036010550b00d0300074845000c2c81140c0c18500346082c001c05480b241400761008160b59900c2004048014000c4031510040207401e0a800c0180c0c4030640c15038a800500144440329007480c110440c1615110901d400305156100040d030450351060107001c02054211a6056101c801400200e44140200540c40c40380c078001d540407844d81042c0d03410060350368003e8100c8041c981403c0c01110b03c02c000c1001d45042d0305c00c510b070204204 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 316540656 1250 316539406 316539413
    0x615141c0c060206090d2a031e0801030b060301090203030a05130e1e010515040303120213081501060c020904120e03030a0e011202070c0b030711010203010f0303020618060c07 77
    0x2509118014000300401c200000d85a0300429090303c18003418080c0c43c01c1184640049a551000f501148843e8180d001158001546181e41200652003401e00d01c00c030f1218031203001e1100800c40000030001d00e03000010310810880112070794100744141e00074080e01c10f141d40025100d0003800c2500081203000f103140b1402c891600c0000c00208880c0a081242d81402090080f00c003d2840c00790340329030f8603c8000105424019219884d010b00203603590b04050035690225503001d0104100c03651141c00b8130019992803411360040380102410f200609558440340b0b8940130604050340500280104404e5240140c2c403221b079144d1707000c0c1d48258540c0d030100c43c4c1d210640f071541c0b00d00c401c00d4043c0720114207948455000b084a09411400f6203803c02894000300902c4264400e070b0034028000c00407002c04100300d2800601035a0080302c03070304140e000000045100c070f0890b0000d034007075440c1842d042403c1003459010f0000075001a48000e2000d520340d180072260717540c0d52018042441c035810005455050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 316541906 1250 316540656 316540699
    0x801060e0c03041b1403190c18110f120106020a0f0b0c0d0504060e210d0c11030a1718070b16080d050105010206070903030e09180a050604061514 64
    0x8044e14564210b11460726402503212440c94030410760300070b11031400304884141ca42042201c5860707000c6405203000e17080c80300341041d0302903440510840640783c2603426207800426000d0420b000740054515101c2d0143c0b40008002d0406a0110083d0340200e0010700c04585c008a481035103a400410300401d035103504800128a20485140f1601603207003000344010840c2035041010340b002d000e4108c49190085005e40781000080158290f2092420001400d00c90300350b0b000169280075905101101b1118010794a06561090720701c0000103200d030600382c03002d4460341c04007500103504100b070094460440403080c2d030304e80c3c4034002d8400d8001d006c05c28020b494004c441584883c2d500409260700d807201e403190407010308001e010b10303400b6001d480d0010310034622035825841240d8056031810b110007031803400c1c00000b4002800c03103141081d04001c03520058404200c0305801500c984000d104500c0e05041401c101c1c0c4c132004e244504444810030400030300711802c44c111414081241e190001e0810071969145 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 316543156 1250 316541906 316541933
    0xc0c0306020a090513020405060715060e040c1503111b03040504181a0702070e0402010932031b061602040e031806070c0b0d0603060e0a0c0801060e0c0304 68
    0x2840d0300000d031116a082d48008200c08440090314482d40c0d045d400d040301c000303a020768000c0304d8000000344100000f140b1202400c92144101c000c0015040d9200c412000d5000301c1110309885030407140008001c070f031425040c1a5030400091600700009075070b4904000c0d1034802c0c0100d8140100007004091001c2d0014412600200070042040011540030b20181010f0031030780000380c07031000c403507c560020002110800744c42070320f481c2d0143c001107042c1884035444a40c0600107034100218039074085184c070303005602041604080d005214950800c9400e18804e4101042198003079000000c0c0c0d1615810b140c0e03140c5007450000c4440c50703112034450341080e9a044d424000607600600f07080011210b500c0c0400208049603039001d40200032141c1d40c0c1030055038805d01000038484640e8901c1040b04070803003405001c0705111a80c0c04140c0c2c81da80c5c3c4440782600d00d0f00031540f205030068840041049645150030009142030070080c050035150461100080d50000c1901501c03a1780040014100080c4606500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 316544406 1250 316543156 316543163
    0x3020709020a0e01021b010e060f041a04091b0210180f0b0403081005030a14030c0f0105151206060609130203130b01080105161b0204110304032d0c0c03 67
    0x19242c204040300180303100c10803400c032405402081a400d100300103001c041d01c3d2480c010b8540700c40129110082c0200d903071000100e4a01c1403810b00c804110440d03000c113000341d44c0c01410041c60b20b413410718241c1000c4500040d40c007100c02c0010704001d0304542e0023044a051074004004006001682500244040c203400b00008040c005d0f800d900700c0411400741c0742a8080e500030354030b09505507035902d1080c0d10028140100d40d40342e4070294075440092010600c2004070380542c803d4138108031600104504e02170540714816682d9448a0402004054444035810800d804494120b17102e5a0f81001035228003020b40054020030000829058944070118219400502e1b100115540d141c41c202e40c95036030108000071107480700340e13500000d2210414000c281c000d409041010045108015058440411403644048105815800700015955900c42c60303805030700910003a0342e2072425260007030903410021404040042d2040d5003010380c0c07020103018096030045052071600340156040030039101c40d0361307403004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 316545656 1250 316544406 316544411
    0xa0b030a080d0504051203091c09030b1608090309012316060b090a02090f01080613090302030c0d17041104330504020f160609060c020f0d0c170703020709 68
    0x300080c00656000a104e0f174090410b44540784900320015000d880103170342040e40e640c4a51003002e00300d00d11003912201c1c00c5042c2030041d801a0b80355a1355031180b0703044030700c540b41110080d079142000760880d206961280f00781001d10301c0c045010002804100307251050440d00b2243d00e004601745000b0a089030054122618020080071842c60610050a0031041140c0200b0140c1c020464151640c001e840205000500504421480000440c4c00c4240248019401443d0b0b0381c1e00c2c0300c800c9092090700b0016019030301555541c0080c03807080380380c600340f00f8201c02001403c80c00f079030120b014044a42c1e0080d0744000b40740d45c00b1110000040192401864140d1340b110080c48041d035110b104c08051050384020a544050960f9440c2044200d009603010400702c440c04100c1400d160320a14111002c4510412000801c8221901d660301110380149148016901004810a07400c4041051940d403444506d0800d082d0b403002d40d80c808084107100d006a4010f032001c5040c00805000344000405002c0c8400c08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 316546762 1106 316545656 316545667
    0xf160210060f060806066301030e06010909060e060705030103031b0507051318111005091c05030f0403060209040e150a0b030a08 57
    0x1000440c00364011040c5a001203214000140c4110640782c032805040c950050000500540500e1090a05100307501500e1050303810600000c0049010754001a680103d240b040758442d00c0b0f4000340b112401c82c180f5410308652107134282107440b0b2100704000040d0401903003198420150707035005800c450018443c041268210740c0c151486820000380010510310050b0400078151a14000100000010820b05510640303244810b090010f0310b4003290b4156a4803036a60396a0b10445028605101c005000f00e8160b03400b2180d80c8929240c0802e002c01d00b0310b40704101802d0540d24500c07030100740320140c4043d0f1060041d0783c0c41050144c1740403001e2040c0f810000d1500c4100504840300c2c4010404084c6102010703001d00001d6110740c0e07026840300780d01002c000903100c200f80d003640300d544480300d440f030340daa91f290215401020074000082c464907140082800c01001c500301a0045100094 = true := by decide +kernel

theorem cover : BRFrame.Cov 316366906 316546762 := by
  have h0 := BRFrame.cov_init 316366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 316366906 ≤ n) (h2 : n < 316546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
