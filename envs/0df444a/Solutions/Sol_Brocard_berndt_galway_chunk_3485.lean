-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3485
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:48:04.35429+00:00
-- url     : https://prove2.me/submissions/2852bc1b-cce0-4da9-8945-b448a2ef9cfe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 626618705 ≤ n < 626798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 626619955 1250 626618705 626618723
    0x1801060309060209040603050c1201020304050318060c010e100f150909020a030b0f0703050906071e020102072010050f09010834030b01020c03150a180b04021003090f 73
    0x250419030081d1060000c485c0d005840d041c0e002081c84000301309502e05407001ca460844868000d28414240d0100b507c02500b1900b04015a61100d80c100e41c540b5104000600800e0030504500c0f0f01c1821500003020441c032a400c8203007002d8002400c0d204018900d510030344100481200d113a1009030146044c016000050307940c00b048415591741d00e0441c0015640404159032501d0b110702031079200c0d04191000d00c086424400410700c0401c001c03650703a01c80e43d407075070381c0c803010704040d001e14600c22000d02c0d0a00c4c203555007000107401050385000018080042d6094020f45030221509000c0c1c014081d80d00300701001300900444403c80d401000f140e01c0b84000f440d1050098a600700810002181140704944029400342e01044d4005031603040ca98902c480d840811400b4040001641c4880e580c400007580b58111a56280a003200b540b50a90440081440000d524981610300000002028029550160164100401c6151180000c0240c160520701403211641c5036803034644542854a00400c0282 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 626621205 1250 626619955 626619971
    0xe0d031a1311030a0b040b010e010e011808030c0703050705010306060912060f0f05090105061002070605130e010611010501060f050f0c0c03010524060c030f0a140f041418010603 78
    0x141c242c00001c20307004211019680e908050301c9220061840c000b060740034605040c540c00b1690302400610100e20010784403520080f00c1080112848a600c01d8440e241034800c04010800c40010405044850b56090041900c03c0c11810314526025581c0e10507810036041060500c10913903c540024212660310703003d901e000619141590151074010b01c1c840501e4034100e0404480411500403501030840c1c10020480c980302d14003401880580071a10312f0150303212403800c00c041c601c10780040c28245968100c9050141d00c0b1444a10364a20a80c0310000142c40f042c02040550004e105090050515081510b8504400a009080c90040340400b0f92901030104000c3c498040500540004440044c0200b043e03103400e46900300130705d803503440c02504040200606030302400d0580465081c0300102004606000440342c4540040d40701070200b0b000c10150418404404a441000e003450f5000d6401c2c01d6140ca0400d408080307565003280300309100341880d81d07802c05090b20000456040d25900c0c0340c04220343c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 626622455 1250 626621205 626621239
    0x5190e0702120a1d1f0c08041e03050609071203110c030d03020c2e02210403081e100501030f0605120a0b0108241e0a0e0d031a 56
    0x7041c0341c101e4110060000380c03910360f079601299a89078410307042c000042440d0400107004507a0009500705450100e84101754000074003400e40c010425105140c09442c0039119192510040c040401807172440c000200240100442071002640c8010003400500c441482c3c191800e00300c0e102500b02400f44810001c1c0d188078000180001242c0160240031a085548654001002540150349114490203690701c1280d00100d511000c280900c51a9141c030300c4450344d072403140000d50003140741c02909101140198030310364130041400d1140d40261610400c0746061000ca50444e1070b85028044d14603031410422054844c0d51003100103507842845c1c0019800703410700f1903600810564200544c44101964681c07101c19002418804052080c0b40b00d842a13641d074941241d603210380e1044a0f000301484d22181e0007041c1200318242d07001c0c400f1032010080c03031114081207040071015142510f100c0d442e0240501c40d240d00b080398240008072840e04201844503d44c12504480c02c3c0303007101d80320702c0c40034176444044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 626623705 1250 626622455 626622463
    0x7020a0b03090606040c020d0e13060e0c0a02010c1b0b0901061806140604030b0c07020f1302070c050a0506180301022b1109060d021b0f01090201080105190e0702 71
    0xc0c0855031166507032410910440382c1d035100211141482581081c0e10360305c1c4a840446c0c2501d80d2a0035072144104089042e0400642c41c45081758001507550b00c2e000042d0001100e410301e40540c2c071541c106c3d40c1d40c1c6191038000b030a561245109000340400b018145545030400348040700703425000100c3c0300d442c2c6c58001111380504100d42c0400000b00d0142c0784182c8802d507c0c2d02c030408407680a0303450303c601028007003845007a0203148400703481c08200500294808040300d0041c56841e1009140012004d82d100010369245114000001f03042d501258100030881c04650b400080c1004980040e859894900020f0a902ca5950000740c2d40d80c0a02000d149038600350181c0d0072500501d00140840540000445940750603c9451200242040741e90ba200c0a981401c03100d09120103003002d80340c03000ba035520101a5104045c2d00f0448824250340791055032061100054600781500041001e1106000040601c603041c0c0101c0e22881c01000d01c076802c1c61641d000300303045070418080b00906076030b201026424 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 626624955 1250 626623705 626623709
    0x70c03020d03120e070602010e010b030a24020a0801080c01210b01140d140a1b05070f02090a051005041811031f050709080a0b04081c090503030601030c18030807020a 73
    0x7885041045402d24820040703086810b1b1102d07640200000204459602d09135850150407540640045070105d0102d541e200b0340d181006c0004000420550b01c140244040368414009100003880c42130051003d0141030003050703034168003483c14112512403014010b445021402c2c1c040d007815519418400140d01039405451170b045c0c51407516860b528644444000780c0b00c0190850390401002000400002c101d105050700c90907401e80c6160070040d0710b401916940d0080c00243e03050040305540030300507030710144480d06ca4807101c1004512420210121b044400140d0445481541812408484001c81000c0405415000b40f0781000c004030b0200808c0c01c100d41c500541c0703281ca5007031100c820351039a01e4110fa4011005940c0c0c042d803083e81e8021954882c10301c03400080541c0d82c1c940102d40401c000b5006411407100507440c1300030051410201804960418104407003940001c02001050346c2c1600c500710069a181c02c1c217170f0303042269102c0c406040c69a400002c00b0007030b000c58a141036442c0e0000c4180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 626626205 1250 626624955 626624987
    0x140a0216080304081209070623220e01080a02010509040b010c0b130b0c03060d030e1306080f0606010509030709050702030910320d02090411071a0c070c03020d03 71
    0x20b682e003001d04104015500c250640858644d101c0b01042e403400c00003070100c040b2101584d500841840740c11041b102010150f02d082c8101d0030070702030140054070410340b18001c8540e004c03c0404080c60001081e0444505034001000c0d030304029905070151360048221511440f040301c0c005400444200142c03880b003620700307014004041e00030810015900c1c4030801841c19004690000c100d03629054880c1c4907201c00c036405030b004425504060000790159440c8254480000e0126010040c03803a021800c446160f0b014003002e42c448421508166814401d50f03420100a203480c1c0e1510034043c0c046645c0b01c070184548082c103690f640014850902c00d1003914060000245242c090b490f85800c028030310041c4072420701422024029a40003200300307444100001301049811418483d1456600000350000000f10342c0094942410b012603640450040079180c0c8241011500e030440b204a1401400b0001c00d820300b461010806800803e2007120288100ca034100e5075142c042c502860200c68500151501c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 626627455 1250 626626205 626626207
    0x41202030f12130909030e06030402011e0f0e030d02030906070c0323010506101b0f0f1b060f020303040807030c020a0f150302180f01110d08040213140a021608 70
    0x5400021204010480a4112140751503903540b0b840680c4c00710390174180c0c000d010a041d00401103060503c04007540d03005005040900c0c00625507138440c4180743c0310441c18000a049428006403540c0c110816029148050707000703000c40202580e0107913a070301c103584a482c4610300c0800c003c01008051485d0001456100907001c0084a050825070350080110350031b205a0f5003800c0c000355180c2040c07816400744519656401524080d0f03140001c00040030113600780c032040d16142038900410b9500b21552030482c860b4002d00c21072050260011119007251704984104014005000c03035082d0700109494016030024580c0c1d0fa20354640c40d041d40d00d0355880030002e400c4401030600050854500e00c222003110b0b1141e01044545112031404c03402c074800ca1102800100f07801c4034a8050741440c0005010b00301060502e003a4070f14000c1401480c1070140b400c0c0707200143d454010401142420383c1036009416103a01c00748000718200f890079811400c01011604010b5000c14005405c01070b400343c2c00c500f84d4010b4696 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 626628705 1250 626627455 626627473
    0x40b04031b0501182c0f011a0408060403081302040e15100b0f0a1704050d1e17070e040906140c03010e010611010f06080c1e0105041202030f 62
    0x81060705200e500c460118039850000010b16502130951001003554004141d2a0b5078202805031426030f500d0603412800388640ba141e0001908114009806003d80c1c0c1828002585021201540e500949269420990f02880200015400091101c0d00b05d03a040c05c1000007540d61664402c00360741040300c0a5801030524881144080001c91001e1030701c3d0f06100108400d50f101d9084140295491240c0710a11504111440324440e030744002d001e8130b00c0e5a00c0c11041218101844001c0e200d019903080d200381e000456618000b41d0002e100ca402e48807114a050082040d440020f0300b11035100300d140c0e011102d91000910103d120310780194581000500400032041e06d400c0c00c0008040e8035615072000311002012540300c2a0400a99041320100d02c00c0050316030030114211690044041c1c404420340d202c0c82d108082e00d1803801540080c206040052256641410800c8640c0b0303000d00c0703649021210440310b24890b0341e2040480f400c3e106a065207034412400c41c80482d140c9640d204104606005078886 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 626629955 1250 626628705 626628713
    0x70605070b1812030f0405060106020705030a03110a020a181419050411031c0201241217040b0307030b0f01020d0507021f0306240914040e0609030d0e010915090503040b0403 76
    0x5180d004031f016604640417681c07540b44c180d076111002c5c002c40c1e0385a40103038040d90000c0d00c90448850380b441880165060b03881903a001c00e0584140b0f4201710f44c41c590300301c205000c0c0c0c140791107003d00d0460f01c81c144583d2402c1024082c000d45a100c200302c49229111000901480014800300450490140c100c6005a404603004405074410196060055007000c4015100c144801e07078900184114802150f810348c640402c1d40ca030002c403107404550111845550040b40c0c502c64010304001c00400040654a00e010350700281100c0034400f60611825200e03c607091281d17070000b1240145801400c00c1903840e561400018445c00554031848a210400c1090f0120a40d05801c1042200d0030010b042200d9000c442e03130b0b02007408100c400c0c0400142000c00c10441da070b20030305210302c0042010340002003c46d8080c1c0c40c241071180480e80740c0c0d00351740001000c4440700034521600283d0080d4000811403503038180c1ea00c10010701010220340409481d00c01135024400f050044800500604e42e00d51b0392a1b0703803490 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 626631205 1250 626629955 626629981
    0x50a060501051203031b09030a060204030602090a0605162405040f110105030103030509090a0207020303120601110102250303020909090604061a1c05161205070605070b181203 77
    0x6414041c80340f580444081100010580c0d000300903100700c0102124010320410702d6900716814955040c071980103c01c000c688148010006540038210150352050908103101001900350b1122040000800a03954a41c0c40f04e441080400d43c01811002200312003206815001000d01c0f000740c0c0c10349080180700400112032482c12409206001c40800146404015104c5000c24030015011410401c022801e5107007651a0591102c4060801420b00800b500400c0c51500180d0f080c107565030010f01800b56540c0c0220a800503280307400000c0d41303844106189904070705280304509968940c0350391500d08142c0079405444041d80d020b841142185801c11040c0e035110421380e410341e0010314200a80100140e040d030305004821000e0718800340c01e080e40105c03840000c0e42c170006071410300440800a0652070007003c10401020080c80180e94010242052410903a01b54841001c2c86420816007002070410054a503010350034113800342550045908960600407809086101000300004101c16858080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 626632455 1250 626631205 626631209
    0xc120e01182907210c0606030302030c0f01111e0912030322200a09060b09011404050108010b0309010f0f270506010504110405042f03010b0706090f050a060501 70
    0x1901480040c4641c034865555880f880e10b000e003071050355011280002405501c240303039001c1c061030302041e6501a80c64601c1290f00507042140140c1001170081070601c4208100d400740c1d070588000f04644810660b80d006503114501c613004003061114101c50a10124105803609400042e011019144075808003a481c5c3d070003129031096061a13100d030101000b041841100f00e0740d43c00248011420000d210004a4844807031119500000400001c00d100000340a000e0007030080c48032254541c80c981c40007400d0260640418898800140301c204400e81c0c5c405d41190465a1b00183c10740c0d261100091f403809046402e8400324502c1c2003120580c038890036940940c4014a080c0c1100244ca04000c0b0b10480d20144401d01804d6035001d0700050080f40380c154807140241458114140c505035a44001c00c0c10356041020f014a07030803d0343c0f000311801c0b124140e0580280381806038140f9642c1402800380d04e600400c64080c12090b40c03950b20b04100800107022116950300001125040c0e0220318002d40a40ba0034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 626633705 1250 626632455 626632499
    0x406060201060e0f010e0f0c0d240b030c0f030c0c010c09030c0512070b0306030a0f0c080607051611040905030313021009080c040f2c06070c120e0118 66
    0x41000030703201c014201451340c16540305000c2a0815129041c04c282420f102501e0380d01840c5040110030502c0d40b00c0e20030880d43d01c0d03146c501441044040340100c100303c00705600c980000941042003159210700007048500003d50594015141e8130381c48102a9140602055803005620700700c0825119a0001c803d8411030b8404d000c0026002d44036000d104508094824039001eaa20404041c04014800409580d000001504071034440400d62a4403071100420382c01035607903491031001481041ba06100361369000c201420150310304105145414044400600c0c09001e400c401c40030b100d0296200c2d04150007064000e41141d0700c1e0700704680c1c00c440c444907501c2c080b442036051f682446c2003e03000e0b40c24070048401002c0a0000d03c1c2c0e80c002807001034034442000403400c51342e4100f82284035042e03ea24041c1c01480c1c115410204520b81d14003072810030007500e00401d1144ea041c00c1070014400c071201049074500c500c0c00000446450740140d4250301c03159910140f41e00380309d80101d40d100d00c10205071089104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 626634955 1250 626633705 626633729
    0x5030a0507090b010e0d02210d1707080702070608090a0c18140628030b01120c0f030206030c0c070f080309090f010b070f03020c061c05070e0307090b0102010605040606020106 77
    0x2043c0064507041880c109036074018040c029040d0240ca0a03008158041d001290f150722000f001d51440c0d4202540c16070740f100801d020303d140e450940c403e261540d5012140e4180003c948c02c008101a5407580c0c40c0c440c2104000c0c000c030010f40c00500910031120f03140d501900310301080d82c41e0700149900c80c0c89154421011441c08a8505080c0b00328290746024900161402e21801001001c210240c00c20a180001c56031400c4000000201003180c800d0090403203403102d0351142c03000d20f421100c4072115807003090300780e50185c0140090f965003411a6040000d64003800e64902c00d0207001c5050030210340c00703600c55004d580070004201c00044018000341c00106d400054a64442c8944003904c102070007030304061413040c0100380c0061016045101c03045e000340103c40d83c401c0c00c80005101780c0d014048401042601c0e4140306000308840c040c050b080003007403c14030383c01d40002002c01d68400e82071050044040c0c1f10403848410342d0003940000060b00000c3e0042c44026181c91019001e080b1074454007103a810 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 626636205 1250 626634955 626634971
    0xb0c131508060d0c171e0d0908030901080a0218042a030e030901030b0102070f0b1206040c080c03060d0c120c0b070309094701140d09050705030a050709 67
    0x340a0f0240907119600c1032590104a060035400780b004103403001940002d210341e514420800c00d00b100c61046540e00301009000f070b020b21070402004040c0070341c456290f540c0300b4002c1c46903682e0810503055100007000c500686034540184652180240d4100031504036140407240c5030030398034008041d00e544600744401000c2c0d1507104021011603800d050070103901d40080c048008158480c0d0800301200300144100c40e01c1a8803401a4900c45032035a03c18450b00300001403a1a080c18811302c40c5a02120468080060034404040036020207402080800c1a040000008017543c0c0c5080d4040d440c260130401c0c155800c1e480303500c5e00c10707a030310320345425504030070429000540d00788104e045a801e242c1c07564810480514040c4054090448652000b268043c10440105010f0740446840c444c2880848403080c01c15503800c1032440b8100d0107024504016064032520008066a030032210301c914404800681c10301c2c1030500c079013024056000540c0c58040c0c0103580d0148000011560300340d030401041005154 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 626637455 1250 626636205 626636209
    0x100b03090106140a121403070b0a0c020c06030108060f0406110d050f0f060a0303051e0f09090709050a030b0408072a061e110c04060f0815010f030b0c13150806 70
    0x65074499078172000031403581d0400141c0320b4603209048019400c00c80f82844103564075114600303011600c0d0b040721640d5100c2841401d41c100032500c03190300256003407491075060049044e101c0c00d0080c58514401c1b4180c0200d4108002c1c2d500c040781e09003080302415280c0ca04401d10102a1100b80e40d0400d0364240c160228050307030301404040b03000f400300500d1041002e20390b9400792000e0304102001d5003c1da40f40c20180d20a03a08950061014449000b2410354a000d00703410000b0f2044003400304000c00180050912060b01c40306020004d50f608504d810200381c2c2c1320316245249208089005142d402c4240051a441c8582400b02d440620701180d0603609070380300d1600b22030442e84814031134a01124020342210f10741c082c2030b00c1300c00080c20405a40615a01d440401d09442e610740c0090425500c0d04010000b6410901801400164048070907105514114420410105501015048098050106603114035400455404503a0a4000c403082903440f074041071485242c8010202050790789000821034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 626638705 1250 626637455 626637469
    0x102160803120630030c06010b0415030501050303180f0301020409140f0402030c060d0b090c0315040203090a0b100f0f090609021c180813060f021203040308100b0309010614 76
    0xa4070501200b000c2000b4800c0890b0304e162000d6a509058081003055402c004c6080c400580a070608103109a036583c030700000c0a290380a40d03051a42050325100060059523008800c403208030082060107401c103500900064102d00603500b00e10344c158800100000ca03c011908200301d00b1020041c07071040b0b6910750042000d802801c440096054000075035849036481e218001e44591228200002541d182d008003184008600b520194041c01c80441045044020981c1c001110941918194150308107021b04581c4e47c2500341d0010300144001c0c0c00500c4244510104000a080000001c0081a981d210300c000d030354114002c101406003002404561040b65008468010039408140807841020301c1d0450010701c224031a000044080000400c08681c00c0400f505144510311182c0320411700d0b0540181c110411038a101c4190f401000c2107480e004250000c0e01e920a8142c14450140d5447da240101c1c00815a0441888050040181300e8000c0c015840603099030b80c0404800c0010701d42008108071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 626639955 1250 626638705 626638729
    0x60902031609060c0f2603070804050729030405160324140f040618060f06050109030c140316030b090606060f0708070609020a03140613030504060e01021608031206 72
    0x10010001205c0400540c4803d52102d42801c1c2c0c07604183c0100c401c0d04402100d40c8151009000206660b0502040c071900380400d03801407606010a8407080304c15002e815050071002550440f101c40880010107202003404614010401482c8001000d40c403490400145c0c984260b410061004082405640247d5840751000707009080c415844240e61b9070004001c8013800403c200c13900e40e02c03401c410050302c4c0303000c0481d10b80e20f200d42d901284280c100c054190807110960302850410104000420200d04080000815100050300c84c0354071500d4100405c1c50308004005c04060b0130f40c2c1403000014080c00807040c17800754207040700303170b65041d12031740e00b0821507003e0444040728030b4408001160014650350020001e00c1d1040c81c3c0440da00c0a50b0300050304c43d282582c42540d80361046d80014090340c105000844ced004101d10b400011503080b9072401800b42c041d42c00f071542403018a052060403607000b041102e007251408203242d00c1194640282c9502c070f81000703910b046c04810f010042002458011840b4803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 626641205 1250 626639955 626639963
    0x307050d020307031d090604090f0204050c07060b151c1119110703020109150318080a141303031d0301110a121806020f0f16030e0d170d060902031609060c 68
    0x154466000f08401851201c4007222b40c0d00444c500f101c01a151401100e03c00c2c480c0c00d0031140ca50301981440800e990506580602c5404040f07031100758403541d482640c0300768140e0842070030304940340604540102040c1d003080080d84404903520010340d00400c08010400800d54a0044404150403103554500c100c0c04001d001c5005081c0c01d0015a510042a2060b0b85403842d021422904100419070b002c0c0042c1029521200005003084441c0e801600d003040d21180843ea0300d103044015001a170300701c1c0080c080281044501070f150a00e1824000c5494503841c802002049070b1007592421403100e130f00020310000031a0b8065418001011180f040d961324000d02c0010303000c00440c5549040095100e81041001d84000740540b075010101c150140c840e02c21850b200800d007a80341d060150444042e13111492044040040500c001030400c0d00740790382001044900c544480341224900c01801c000c2e042203108030701c044100014040ea00794400d4250b01a0344a400c01180c5803481100c2d60024440f0284c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 626642455 1250 626641205 626641219
    0x617010b03190f02300609100914010306060609060818070b0d0e01181208060f1201140a0501030305030f0a021201060302030703060e060f09090307050d020307031d 72
    0x6040810001c503484061104550040308440308000111000d0002c4200e84540c00319565400726200c0d44050200018999100d803c1d10000030540319401d4000d1043c0d02591a92010801000d4941c100c00041c110b4040c1c03e100302d07180480403004502007403200ba03034105c0c24003100017101c500510354407042e201160360318400c0d0380c0c442d0070b001c080c00d00050740343d01c1d01d01c0340400c0014807009100213400000c030340c000d0120700071404c4504c1d5800d441d4404032002030720b0660f046e14000109450309281e03080c065820141c102d1781e03400000030401b81411b0030b2150003400f000811621300c64198403a03c41040d1030318070039420f915000100001c030352090100030003056080003c180120b40c01c1c40c503640e220020045c0503140030043c0d0455480c0030700a0b400075003c2a00407040c8942d168041c02020050a4040d06038400c500d440d000040707404400ea001940524180d00c0803841c20034003402107804060308602140c001a50001c0001e5070b992001e201640010071001400804904801d1a10300742c25001301a8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 626643705 1250 626642455 626642459
    0xc03020c0318030a0221071e060e210a2109060c0f080f2502060306060706060b070302030a08070315030b0711010c08180309090f0405070e090604020a061701 69
    0x404024002c41480541c9032280030030500c01a581d030071214401e2080000c200c881c0c0164402078070301d0039106030000402c07c3c0c0c0700102106182814071603c1c00311542d610b400882c2c00c6c2000c0101d00c903030701c0c450b002a400e121000c51070200107000103800c3c20310b18811009a6031081507440f440100100340c480b44000100105c20412440384207600400c0b10f103004403038890843c0342a540c0c070f00141d4890b40c01411503140c0856000c2c0003a0440b92401c1e6202c2c10b040781001510095400218075210060200c0d11a91001c00d03a070081c03010b543e101c0710142550740c85403075484500d17003006580c9400c0590300400040d220700002d2101407181c000c00f862240c40d444660031041c21552103040c100001000002017195009070304c29050270900400d541c1c0340c40e58403045910b0a2094155030a00c10302030801c1d0555004000300c070713003984a011f1000d83c0405a0094888151171b41d150180c00c180309680071608038000101031040703202e00451828040d0b4805c580c806110356071808141c0e080303c1c62804010148040c0001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 626644955 1250 626643705 626643727
    0x901060501021b090c030c160f1a070212030a0204080f100b0d050a020d030e060a1e030e07140102031c050f150603070315091104080f0606060a0525060509010c03020c03 74
    0x74540002c0c4046110342002c60b923041c1d00624500c0c2d020181d606130307521030340901406a0b01400090214a50b039402d03100b8a800c4d00081d50303949002c21485107d06d000000200500000d5059070b01500507101514010303004002001e40d24800d426003c00303500d11b01b240b805541d1030040307074a001046d402000361801c0541d036000c015150000c00019000c0c400f102130038180300d5a4403001000881076544450840b00c0c4010041d681c201c010035041c6050615054040c14005070000b00c0030200d0303810f154081440780d40d00c0c00403030850062043c054040c2110540c01e0641c5000354011602c01c2903440c400542682c0c0f526401860314685001d41070f0041e0007080070641540c4282c11410040c503070311005403595940c945c0080b0440704440200d01441401250a00038200203011542c294032050380105914200100012498800c1e03069000c2030080000300ea10002c0007080c000002c2081100342401410b1250a040d405488101c540f01c955510f0204110304080c00782c400c1d2540400948011030403d01d003646 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 626646205 1250 626644955 626644957
    0x10603230304090906021812250b040e01080606010306030c060810030b0112051501031a1e011701180c120c05120109030207090e120307030e060901060501021b090c 72
    0xe20542400100808580074440c0d010314481c0358420302005a8a0720601d8206541c018402c04540c404c0500004400083e4000940c0c50042792429200c8035034030b0541140125091240c1e072028002c1c940202c0c00190042c2c0850314a4100d894800903161260348101c0110112071060000030201c0b402c86009008007441403d0700ca9021a414000d45d45054032929106c4041340242d11454a40c0d031070681d644c0410105100705102d002000c01000407950561780c903411400846400036185c0d00c5c0190001d020b0780c6281903065030350300c00014401c805584074004190110f8100300109059070801c100d80300008440c2c0c1440da1106c0d006042e0840c92402c3c194001c0080b01d9610741502ca41c0301c92940880c15503a0001d217000c4207480c55000051101c8240380180c10404140c1c404461070f8a000e0410000240c0820305285200140c0b0030315949580b041010350003054050441d641e203101e02c100f04541c3c1c02056200c00c00381c810903001c9a92080d2603106184015015144154003d00100045417003248440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 626647455 1250 626646205 626646263
    0x801090b0613152712050a0c23030a050c0402130506030910140114090414150f1b0904180206070c032d0b06031e060103050609010603 59
    0x50495141c03446070036000681e0490b6403c059450241ca05045a0094001e9502e0054200446420310302540c2407560780b4000000e8810305218041d0340e000030b010003c0c14012188060350006501104d141c0314501240e9908003034003032030900d03407000c91001e40ca858001903520b043c0358880010401210340201f400302079000607000d09080c010000340400c96a4902c00918800c555007002054040814071644e01030750b41700320303401c2c5c1400124401032104400408841c00040d6041d10241030356180d6107000010152445281c080c03900400c0780402c20002d160300418004c1d0b18210460f841500c4403503a080110048032404100207404204a0b461428150008811000001a984c00020150300811002c0d031105804580b03030315032507109004208241d03000d4003420040346000c040311644451918660401060081e00c4403000200040040c0d90410200f050b03902c0d150010170015004401003541d41c0c000b0701003250365010364400655111414405c01c4200c9800c901c207a01850581c00798074080300600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 626648705 1250 626647455 626647459
    0x20d0f020a0b0a18090b01021216020a0b030a0510120b060303070c08062401090603020c07170a1e120f030b0d1a09011406060f12090705090c04060801090b 68
    0x199200140d10007040c000f0341180e41e1583c0b62400c0c9440003400540d0340c0070b5160029280b039443c282407a18a80d034009648400d00f48090146507980d028200c203401d4800641c000254000c0240201140500801c000b0b180502c10141003804a92284100c1c901d40407201c0c040c0e080c0309004800c0f40f0000c00c40b0b092420340c200030054203072807a003000e90f242c001544150b0340200096610040600139110310041e0030b000e403484950604825040030100080411580d407280c84101500807070a02349401090009100500c420740c412494510b41010041e00c0c2c1400050a8071384840c3c00c882510b50b42002e10083d0507141d4840c84c000c040c05014681651038100e84a00d030410542e6404002c0caa540710705042c511158005d0b240b00b81e20170607100f41d810300102e00904a1516905200001a00e405601d10709608854100c0b0300c20745522107c41c0490103801802082e1180410704014855040c0e80441e0314000d503001615401c865681305031140b1005d10882c0316200004140303a00421001030b1980c40003c0301480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 626649955 1250 626648705 626648719
    0x60a1514070c081c0201060303093005010c260708091501030b0f07110a02010f02010b0604030c0f06080c091e0316090614011d0123030403030513020d0f02 68
    0x40d00d07640020341c4540c0101d01142d20560302c44e03e091551030224580302106100910000341940e400410740c07042840344c201d00c0c0b58192100102c41e060009104030801540708200c14000d46401c1c00c50103010b09094000114001340d04140c807141d000c0d00c071604c1500d80103a440080d81c503081011641002c00a00305c40345401803001c98413421000f14a6a8000d6015a003c02c0d02c038100050004e0420b44c01901c0c1a0902071402d5100304070f01c00c041509407132103409080056290554420503805401079902c019808800003a000c020022100e440e00b0030348510f0400b181903280c03504030948030f802c03068170300d071408900502100004e458500780250075002034001c642407041c0f10704042440d01504c002100c02d00520407805000b036140c988500c800030400600c848003080c070140e0001c1c10096400c8000c850034401c5080285059010380c4840c010404a03190303212448079120b18500a540040d142100042d0a01001c202400c0f560381000c03118a4004050f580c05100030f903254200e1b150100c500302e0704080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 626651205 1250 626649955 626649967
    0xd020d0c0506030108070e060a0e040f020604180614030d02100902031f090615060507060207080c0d022a21011409030a02011404030519140406030b0108060a1514 71
    0xa40b070300030394000c1140000400020b41800040300c6211001000b05001d0389007100208909580c4602c2950029004001100e1000e92400441e04500c142e8008200f04680030011400303550040e84940c040b50307400000c4480b4240704908068032142c11000040050344200b00359029054140c2c0001c4a8510080403900814203061030f00120388042c184003407605075101c0024050188500403004040061452195094241074000d4018022080050f10300c2c4e0b03010038903004020a180451b08001181812910822080007009503201c44440449041c59401c60385c2c0c50f040304070200400844039000b080204c800c5a10305059202250381d00210856648604840c00d41044504807507000b4007c03c03000d546c1e503101c0400301a094800381030241e00913014000400c0080381c0e110050300d901c281c3c00d4000981c03280342103004403140d035502c203004001d1110001d400031380190158080c40d842c94080c2c95003146507440c00104402001c0a200d4952110080d0644d801028420303a0981045020a14001c0c1800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 626652455 1250 626651205 626651209
    0x1101060810020304021305040201021018060e0604150515040f0209210c0117060405040c1a12180c0f0103201305031f150510210603020d020d0c05 64
    0x300401d40450403080d4000244019400d14069030302c000c4002440c00d0109041c07580c0000d40d00e054071401c3c000141d030f41d007000113600c61804180000182d0001c20900c454a4644011608e0b40c03800d07501100d03820750352540d264401c4c8850150034860380e600f920440d0701c0c900c0d80d410700000e40b08003941048819030812405029684106d04a403180c500a070545030a404030204843c0b514528807040c0741800b41c1d003030101800035002c000c010f511040645003c50036880c2c40c54805003400450304210104401d84c108036001c0d8003c0300141c460b1200c000c0c01050f46031074042104601e115102c040d100c05401c4035045a0f05414014003011601d1070602d400940c4824808030079010580d041c3d00000501000545205078000d4510004080c140071000b034400c03150f20460400140e001c07400e035408510b8a88486042c481034a1011000805001e00b00d000c0c100d40d101401014101f40140c00b0209480555040c604880f80f0f105d21402c0c0ca80c013410049174284281c00300301d052030b00140111105070b440306000c01c941e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 626653705 1250 626652455 626652463
    0x1150503250e040e030c071a120702030705011a03031b0c06040f0312021603060f110304050c0102071e030308060409080a02150601080402090a0903030b03030a0215011203090611010608 81
    0x200403259074855051260008003c00e076540c02c071001c000d950040c48080b2032500c0100e020801c484802d8480d000c01c52201e0402c420b41c1c00b42d14245401d40c00b0000402070155008070052046a1043c0000c00a14405e400002d03074041044440307033f0301a4010301c9145030041e2100504141040840308036064200c800d030004115030b1203508003000c04d4003000810010010441032406a401035400038201c4a030346811440c915002a00c03002d0002515508889041446036006e0322080d4007142c1010755901e4141400c55445000005040c01403107401c0001403408100304002601550010702c00c00c0c05861518210b40401d4003500495005650351600e40014100360010140c08007a90042e08101001c012495480b100040580d810302c83d2003000c110040c0c0e10034214540c0000b0800000a0180c3c0c50304003140102210003030150144400102a99610b0b00010459070280d1100c7e034003c2c0c1c40e130f02c40e581910392825911004021802d0210180002409a4010310a4a03511000003500c40e98036040e261034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 626654955 1250 626653705 626653771
    0xa080a06031e03020115141e100306030218160507050c1306030507080604051c051201090b1201180b1b03040803071e0c0308070c1b080f0601150503 65
    0x42041d502c0000300341e028040c0e409078400d2200c001d00010b1804010188505940349071520918030309022040f003480f60200281951401307000704a034281e0704c81c000b400a20307850000781d1049841c00e4404020541500f0050301c00c8100303817100c9040e5101442e003a030b11a042030f0700440d040d01400c1281102c46d1100014000052183e80020030b48a05d1400e140d410038007140c010b050560005410800851f0380007603850f80700e072480c0044041801c182c908c22175207401400e90700e03101c0c8058480000f0300030020341c0040b8500030085401504513080000c006003262500854010084c02504a90b404203600003a030a51069881c021a03030030792110300394210141d00c1114201d580302c10120a000209510a009001c8140039001d800c0c03129003e81800340900f944403c00078200101400020505071054110f40c011984c00f45000d64401e5030b407002e01c108841f160050202c1c511640501404151000481a049806800755074090408281080300c4c80c0d84003e0120106e605542100200d40603240c201c208 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 626656205 1250 626654955 626654993
    0x605280b090f0c0426030a1d0303391e010c0e03061f080a0f1e0206030c0a170906060a060203040f1205070e07020303011d07050a080a0603 61
    0x120401140100059610081c05502c0c1e480315200800c883d140414040302e041d40d4080710400c034170b915003914640064006a105500f540400b0406910940d005500c1402410005da04c0d0342e0783d0b501000a040e940e0084c03880e030f0404c03403040a03044500c20400303800f00c7c85004207c0c0701c2c0422840c2150003062524842225510118a0319540b160b0381000030312515010325903d03d4806451a4003000003940d03008003078003400c031500010651428240a4015003402080c100302501e032806c0250500c1e42d00759403421400c2e104a65144001802e120711a0103620b01c280d401030007075082d9100c40025641e01c0c2c000c801c030304043c44014091107882507103405005100380c030001d0080c2403910b0324100340036105095602401c150f5005110501800c000c0301210b03c103031002c1601c030030444461401d00510301051a40400c0924100b101401307030b015404001941a5900e2107007241c0710003000b0514949041d000c944247c0010024040031160358844c0501d43e40241c1e035140d0224100c0e131691038038009407040940c10340e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 626657455 1250 626656205 626656211
    0x70f0203010914011416031a03101d39040f05060f1008071b0605010e070801150804080307031b0509013b010903051207170901020703060528 62
    0x500d00f50000d001d81c0b24107500115008650f828002002a40103600c1e00103c1d00b0f140d210706203400304403c111450564140024201c41c0c3c5139989503030000043c540810401612039003070110548a6000041c503106c01c4803100d02c0b4070081484101422410720241c96049000c0400c0391001c10150741d24000c1c1000c5013a8060002014200341040140d880c0c4980d541c01e0040c2110200d40c1d02c89a00b00c402d00f039201e01a8203050707035035403080310755282c13101e05080c0d00a00c039600e03001c004295030152a290364440d141c540c850140590301c4200008045510b1030598000038824000280001c030030380050b5400c036a842c02c020858503800310484c0c0c0b0804103800c070a0000355022400018660340b200c2080043c1800c2105079914500400d5000004640b14500d444018001a91400309920807585c0c000199005000d40740c07120b00312168801546d10180040d105e420140361214544586e40c4112004160140c000309104c9180d599100003070000280454035103002d1148014181c00c0c040b031400d0200450702c07000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 626658705 1250 626657455 626657483
    0x1030c11251d040204050703061a030a050903120a0f0209031015090b24070c0801090c060807172805040204051503031c021912240b070f02030109 64
    0x484500c08207030b84108034a1158000c0c8450781400000344030780080d01543c02040c190358101054014000990068a0325440c1c81c180085020000380030f1070040c0641c60041c07000c0d440d5900095900e010301e0f03200c0302c0c0110680d8045030982c12590b20042d10246e10140150511038814002400c0c07070320425001415075100c15101c410028a505288080c112581c020011094810702145007a071580c0f43c4249803403440061220184500b409507428140d1041999550940f12012103018224018080b02c4443d1b0340300f0080765242c01580c1107446010959110440f1070009507111051900c050300e0342204082c18003402500d001c042c02c40d20700241000d030020841d400c0c28030601044860050402030107054a110407610b40e5000700c103c43e0075184a0821501e0f188030700b00844001d103d04090b0068085401038020341d071030b030030040350b0b48500041001001140d40e40c4464010703101c0905500301c91101610002d000f9001040b002d03003101c40c01b40c000040200126030102c2e084420107001a80c88210751040313 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 626659955 1250 626658705 626658763
    0x30e070510080a0c0f05180f06071a0106050a27050a08030a02160303020303010b070c08011b0f03141b0d02030903070c06050715020715091518050c01030c11 69
    0x26180034014145420610004901c170002c01c0d03401108000c10010154188144256607002c003800e00c0c9075001018696147c003a0314140c0040307070301011a01d0314548481c0002500034006e20903245541c041fa210000740c8004121a52038007141d0021000c3c0a0401e01c41c0812561906c41400c0c0180c1381c241e00840c0c3e61401003001174a00184043c0f1112884041d03030003440081c0d4048242c0c0d04444043d0240380c2c50307401e1464503c144119940065666600e011090703130031070707240d6000c4849034030700c03038803409000c840c001c10840680ba038440c15440b0045900c40400e514101208101c0c203040d146505c2c0f14140104d80b1442c00580c0e10560f42e040c540d9001240020038440800c1075980140f15030309289151062946d1618800b0080e82491000103034041484d0050009080d881c8030705e4140c010301042800c41c2803070324840902914040c08841450450000f880d0082041ea05880a070080300038885107046100440140402c12003030b0080000e07200c0b4030031000c0000c109600040211030001045042c89c000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 626661205 1250 626659955 626659961
    0xf0105090f07140d060b122a0609311a0108100e060d0f060f0501090b060903060112020301021201030b190204060f11070b07080c060a110a030e070510080a 68
    0x3010b0191025806031143c20365030901100700342035102201003055001003001444d010f080304401c0e815406000000014688640020000c4c0007584001c1012035140c40d0912550303010342c407200e62304100d0380c0034801c0507560110403001880c1e44410300e1098100340440003400352040c500400300e0720025581092920742c0c0010060754412280d13000108000d00d001500514203030701518060040c0d175405400e8092140f5980c011080350380110302407003aa1344410020340100424400d03100d1712403800707460a8251800e4021110382c6d0300011300604081c0d090013800c644502003140c040b64159820007040c820f1030700e0824068003c6014403002500e0340307007004151069042040c1c2c02e8528610401061000582003045941403038000d00e043c4200ca4582000300746007031110381010312000b01c086061420090100010100d1380c100c0c0d0107031811501c0340170081d401e0b50000f0082c0440700c6400d100a0b400c1c14030a41c003031250b98507284211001959280c001c91400d110840b030703e400003032412042040c9008140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 626662455 1250 626661205 626661209
    0x303270a0b030f15130902060d0507080a0e0d170a02160305040603050603061608090109050f0a05120901090e150a1409160503010611070513020a14030c1204050f0105090f07 76
    0x1e400c41c400c0100310310000c0c58503817078071400c03850580c0c0c6c81c1c040c2c0c000c0d0348408c404d0714074440204c2800c028a040204002d0440041125564005030410140750492400802e111003122942c1e180c070051484045515815444001c1600038600d0303084c0305140209511050340c1040c240681c445a580f40d0402c0344c014144c5500915460081e803141d800c2c840300c2c03203140041d42544041454440405e0305c41d8541ea82c05084a00005816031203003000c0b0f404000c00100c0c003207541034810b6003111a11080f1b22503000030390081403d0700e404101e10034401c128800c0180c0791150300190344494002400d80b0340002682146141d003104d40400100c1c4002c040a041c403408240e08402e211035804149021440010301c035100500654041140b01c04001c17004100030000701000c1e1400402c209034030bc440000841c02508134150b10400228032010310503c40405808582c094070a1400390b45c0340490f82c0703818000000010344120381502c110304001c9034040d420301c90240648080000752910030407010070365103402003607 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 626663705 1250 626662455 626662471
    0x605130e030d090302010b041a0f180705071a0a020324090402120106050904141c080c13090f0e0f01021c05150a0b04060f0e0303270a0b030f 62
    0x4280c4800d0184000290b4400035070304000410903d071149000c901405110160340c1d0000c0c208990034103041c200b6202411040415a041503000132803808010b4074240000001c59089005004991540e209200400603075014070040c1c3c90100707030840b0300300040d0b00c01c45189410303560120a0001a00b0202100319880e0410202d1205001080300068203040010300024032840701c00d8550545a02c0a4014200a100c02000c0c1016031400d42000d030484029100095501d0159540c14a24100905a40e02460700c06641c3c8007115a10740c2c50004546d4008407000040d010403250000305503001e801103a101041c4c0c91404141c140d507010040b8030f0a008060b80062030b034018020780d007040408405808000721441d0021440e6103c885c21750704203280c070702042900110030230300c0807a83d100080b009100f00c03146603681201d0034250707600403690040e64402c401e9040c3c004001941944592100720000091800010500840d00e04c00240f44041564415030340300902004010801c0020703000c840e40f020072 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 626664955 1250 626663705 626663711
    0xa0819030903020c0f01110a05030705010b0d050703260406120b03011e0b040e031219150905040c0503101a031204030f080423040c14191809060513 65
    0x195800303504c0d2180d0b140c280d800b600c0c022440e4062a03101d1000000000e03e8039051f6001c8181c5424855241c0c0c2c841d81080d01c041d800c1002c8031304681440307111040c0709500600030704003942c1140d036051640004200c20407900c0da080190100395803141f00081c00100102d0f11a01903501c5a40684400d8950025640344241d2505120341c0c0030031507c2e180c00a61400749100090a007480380300041c020400c890b0a10031a2101080c100c40d204080b40c00305015164038000d4140d003526640c0c10034140c504034040c1c00b0421b100e1400811810701c8039040150481d2180c40c240000381d0720303480131a25084c1220504400b01e92922215181458240d00810034420b041d8050034007821929200c40252003a80700c0102010b170401c41031410300c030414060300c0103842c40315440030700141e62031407c1c0300000001074254410303468040300100c0d131030154140b1075403a064415005e040c03e0365070107503a030100d0000c0081000e20528244002e4000b0000101e035018240c0f055000450070b051400b40300c50b4042d410100003001b8a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 626666205 1250 626664955 626664971
    0xe0f060904080f090a0e090a02240414180c1306020f03040515040e101703030609070f030e07080a03020f03030c0d020906040b070b010302120c180403110a081903 71
    0x20000080f190980c80201101d580e80d45a10701041803d0b00f10b42c044400c0460a0091090b980790114a01485034000c40704865074007181c018803c0d8140c140444989112010802001300d408501e02c2c10808080091070446106c0d00f101d4810890103044881c080c03d00400501700c00c0384000d812010018002510003014140c0c10300f00314036542c0c49035002e01c0b4450080051400c02c00d40d141e100311030140841c01c1d403411850800f840b07003440e81581400f500a118041d88004d0f400c0c1030001050b240b0641005151590350745400d2001c2e121221404d02031030406445516010711031004202000c0242070110051800e034440d421700a00b4502c02c0084010760b40c100700244100500500145c031110a2a010016a1b50b80c000c0c001590602c51540034450181000c502c0c101032041d51820607040300c0c0281c410940b40c152a005240c1c44210b80c1d0361103a804000404240d072071945403c2c9855000d80b00e41081c0480203046500140350650b4080110f49101e0001004050b02c00360203490b648a06c841c0c242804408 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 626667455 1250 626666205 626666213
    0x611160302160821130e06010215130f051c0e1e03030a030e0313140108070203630a050a1e0b0a02010b0f0f06040e09030d05010e0f060904 61
    0x4a01c1d180c80c20500c000e07a860305422025410455080000072404400c00654404046e606143d04440981c0540502145101050800203c00c0d00c50a0100c01b082d0201c07205942c1e01116001c140780c00e44c0c40f44206444c2d00d504c200340043e440800d00031515100500f00c0300c14204034160a030714400240c280b12a401031039594600000b0f48120100e142404030700c1c6c640620400d865030280344420300d40c10b141130100042c1d00c00c01550101d0304600a0b41d86040ca61740300d0f030050703959108a4043c64048260001815124030380c001079600300280c01c2d07084803004042007072002540014044ca000074450300103080e00c2d460708400d40e0090f51250580d000040a0301d0b150010b030700035200c0d1040c1d10741c1000580340c950b4010780010401000e8144140b10b2a19003800381c0b0024001d003500401140600900000d101651400f60240c20030210700a1590b8900f03820187c1200070350201811100007440180514500003c00b4001c0754003078641c0c0b40c0c0350041840d0515010f4101c07600a07000b503014186c01002c0c0004070b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 626668705 1250 626667455 626667463
    0x18050406090b07180515121305070612050709140409060b1314011401350117010e011512020303040b070501050703060b07111009170618070e1306111603021608 70
    0x18083d4400d1120347c1e9680e00c0c0c60300003598480c0e82c010110701805901140c40c5400104201c01d285001100f003251317642d07041042d60f140d505070044600000303908170a00140e20b415004407507a1131068002003030800100b40491800e0b03110f0002c03541c0c4183c48208445040c05e0001c00c0500421044c4141046903818600190105003099500d117607007003445961150103050503404061600556014401945c3e45d140c6801d014a520b01210700f8039400c0c00002d008062050081d004041c0303510b80101e280900e440c1d5030014089000c6001ca8042c01705000c00144030342080d015002d8240511300119840c50440d8005080700d4180c0c0060401e00d6040c02000c0100b41100b003e0300350f90106803554442c9101d9207005440c24220b5034818030540350702180d80309c00c070381021403502d0040449800307100c04c18882310b020b107403a562036000304440d0a007420005000c190804010070041c9000321720002c2c00c5586d85010400b6540b0002c10101d000040c0b620480030140c1c104043c41c0d619140000b05840d0341c1c102440a615 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 626669955 1250 626668705 626668717
    0x610020a030503061e0904110306150303122806150302120619170a05070807060228020d030804151a12121306020d050418050406090b07180515 63
    0x20742c0b1704442d14140e070130300c4024481207001e0090001c1301900c0c01d0b00d40403540f000c64410700c03402405800c002c0b0b8002c8100001e044071401001f40a54100500c61800b03803a441c100812840010410803100c6050042903074071006207515a5602040d480c0c00c03e0040d80d084418003805404240c810007015076014903041000d60402000c494505109040340b010280380e240079009004071500d1680700c05148407001503001092803044c0251005695030f0b1044613110100c0c2e00c0748001503008401141ca08060100030520540c04200860810401b44d030089490400401e40803004500213206100c00c0c00b000c0c000102c40d0310102d500521035181d1404106600c914001c01840c0900604581091407100611040700304901c0715407010346420301c0014074107040b096845208058003400910107020f5100f54201c41c281c4208114480e2248940e1654400a04000703005885241d5510500350000f0b20842d04076010b1006a038442031407211000707000030800c0d519071003a8481e18032060300e007135840752281c1a201 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 626671205 1250 626669955 626669959
    0x70c0303020322060903150b09070c0b1302090402060c0114010902070510050106020309040b15030405150a09020906090c1605010606180302030604030813050304300b0f0c0717030610020a03050306 86
    0x22031f6261106202510790760140e10ba10240400402a400e0361201144d82c07214080c407000303007064540d450b02da00d1401c41a00080d41008941c00001e001d803e22800030f0a00f007680301c0c00000d0f400081c40c41c0350f45c0c2090030b0700880006500044d40506100701080060190b01c0c03016030400040d40740c00c1005e503a92185081c00ca008a840380c070000c4840e6913102204281007441d501c090754074a02882c00c90384800440902c1d0311041510320105024040510420102d80c0c1d02030706054550b102d01c4200000010000d00b50340a1010030003444855000718002d0b503040911800021810030308219000d000d42030300d2035001c2200400c0960410140c3d50000790f803074220750036042c039961a45410440c4903003a4019280130b8111711000400103441d0b9084440321012712030410b9500648030041d418241420903115001d8512414a404940411500d9a070160407580c0c09924902d071a89554404006484110701d007890403201108000050a10142c10b190250080c8082d058401c0301d40c0c0c000d0300d640000740c5124 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 626672455 1250 626671205 626671223
    0x20d050601081e070e0a090902120a030c06090807050a06151e0308090402090a060203070218040f231519060b03010e0403030204170c0a150504090e03070c0303020322060903 76
    0x10991170164040c1c4040c0c9a01500c5140a0343d201c21540b0051300c2400e100300d0084c004034100703801c04200402c8a07124560702d6030f01c0341e01d00b11300354840700040c1c480d1603000d4940c04020450600000c00400044820341c0c403401c2d001c0352411030014161240036056004250309005900c0e034041c100f154140c048140c1368082c569948806061000c54005c0c0151206160003407940e803004a100b58001010700100b074400c84107070000d840c5645441c2c80c40d400680c1e005004c50200c0b001180000d03042c901000e0b0010403030b00401038140360036424924105201c00c0d01c0058070040300501a0050303049c103603008000d15a003070910050f80303454040c0d891840140321f81c0e035050140d40081010140f10341c04a400808075041c01c001c1c41d14209581545680d1040314542c807688a0000014002e030784812820468000c68a400e4202840e1026a601829003e4680c2100d808204040720000b1801c09a8801944c041e40c01103465017004490f81c500000060f00180f0341010320f0208003c241ea0180001040c6c9038010504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 626673705 1250 626672455 626672461
    0x206010812130b03010f18091a0403020a0c1e0b0306030303130309050901090b120c150702010e04020307080f1302030604020d02180f0601020c0a0315110c0d03020d050601081e 77
    0x1848200d41c0e02e402000440c20f00100025284100c41d0320503003512501003100702e00c0900c01c40c071315044640410f8004c0a0103000b201031180c941602e0300207580325000c1e0054480c400c0c06562401a000f0213a00208001c444d01c6010389600300b91020b81c000600348c0710000d2480c505104c4002030341c0b4007008003580c07030401501c1030200805104000400c010b15024103820429612131011401404900742a03500492017081c0e6000c0c090310000d082182800c0c0901020241c04460308004c00d90751202c00281c0c1400050075510280e61507e10003140b040a041d41c41d0b0103623040a00c0300c10311a05028080d62210f000c03464030040503940101e1100c1e0001c1e8115280c030100000d80c80407400504c106c810040c1c009411340c040281c0c078580400460301c2500c0907400ea585100385001004445c0c1c0d00d80c00040d1019180d4080b11116100c04c4e8051103080c14010741a909142c40803070301e945080700c03a80410002079008581c040c0c0e42401805016004a42401d2120051604d58078081c0d0480303440d0200349140b4401408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 626674955 1250 626673705 626673727
    0x50103270f050a0302010c030e160e0a02091c0c06090e0a02160b04120806150d02070201140a0207090501090b0d060c0e040e06011706131202011103071e0206010812 72
    0x501c4030040c2d1000643e20300b40d040e818081c0c001c0c842d20341107102113401d090305800c8583c0080342911460004403403031181107003046021031140000901e10301c01c5950800000405503070740d000e80f101c00501c001c03a0740480a200c2c6003060100742294404800e000f003c080900c030b800107021007168001d698500c01621440503212180410880440c081c004281410074001413181d80c03002070070300354910313251040c0c00c0c1c03903060910a00305540c41d448181d8400c117020741c0390b411000b50020001d5a00500d0301c2c5003081d64038090403885070f211603401000359101001c10400074009000d080c1c01407280c2d010400c00e06112001261000d280014000c0c607084c1c3e140c0720b9000c000d00401c0c0702e014030341001d4410040c4030382c02c890701c598800c0c1c02e020320a40703054a00400b40c0928030014010340306441e00c0c2c0400900d11801d03614a0701c44c00c2080504030139075481d0108009400c2503440558807401a030742d50700d0f910080d604000680c40050030413000454002d280148030b81e48000032507070985c0c5424140b0b59941c45c240f0030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 626676205 1250 626674955 626674973
    0x60207030c021e28030303110f120702010501060516030509010c15060602120403110105070606091125020901050f06250b13030c0201080a1d030a0905010327 69
    0x4001c1d80062810324084052240144000c00c40c00195489200340154800f1004c00e250b40030b942e44641e404049051000a100f600200316101e1b00e252081c0c1405083d041091458000d90ba004502c54490420004807940c2406014010001070616900c4d201c2054045090400381d41c0c40a010300c980002c40720003d910a42d41014441d4102128190792120824442c1c00b42c0210312a44005214864507181c9961400703003110201c0c0d82c85158600628501001540c1a17000084d003650525611200081c40751501d00540031b1540300803d185035174101d502003200c1c8000e07400142c0e115038200c0101d1800180c4461601905607101110040a0300e110900024060320072a50070510b05100c01c07052000c80701c208003c900d03031b00f803003207880c101240e54400404030600b403d60350140001e040003050f140554010b505160f00604040008560140707611040d40058035140c102d802d141d800001e68034011540003584034090402460b080c0030781c40003500d1003c1801e6090200c501c42c2e0000c09824010080d5201d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 626677455 1250 626676205 626676227
    0x60103030f1803050105091228110a0b010312050a080745051507030509061b0601030605100b0304111f0503090c060405031009110d0605040c0503031606020703 70
    0x24150001094413854924007814040e510848188240448201c541c0403100666401c01c4c030f441a500c01c80c1d440e003d48550401c1201c4480c0301400142c145c0e00c3d04116084c042d080720a805901190025455072a1251000d0031500b107050401c4404d0080d01205540400f00b207410412915140007107031005240000d0a00b241c800002c0001414020305402c4c110a8038043c8402d4220361101c4400d95540040c400c00c01c6040c00002e0b032000040000c0780001c4d000b0000740400f128003801d514107210031801c4813201e13011046480700c056445a00100f0410016020303969100b001c59025010700341c509200320000e0702000c2c0004144c40d844405250191b03c0302d8111041c1040902d0024001c5440314001500359801a514081280960015103185003407040c1150200c490240041c481c0c4c00312440341c1c000600280c07204071442440c1840b6043c1642e605200040d00c0750085000255a081502e4000c00068144c0d00c000c2c0640c005000b54500d15401c03100022034250070480140e80c8201c18501201e11100301c0b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 626678705 1250 626677455 626677487
    0x30c070303170702030f0703030513170706110c070501050d151815060525200a0e0103030f12020408060106030b03061f05040209031504060c08070e03060103030f 71
    0x81500100341544070580200b21660b2052a40e095103c601c001c0380c0700d00c00c3c600703020710002e010000d080029110358004c80d071008401c138150b0140d500300c1d80c901904855800c0c006030040c00215112081c01428400d052081260b104481c0ca01107206e2280c1ea1503290a00c034142c1440310203e0860985981504408800c000300c05007451a10384a006080001022075560340c00d991a00e244400c9000111600030291840340c2c4406080c01002d4005c04401c0700448040c8614400c02e400003000a00803411307840d02449207010074118544403405004900403140e0091140c44000e40040012135040031600d05660560b03d08800443c042d910464007a10895000c442c19214090001850aa156110424101088003910740c582c5903a030140d181c43e100302900d60f24030b041d88101045586000c0e4024240d009024003600c40118060254008807403007160242c84041c0c840c80d955100c42d1348030b030742158030244a0510032002d061040200c0d9894072b05000c01010302c01c07400d524204450082c3c0e046450701d009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 626679955 1250 626678705 626678713
    0x13060216060618090519020d0b09030405040e031c02070804030b1005010f0f020c0f040e10021308120702090a0b0907020d1d15090f0603010b090901050d0b0402090603030c 75
    0x11032901c50010300491184492803045041d80302c0c0d10510714041c88104075080740080c00ca640b114050005490180314040313a01821b80c4282e10000340000d00880c0c41046490080c44e11a4a48000c3c4000c1d955001e00d06200d60b08200001d0852003d00880b8030024400410010384030346092401016512031500050860a607a01c100103510000e80007207000d581082e82c9841d07010035038450039140c480d8091940760160704490311480a0342071003030320850350070320062000c41e55010750603105003001e2000154100c2e00380c0008100c5a40f02c0c01c2c034260300042405200038032183d8041c281201c01806511402032140707544002048181c003007500407102c00d02e00100110703000d080000c1d0183d40c80f602303d0321900100e1180001e0b0081014052449045010003622880b0400402000792041c0ea01100088c0c1d4801d24111222401ea281e43e0065806031030a140e6560303840601608008410308160b0000e40300380b41c00f0f6103c900261a50080540103503040d0307600c0d4030b1619180e00180c1507001e11140801184a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 626681205 1250 626679955 626679997
    0x30f040615090204180e06070e0102010f0c030917040605030c131d16020c0a091d010e10060f03170904090819030605061218030409360b130602 63
    0x3a82ea0300800460712140d401c82000b200000d80c1000362410b000850070180c10400000f90058011248402e803c80140300005824001d40310345000c88240c2155140040e0b580d004020030040030039103910400c42c40036580c3d41014076199006107284401048418460b6020070035a951020360a1054040c02c448684044e1301c1d0300001401c024034104030384402e604100020507107041070012900350b810013000761244807000e0400c02104050b000c044500b5460412600886940b050300780300310195944298080d100110150310060705841c3c040d00121401c03204c10340204002098001002e1081600c2c0034803680301e100003400500240448040a854260001120b00003180006120010280d41e074074100982a15802806050b02400e00001c0f0901054404900e241224002c24031200c071008045916054403540c6800039034060001d903000350a5003080c0e1481107550072144103039408140d010200c0d8103515840340202124060801034100741e40120030000d0010396012510b1024201c1100b0385408 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 626682455 1250 626681205 626681219
    0x9080307030209011b020603010b07022704050f011b030b030c04060314150405062a0a03090b060f0102070608060102010f14041103060708010e0720010e0601051203030f040615 77
    0x140c40380f4401c80c0042c08000e42910101103190110203030b5900500304905580c04c00c2e40e200505d9001c142c099a02511000e0021201c01602c1120020340309607951134505401c1c6842d00514008240c80c407001c0990505041e205441b48a4202d03c0e034084451601007484c60311100403c4c1081c0c0c69180107038026051080202c10710500c2485900c00d043c1e0003044906400d440c0d06440004982991300a000e5045000450f20014041182d42404a00c025185c0001d250440d10f4826591142c4038560229403a00c03000e405100301040e807203501101c00e650100c9040c51420000751905a6030240c07000740303e400c84c00300b401d0b41d100754800d061410500320f08101c050025228000300d0038007181c045956540c81100149141400b1a085008603020303100c03c00c60741d00b0030100200d02000201032104106955800c1d8495444403c66030001031000c80c000603410115003006810448143c11803402a0f0182d203000c400c003c40002107a6004c500c11200000755140d500d482006000a01c9441034000c05200000c02c000f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 626683705 1250 626682455 626682457
    0x4080303070801030312020901020a0204091103060406090c060e090a091e0515060a061e020c09040b160813030513050411130f14040e0c120106051908061801090803070302 75
    0x10f603002c2c0d21b032000c0d46101302407803c050344502d80e14a4016003000001c0801030509400c5004a02e100b805505c09020010001c6803402a0850301503d00c503860306040014050155101405000245080d1000d003142070041072005c800504100c0170256900c2c0c100052105050b09442200300304404c00343c010850f070416681c1e0f02e00444030300b0b41c01d80581c400706401d071820140700c1e0100c1d10591984d11040440c41500a10344e407400078502c0550040901c407042c9135072040340291045c1d1281c1d840000a04103203255500c103405c0e0202d500180401c07441032241c135807203102d81030541c2c3e41d0502c2c11690f1036005100e2800c01242039481540c0080c01c01c000e0846000d085000740509400100d502000c85545d00b0500b03401260a1143c41c10540304644500d240d8102500214200c0b02284125952981041d01007603180700018026161039568140030b111600e0040b83d028007500f400c00d1108203581c10801c8503502e07800d018243c20342200c4501842c081000b000c1d0003004ce2070ba0040a038a031280b511ba8800303000303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 626684955 1250 626683705 626683709
    0xc12020c03010518070b0a2003040e0c0301090f0c08160323090d0c020d0b04080702130615030e03040909140609060105040605040e1f020d09050c01030c171b04080303070801 76
    0x714050f4100200f01c1150b46e02c02d0301c582509980d00c01d0503405916a0801c171801ca4400305400d00c2c0420031001c00c001c884030414602995840051035034070f40c505100e00c0115030404010552050a05c010641380941c0400456008a00c44024031160401070701c0c00c2d0010040341e041e50a142512501200d411403074640164440d40c0d007030b070a035400c1c9845d649046440c4062018000c2d800110384a2640200c0e903a500030a6105120741d085502d0f14038642c000403500f42c02d06495000b0240c0343c40b4144001c0002c5504030928582904050008862100d0718075203c0c040c60080a15075613407629444144001c480303061504500000c1950f15905000754015140c070b900b401418026810603000003000c0c10113109881e80007680c01c01030010b610345502880300941250030032000c045d03000e00204005107040c5c860011050710600007441c44170740d48000981a900e041201a00b03120358020b45580e0007509003501a0300061852458500a82c502080e9a4034001c42d0080d8800340700c0401003050380f0b9003000075141 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 626686205 1250 626684955 626685001
    0xa020a0605031e0a1d07080d120f05040f05070504092003030f0c0105090606220e070801150302030c120d0503040501090c030f050c03070b040513060306050907061e0c12020c030105 79
    0x10005c03807260700540d6074034428410b40c100c90707024180680e00c880c400c6a611a002140100116004400714810010b4560030340701503459000302113051080000070080303030b001084d05840c14840100303e500c401c4060105005d0400c0340808141001509680510031206580a00b00d00c4035224249400803900030602101c500360746105200104e155442e00e1204242c1040690074080f00c0388610b2002c8202406900c40c1e14402c1c0d100314000410b1940080c050f00c4025180031405400951450042529051041100600481c070701217424070720b84400701e2000301417a07150400c2e139640e0f01c1d40e103003150050084102c041c0c0101000100441007101000305070414600035021910210314a50405403207110f28402c04109940030041000f180c00c045101c442c1c50801d0990010300c41d5900d460f620b06586045036003044c1904034003014006103810010040c1c1195201d201c1c0403902c2c0c4003082c090207680f07100d20050108051010080c5115208029951b01c0007005002072049042104003501c0e011790380c0203011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 626687455 1250 626686205 626686241
    0xc0312041403151f180e0c040606090608042a26061302030a0506070f020d0504050303030708060d140615120601060c05030f0a0915020a020a0605031e0a 67
    0x701a882d0000303241040704a440c00c082c3c9a0744500aa8186000e64102c3d070b810840c2e9070403c00140b90014014082031968880d2001c1900744400740c8803070625902520691280385001305c2030240a038403e103e401034901ca0300741103420f900c2e203080c01c100034050f09405405500448194042d0384000506600c111807071826984004019a01c0000c910982480703509140d5000700001044101401059591640098252a00413100d51200d0303081c40c000702c50200104005002e0008060303410003406488001601e4091304187c00c1c540041d440e0710020349124100124100400c40e10b560300207070001c0c0301d41c0c00b030b803050081c1c20081c411075200d20088400032845c25008628104a05200c00c84240d00c0c141d00001e86101c0c2c4c24541c0680b150448000c00340c5691006000d42c4014500034002019124141d071224042c80c1c0c5840b4003145001c3e078903145c6408540040d503420006807981080c0800340c13085410215180e6641c0d03e21110540c0814602e0111400351030b040c04150703022980118004001d07201c0d00303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 626688705 1250 626687455 626687489
    0x4061b030e0d0825051b01050613051801020f040806010f030b040b0c040824010f050315180a0609020a0b07033f09140105040b073b03070807060c03030902030c031204 73
    0x6c5400c171790080b04d40c1c9801000f00d0700001034241d11503105c59440820a42502d5240d080c41c040582260800440001c180342c00003410b01c0805000c01c001401460010141e484c1103080d075640c0c60348460054801040c1d81b8508000c92240104141039038081e1804108480c03c9a02c8000017007034980e4035080c00141584000e00100e41400321a00e072406461b03010b0300600800b8103e00c0701d4100c03110001c1c034030320394001032402400d4443d0003480140751b00c070b00603171020860610500400001401d203a01c48614100200034a00019802c2607140036241040110b190403580c2d00300840c001040101105080c078a26858001d000790496480104024000e000e08080c0c40c80c004c0e00c150880724107842c0a803858900200080070a03110b903c103070000d440b81802c02d103044070106900c01040003640c0545008222000380ca2425404c08103c00c80c01003001d180104151850000003a0904d1010320000c0d007010788a004040654404001c220044c00002d021200b8021b0304144100143d0824050b20028917924450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 626689955 1250 626688705 626688757
    0x10050d060f110c0d050706060f031505060306040201090311011e0306081209010e090c07020a12060b010906091205031e030403021b0a0b0c100504061b030e0d082505 72
    0x2030f21054100c0400820210140ca10142c1d16a00020021240541c4480010400c00705d1602828011803050101c0c001070700314000100140c96000b002e185c004c1e404882004050f07a408958103040303030b412400c2132080601040048030b020380128456000510014010007856505510010498450b00c059440c42c50400110024074480d842019000410354940c421103031501c0580310360095440c1050628083d520350220b0851502d80d030060700143d0310140040140311250141450b02d650918220314154289217005e4403180c51400740c14030307072a070030340d04032080000c20001c49000d019101c0c4682509503c2d00202c2d603042d03008650850042c0100008880d0a2003842c898150001c3d0050440721554282008c03500540c010900100030307071095440c40300d15a00c2610595010780d006040c081240300440c1e801921140d2010740a00c100751a0100c00709070788002051130100c8248524101d80d160f01c401c0704440d00c411514258040090140c4050381210303030040010480303500c200f88003544403941320320307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 626691205 1250 626689955 626689957
    0x21e030615160b0c070f0b060a090e07091d01150303020d02030f091e0405070206060910050d0b151f02010c090503100924230c0a0810050d060f11 64
    0x180550032042c40305900c0d030014031030000c81c0d64000c24080c20f041c10081c2c20b4036550041b6580c0c49083e60358290b208180112428920702e44800b070582c0e03580070b116060310700700c25036640d44480c800c144030b013590f079087c031410004808401c08214030301d80024806801984000300c2c54642c0c9100803400b600c20740d529400e440b4004003d40b80b11a100307e01311410500b0580a105601380258104100010350005107001c0355128400c003809a03c056004044510307005007072020820b400303045080360724a510000c010b90b5036420503a15880398042c0105509488071450000191119400650f004c43c1400503221040511070540e4a19407003079001740862408810140d910f038699010301070300342e081142c02d101201c0098010110191082d4442503090440c100541d405d4801400c141c1600358448202d030f1000b540a01d408608907103000c0100141d410441105804d6104036001002401080f000150301c40c42200c3c10301c0001c282c042c080c0006000c041ca411001806501144085145007a02110403500418 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 626692455 1250 626691205 626691217
    0xc0f050315010311150307032c07090209120102030f0a0f1404030c0507090509030a1214060d0f02100e010809160b07061d030702120a020109050603040303021e030615 73
    0x31401c14401e0b403c41d100d450701d040c3e040750702030b8101c1d110800904210309600700462007500281d800090069a045042d0680fa41d849041c0030452800050070244810114a10301141e4500c20011781d00ca5100300802c06a0340301e1a0784200320b51000c13040201030301814403c00c7c03144020600c2008000c600b400002c0c100c031030ac1d22401201c1d100000020340007a010b6500005010300550441d6202503641d03500100b0f54100702c92524481d0004980200d1240e08088001c2034004d00060600104001142d00c400c80e0500a0a0f180726a410707004007410b0020006203c0d00558004d001e240070448408405890514800200360019001a0009010140104205291800f1000c0c03c03200d00340390000741c0d04140c0181d441540c02c99a1542d0710100d402c02c1503101c9004012041c09561514094010007507902c01962030210183c008c1300c10f500c010303a031104512003030321070456070a5103948070b0b0b00301280203019080c806052421103c1c0c034900c01c6007002c0c01541c86010f08468081d41421490403100c43c1d80100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 626693705 1250 626692455 626692483
    0xf0606101107091e0c09080f0f03090103090201050c1203010e16020a0204112502151201050607060912090f120b060402070318030c06030f052a0d090c0f0503 69
    0x1010303c0101915084620381c0d60140d4004d1244000d5200c02ca0115600315502134045450789804200700d020501107203d29066070300c0600004034030118615203c2c400c5401003410142c0e91200d1600316805581950b000380c40b40700c22613510015000320b403000b0754020301606102105200004a09504070003607030060a006501920001100798284000713000d003010ba0010620040c84a0041083c90058070b22060507900342c1d2800707030556801449100c0041550160400c042045494001900c0074007950440f10141da450740c3d100194103014004082030310000f005181124546040310b5400021f0030b060380d9166003824040b40d42c440e04802c2a0383e05d010000c0c4034210306800112030303107401d6001d02103d901a00f4190310703601c0380c150702500301c0017150000c0b0b4a1514000701400050351522076032000800c45401040b4a06005010ba03c0c040004010600c003079412407400e00c020b94289056801015180b84148656180c5103804005030032075001d517950700130384408005039500c1d00051241031a058 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 626694955 1250 626693705 626693713
    0x1e0c030301061d2b171602040c020703032307060501080a0210020309150d020903030301080d180b0301050409110603070201020d050f0f0c1e130302030d020d090b090307080f06061011 80
    0x2191030443c01c44150340d0054640140c0f001c5500704522a4100500446049086c4603880d0407191042108841d04a0120300440d4022300d802e2001079000443c1d0001408002900e01c0c00e40f02c54106540f4511800c0f800608680c20040000744481b800200b054100c2c1c405c0705c0e10548410b450a0480c2c1d0381c061441c80360ba0110704450b0103458580c00c04000c1c143c445201c0d42c098600716100340400c0c910340c030030707400030130694010303210140226800944040d5204040a800c1049450034000e26130038041802428481d07607490b10700808004030090508a0914040e0410351a45842c28001e8001e40001c08a030b5400740c00c000001d00d121110500c1c0d148140c0c154411589151685440411170750003020a850b10400c942003504001e0310b201d0081c1c42d80c00704441b01c1d801030906502c103040c10102d0300324200c402d6510402c000780712950070241910996004011250f11034000100007840d0044031b40c400340396802203001142c0d02d540e021808070700c03a034020f0312581d0300900f540808581c40d00c07c1c05100003140d08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 626696205 1250 626694955 626695009
    0xa0b04120f1d0d020406030506010501121109040c030e070e0601020f01050c070f02180f0105040c0c110f030c122b090e070c02041b0f020109081e0c030301061d 70
    0xa070380300701a00d0040b0241c980400321610b6800320301117030410342050303600d9031002004015540e840f0501840e40d070703000042031001542700d0030800f07014019440403d106940352440380781110700c070340c0c080c8071409011400c0b1803049076128942c00d0500025110940140249814851700820500034140114030b04011540b0b006515102ca810301050490126404481001c8000616428690542c05a0590310310081154034000c10001250040515074017032055000791003004c54040104c251000206880e0105e0444803100040d080004951103150b003c14000c5c1020704926000030305845850f40d901140c0e1550403109a0380400c000d00d6030101c000100384103002d201d000b00094441e0b03003004181c03d10540180e40c41e400034044d40e883d420100c00c0d5024084590b2034040c3d000c100390440d07180500082024265503110f0f103405104162200008200003c0c480c66034450b08021512510750381130941e0740300d58543e04000c0030005600780f4400703811102d6600c10010b1070104066a6405010500d01000301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 626697455 1250 626696205 626696237
    0xa060f03140708060708010807060c0218060f030a0f0203010b0a08030f13210b010e150634030809060c07060e01090219050301060905040f0b09030c0a0b04120f 70
    0x80c80d605980c4403a07006840700022500010013910f0300075012519585400d6042000f106c9c60300010340d1100081010420000c4050b84071615000849540345602c0342480c1e440c480402c050504000702590548100031280080c0484046040500c0d4401c50003441582021030400280b80c0450060180641082200b07090504e1400010031080803201000d519495407241c40c0c50603603040300462802180c0840441d0704100c1801c0445024014044a21110b4100440c07007580311820401c145016910003c0c0000d074511140514030054143c0503001c04900c0004a04100841030480c000c4000c102880c3c00b060742c0b07030307800315504d403081c0000b504c528200400c50f215030010381000900100306550310720b484009a00d45040521202c400407a031107481c07a1a0005060031508035900001e0001d1411082c84000344114484210300ca8021086003020745802c0c00150451152601501e0244154134280b000c12120a903a2803045006448800c0c43c5001440c0a0350f0625215648800142145e2034800440d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 626698705 1250 626697455 626697473
    0x308041211030a0b06100908030f0a0527030f060108152e2111010f140d090308060303070c052209060b040c09140f010e0402160b0a060f03 61
    0x554001c9030300c807500040c450040382c280103080c4020b441041d1400d08000320740c14401c0440321b21a0303503403500d000c0da2881c1c4084541c990003007106003001c091000503003107a007921880541e2401c0f0000700303040740505509040745c8c2840d0004201c082c024000c03580758005032100812050704881904c2c01034103901468610f011003044009007012909109191801c8205120910345011843c00340015954242000c500804a4045490303020300b84049a00302c0c00003520040066110040030300300080940400c1c501550000302d020b82c1d480c4d41000105000907003040b01d4000c08103060091b118104151a244249038480c0304486014040b40120300c401c00803030030201c2c104180991144d44908004800305000c1d020b40315142010307507456446602410b100c0c58580314440020300c0900f040308681e072070103a0716002c0722401500203101c1c4507400010a8907900032918000341c03a100500c11951215080e210424500c40b110701520942c49031000a00d21310910720900064440d180b10000805180d07036500c45017 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 626699955 1250 626698705 626698739
    0x2040612080729040506040209061504050603040c12050115090920060f121609050112050919030203120601031a04020d0902100f02060702010603030905010804020a08030c010207110a030804 83
    0x83c0030f8128215401c10a42c2040a402188500060801070406004105103a500a4410751054411052414654500c2c50843d002c448090700d407543c6a03a00c0b03091031200d803d810303070043c01c0c5030311a4211801080340651205951010000107984855140c805100442709441e90003020004406171908050319002800b0001d460b0003442a031614408111601564000d21054141d1180d59001d201d680c1c1a00080e4451041403440c100b641c1502d008002410706a616004d404216500e0010a5440800b800364030451103258800c44d008680c40c0c41d0095903940011650110640c902d0041600d944c4640504502c408100d0080e50310000c074402000000d42c40410250100c95651074200700680f101014541583c00d6030f281e614421816040280c103014009001d1021645032102c1800081e1b0400541826114203280800e503582e50b5101040300301082d0341014a5900c004100210007540540060605a2158505120005880e002e0003040e00250000408621051005000601301d6103c5012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 626701205 1250 626699955 626699993
    0x111040e0408091306090f060e060d08070c0312120b040504080a0f050d11030709090504022d120102092d0d15050403030b09060f011e020f01060b07020406120807 71
    0xe0130300700c95541340407201140d10605039140c40d030030800d121805902c2140300078100c40060350160700e408800103000001034007008005070341c08280d120900409440b0301e0040c1da88607403030340004800c00348081c2c600c1061140071903caa00b002c1c0403418034102801081d00855102c2a024240600510b00356078102507603112000700300080c043d0029041c134034020140f5003a05805040c0e6070b824040002413441440c0d4000400c1709040c40b09000058590008420284c90340324507054128241c10500118080351400b1150301480c1d040c4d805800d402c1c194014000c1580c202c034003034100c0d03041d440440394030807401402c810540103000c41c06e0f245083c039040c0441c00e0792040d2481d22007050381342d0405007124010b031015000260745074070303100e154104441031075089031040756001001910a4002049141d03490002200464506061340a4174003c1141641c0703048000000d10815460740307080d86084d0484071050b8452401d020001030030190240031000a0b5421003503942c5002c4007512940c0c0c0d05550b040c2150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 626702455 1250 626701205 626701219
    0x316030e06040221072c1014060403051507020d09050918030708070b0a0606110604140313080a1e150c0c0209090a0303050c03090d0e0d0b07080103050111040e040809 73
    0x794140010710aa0001d000340c05100307100c85c21096450040714281302c6c0b800070498480820300400c6080c0c440810102c1c1d2503e060745986000040100302c26002d42d510040c2144210514403c6a04924010521461881d42200e8881d160010704940789552482143c1d00408280c0100b2003091085c007208001d1114882100e28014003a81c407d1a46d600c960001d440310004001030266001c001c0c02000010485d914100f09040d08440d181600d40c40040c00c02054140326030303114400e560003441524040441d251610351400e64881d00203486004400c0100c3d141d40c504240d060302c840701145040c2555401c134407803501002d6040000401010403580d040284039410104e00c005a8481c0781241c403807101c0750082e141076042840c0140c1983d03405000302420910501c2040452070b00041d000300081400d18204c50506e00e1b102c0401d8090f150000040c103520304486c2082686608170003080d04030b0340300700002c00a003610710f0042402030281d40201c90f009000807012401042c64038000d84802c2d00014049 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 626703705 1250 626702455 626702509
    0x51303051602030d02030a1e120b0a030b010807030302060901090308180c0d150515061804021b011b09060c03080a0e0714130b030a06051b0301060201020316030e060402 74
    0x2482e0130100303841080103070310000d0603980490f80855140d00320403854180c1010031344003801c0a09030805550681207216941e0b0410001a5584680c1c40f00460f000003055110f941c603810401d8031a000c0d400150301501c102e0002c510002414410101140e405a40c0c81000e500c0d045004440d40105035140c105d54810340b0340d01d000c02e84d034950814416920031242c8420740d11611700340c98207413a1b00400c00080f40e100c250704140c01fa141c0c40100c8076005000000c03082c0410740c260000d4002c2c092544690714039078030059a9610944158041002c81d104d003221040030b8035055104135003220290180c1d00000e500f00c4270b8140001e000f440400e40000364240040780c000e50b8080100e141c0002035101a92150008402a1550601e11803404001d12140428400403100e00d02203556151250002042c46030f641c0c0028032000d4034500200341e030303021400c942a034a50f550032009001c0e410581c0d06181c404100c410162159000340708480608100ca000b510560b80c45030200018080030140c40e1b05042011800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 626704955 1250 626703705 626703709
    0x30501020a0305100e06030607031e0603110f062104030507050d090f0503151317030106090311060702011b0c050406030b1e0f13060f060b091201051303051602 70
    0x14000c2a0802c2c2e0300041e542c5455003200942851542c00401c0c00158001031192985010941c00c1d40308c1980c0c18003240d084c04550600410b440b51080c204946031405102100304440031008020480b4210703030718201000d020080000a100c0c40f03454810b02d120a0810068100a042240341e005009080540c01c117000da0301e926080c983c070a0456070008003c500240544281c0890305c03009000300f50000c0410001507607020500040151040b2022181c44513510100f01e07204280c080c40740b5140303a0840e16940d407840003616000c0240401c40d03098404800070300071402c1c01c00a603410b1940580d01c43c000040b19460340703503e00c4040300c815520713060030240100b0380381ca039070080f48021441008807081900c2e0040b0304801c041142c0340004400d1060500f031000b0f0b94000d00c110b40c5c01146030f075440c40b1004014940340b80100304118045d00341130b05104000600326051000b50410301c10507211078014003c140c1038030b0b0898400301c45030000d1030540f0302d580011901c00c002505200ca01c030340a0301070003030450f00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 626706205 1250 626704955 626704957
    0xf03060504140a0e0607053103050303070915090b03040204060f060203070218071413230102100501030201080c0c0102090409050102071b12023d27150903050102 71
    0x3410415070b50070018048101900d1140d04c40c2245080040d05880c100315500400500c5148804946066081c01065468051002c2d000041c103140413151240c6549141441c1c0740c0e00111600303004194000c2e00002d000031604445601c41d40c15585018100703091180c000c002d40c2015000345d80096a6030310200d0403886400c1000b0103800304c0c1e00219120700903441001080c100114404194511170014001c546411102d07030360502810304003c1d503c95440e81e4013602a0406640035504102014490001400c0320140c1c9045102081e0701340d42c4503d8084444006441007880700178001180d080000344031600080141ca803804240f03001515080ca80800078042d54100c9400b0390313480e54000343c19410444001e5194404c409410125003003107203004021019a90311041c041e000e1328038010300c5c407180c440200c0e0034803403400350300d281e0301e0305500c515150036030000c4200e03030355011510800083d03081c0c201c03610b4150007914030020654a082d050000360481c82c8158510541400315040b80032002036804c1c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 626707455 1250 626706205 626706221
    0x90310050a0b06130501080903210f0c120f1905012c01060807080c16030207030203071e1802070b04061b080f06041a0307090e01060b0412030f03060504 67
    0x8004202401c1200758034003194014030760184541020820203012048030240802200c609081071060b40d602c1c50401030551040043d001e1070402e07000700e80100480e0800040340a485256981d000035034810903803000c644240c150400c066040134000810808044228a81c0445562007130443e040c40f45a03c0010b47d00280c0084040281110280341020340c2000c50201301c0700302841801e8194500b48000d00382c0400641940200546900040c012001c030000315000d014018074404264811800c0082d00c441541c04101d00c280500d030b80010301217030007041203d68030183da01d03686103107071400c130441040910160382c818400b5003c0c01a80040b034a00135000d031149020715000315a488440c007100044070b00108032082400f5900007807204449040ea070165011209940c0081e2800c11000804858a10414510390620489030b01040703d01442c0c1001c40c400300408020300610340c0f20000f61807640a103001d540c0c03d801d5501c400a000c20304c81c2d1041c02d0300103494240016107a407581c0219054444103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 626708705 1250 626707455 626707483
    0x50d0902060c0d0203120907030209040605040807082830061a180102010203010f0902030402030a02101101050a0b0f1509030105070302360415210201021204050919020903 75
    0x2c16904a0310541c98400356107c2c1d4034901500865003954002a003a00d80030b400540643c0d07407a0001f80400c00407200301c4881c250001101d42e11200313460364241901c0d51405a0f00d2035200c131601800c104902135800300400040c0e840b403403003891101d14014100c0c0300050440018064641d136000814003d40c80c110b1489418100d0708541e0356081303000000d8485c40c019680f5045a00c10001042041c0804043e0380031707100000e8016a894440d40000781c80c0a900010103035025440540c0181059000001d01d81803d02c8030f0003d2003d6601c22440300300704c030b040440a81d00216002246919840c00402e94540c1c802400f064901b000c2444d40071a01311101201c048000c2640051002100c00401100034190310780001c3d20200d40d2141406981240542c8132124000c5d522558018a0261030340e285034040c1483da0028100c0c208100d04180141c10526010b0780940201c0820000c91003054086900703550024151850685801c0481541800114513401c0419401e10007542039503410310904406940e1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 626709955 1250 626708705 626708707
    0x12140f0412090e0f0903070b07020313090e0d05030612010c020607031a24070f0609060b0306040314030421080a0c110a0212070b0d02121303050d0902060c0d0203 71
    0x5490403002141000032541d00303101c11a1010042400c98000c9998860740f20b011040503a19140341c041c2c0f8501a000e0300500c031404a1003000003840d07000005d0b22100d0008524500000c0c2d540f0b030140200c2d40160038100080c0c11041d0b561801c14020300055410010251101c0003c40c0e46103882403c48180c0350341940141c00c490b05004030954540502245041d910302e011a04105000016402c030248040350003050900608819020102c0002e550000c0d8009070170485480240c6450401816070b0103040380d0305c9240020502860400098445c4181d516461303541e4210b00700e01d44c1c2c0195810080c02220110801c080100c0a52510191050005207030b4481d0407071b908084942805407003c81c03100d803042200301000c4000c1d5600006081403001d8068801902c61203a0002c2d5908188158000518008001541d010802841e80c01402521901c100150300350b2100c2c052a1101885800050000b40e4103000000e040d1800f5403251010620042080c0c3c03038100c440740c00a081c001e048100c80d0140e08 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 626711205 1250 626709955 626709961
    0xf0907030207060c0f0c02131b020708121e09061e0c10051023040912030c0306060c0b100e090c01020601080a021f05070602120114040501050303090112140f 69
    0x4001d005807100d1380c005044c95841e610301703041c0040c00c030651541c0280c420f054074407d0900410883d03021051890b0f4909000e0426031411002940d00d01d03243c45030389914071448208000d41d0941400741d8000c24080d031452002c42c00c494140d144141c00c0342010a0340558200001c200c0e00305003103610410070400729030240d194020381200324185072007200500300590500003000b40c810181016002a41c5100c600501e420701e40380f0708880d41032886c4202941082c5410000d205001181184180c05404bd0f40d048c4100d1425003411070980e2214440e1001203007661101d800090380d104001030380285521000c00805a0f1001b02d60030080c011303546600c030703034004080c00001c5581c1480118050840385000700030034482a40810441900207030992445501c40003c030801030710407006c640d00304d600003105540f1445032102100040e07400303218000e078401800081d04154207160107005d04071507005001c0c5081c03103c031200540305040e0f000d00070b22100d0390350312100904120b071a10710743c02044040d4000c81c3c249 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 626712455 1250 626711205 626711213
    0x2070504151e05010906051308070b03040c0b0c03071101020f060406020c01181509021203030403030f050703051b1602090a062d03020f010c0203100f05150315060f0907030207 77
    0x703075a188800041000c0039105103c0759030000c00c910100c07002450312540d0340c1e416000400f0400c1c42c40d0480e102600500100017885400c2c00003460141e400f0300d103c1c07020280c0c1c03883c56480300e10411190100c00d03081441900c02066000c884000140c0d0180107941403841ca90784050700b011003c0b80c08480003076011500d0f04580300c0074031031003405d107402c07880c500705a4105031140c50303450120341c0c40c80613100c3c4c454070108110348075020300c40807402840c0d080300d880303040a00d8090042c000710120a154245080d0000e04010b119019141c0a01300311143e9030601c0c04000e01903003a0381c1c0010b5220403000346800395100103803543c9501300e20440c43c22800084c150300740b4103103009051a140c102480744a088040704540c0047d0007068085a60440b12030011404103070041e26500c2560101039414010a101c503070620119400c00380b94204884400c20081d80e941150041e00440303402c090f0b03010381c001c0108031182620180e18541003200140807654811100000548000041714410006500811024104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 626713705 1250 626712455 626712479
    0x103021309122c150c0a0218150a051f200f06090a031e140a0e01020c03030c032a0f030a0e01140901030203130b1302010215010b030f070207050415 65
    0x40f12500d401d2044561002400c500044000c0c29020000000c000c8440341d400c020038104550b0140116000c01c05107003024004400403901d0b840481101a81000940350030341c000c10948034000e0403140b948031090203c02408095140003010300034502c10001000c9101c400b6598500501001000e05421b201d07100d0342480f001500001311640060728a4000a0b0000c80e60540701c412244000c1a00303d03501400c03551208007604031420704800190418680d54030149881032000285c00303c50401d4100414103940744104410300b071150301b0500088141c4420340501101e00010300da10901d101705007840380b80c105249440e50305001d91000600489558000c222000114400d0a0588007004541141404c23031040c0c1400702d04041d40040082c1d070806401000d01d14140d001070580015141c452b4400304c03620300c1d0007800d90161080001c071827840c105049909042e200010009811500c0e00d080d80344011001800100a5005142d0089800d032124801d58416001c9590701c0c9071024a0a0b00388501 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 626714955 1250 626713705 626713757
    0x50301111b030405030c060d0f020403060615020f0c040f0902151c0207020d1502071a0108010608061005041508010e0102090907020118031407140a060b01090e010302130912 76
    0x41d035041488200601c4c2e4002c02c80b034030220300a590fa140d898501d00316080082c10882d000c40c058910100d404070602080754000c105980d00e032914188105402c1d4016070352408110420b812039401100342c0d054509007034210303c0c20004094400f1030500c1c0582c3c001020b0882c103d800c0c003841d203c0800c010b00f41b40802e601c1c00050700c24011013140f81c400950081254082002c90241c81d65a00c1c215184500036907504403414140c020074000101c041070800c03040f503140e081c0308078030a5609224000c03403803403804583c140c024444460300c0190280f601c0280805040003160b082c2002d42840b81c00140842d080c090003201400c030a000594031517241e0208407440d2000760444085a01d08600900007024035034403588420b80508060814080c1d07040401000e20543c280240785004001c0454440e071400a0041c1c04244208428000c01d007400c801180c140170035201d002420a445001007000d414008030305001510306000200d04808135840d0440204554000d00c800100402e04811641854001c800a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 626716205 1250 626714955 626715007
    0x209180a06061b080f0c010509010b040e031c0b0f130c0206160819020408010e071805040b07110a29010f260a0b1306050133020705030111 61
    0x180480310304103c2c0e11001c1043e00010a01c0784c00094100080b4690030544001c212000001c2c4058588110503e0281500c2102d06001c0c40c02c1243c1e0030f1100c0004800d0f02c5040152821420400e1107a12111001c0d003103400c03c0c17980021007802044125122144c0065000150100114038041c100034000c1c941107008002d00e8500b81118402c40c00681e02010b0140c0191051542c00b00c0e10480b5008040284919842295658604003101108560120f40081100d1895041c2210a02184000026200225401801000440c00082c130841c001d450049030b82d8006011108129115500c00400d409004004101c0701c1100c0d60425100d80112010b81c09007280300500c0703003c189003611107100c0f8004124107800060f81340c3c01d1410240810049080388a4108078500020300f0552245541c0e10f42c0c0c42004d4030b900e41080004a511100450b00030b0000030340f51000d40c0c144050101e5844402d41c1c141e02281103010345100010a035909005404a146210081c0d0b0713134600104c0214a803a4420080c110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 626717455 1250 626716205 626716217
    0x414061302060901080a140106090f0f031e110d080702130b0604150c0602070c0614070c03020609040e010c05030a1404050c09061f031508010218130209180a0606 71
    0x1200580320b02e000e60340038410038200440651a0811140d000d4481c4c0110400000100c80c000240c0c0b0b0350000028003180c00e100e08c80104c1a440744041c0304144d8507408046e001c01c0c030540312004221000034181300d0407401040300329804c00d0503d0001d0101c10400c10306a4612001080200a5240c003418101400b03850b807404106440503107010509901a41c8140c000d110722103c6042803c9001e60f5140070b45980c003560855130f443d12840d24460b0784040d40190300000e48100d051041e03d010910468508a410100f800001e500d96420086582d008140464205803212115684001c09004052060720141c5401d5201e281c00420041164a030400288501402d00e040c000130036408984d540c4071190594281800b03036600b802003001c615082000d4103a459110322700d2800346030b145d800140064500c0a41d2002c0b1580c0e28007113130907405001c00184824020382c3c0780702602c0c03800c48a90702030506d001401500340084600065082d1318100103460800125904210003d0024440d02020b055142040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 626718705 1250 626717455 626717491
    0x3011e080a030c2006030c180303030903041503020f0c010f18111216060801060206250809070f0b03060909010c0203120403120c05070204050a050613020f070209041406 74
    0x145a0105058081c0a13003103060b111258850501888084c2048060429a42c2c0d00b0800540b400503400260b681c0990705140c01c07a40703505e20300403041b240203030210350065007007d040c070801c0139090071606021300902d82d00300140f44d00541040090807203000480000184c104800d040c400a0f00c8001c11003040602003002c0701030001e070718183e9103254254250b800c4940704022001d201e260100000052981c0528075400060003584080068142d42c2254296480d545515014029041032031015080751002c00c455940e0040c49098400c6d4010f8446084501d569078507080301901d500c150b0071002c08401d000003008018100b81d40c00c150410381180003008032040d40c0c88003d491b4051070110a6180d41e0003400306042c14401d09800c201d202900800f000002801000035161342c2c01280201d00486c1080d000480c404040e00c141e900c55580500f07a1100180c407641e50728025800705961544801c0d09200700400350710b6885201d44128400c628144080e024612002d1034003c1c0101307501c0e0361012603000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 626719955 1250 626718705 626718707
    0xf0909030905330d0203040b160c0803040204200438030402060a0509090a050711010606021c110d030c02151504091e0501021305010816051b0303011e080a03 69
    0x944010354100303c0e103040c0448484502030119100d6142440301160000c000c0c0000d0210000d10140220f1800a00004c42e004c100070641d000d844507940505201d03400d10002d0054100343c0c00038912000300c01507130400b808003000325499076081900907410f40070020441000e19042c0d40ea0455602c0c411002100f007017403130320320130052910004200900a983c04a66405001d0144081e80c0a80e8070080c0386600074034058a61100a0004490360400904a1001a240765506218140949001d80e0207005c1d05140401800486030349079a07004104824003184011040060008440c1c40d1041d960103e5450b40304a0001d00d0f03c00f40c201d9a01c00180c84c281481329415a440300f6002c104002d4402158205480c2004144820425070209070400f2515543c020000198010441801062100380300e0075112001111000303011554a031002c0502001c801b000c43c0240c02401c400e8403c2c81c00c1200d100d1813120b02d2030841d0001ea11602541c03031421110503a450001060360094484000100640c00207610 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 626721205 1250 626719955 626719999
    0x5032a0406030e030f04080303151207091805100c200d0e06071202160b0403020303070f060e0f150703021812070b180306060108061e0a0f0909030905 66
    0x4111000c1c0750383ea42c15035003540418425591000c420b109020f031119a100080c58172540122a03450100002c600011410b1814400640d0701001c0c43c00140284c6050014a400500a0007010b000c4d480000070360b180041d0081000d200040b50b8030001007400e084902c40580201e000604882d080b1507105031101c940e101c00144d01000710064030706080e1351282c0501007402c45c4601803000e8119240000da4110090300000c580291152010030240c80e19562644000035008602000354513400401c003040c04900302c14500c0700c1d405d005610008074242412216450310740704124880503a003010041c2c81c4440702500b01c2d103a0149403800c007585000c1c0c003000740c040e480d491541044d200d18042803040b241c4000410800c00642101040981e403003d541452801000c05a6801d03842482100e000800d02e5100b0b01550f409800003400a00c0c625a02103101203d02030404181d640168403888005912106008640300070f00c00e0120019113075100307050007024000b480d08190300030041404400403031906a5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 626722455 1250 626721205 626721209
    0x30c150302190f0504170d0807020f070306020d0b040c120c0801060e190b040810110a1709030c06010b09041b0e04020a020712030e010f03090f020f010c0f0305032a04 73
    0x1143c100007100c1040800e03607280c001d54001da030043c44a41e00d8200980400543c1211a00050b255a052561082c01c126030300c45c080e82010300c582e0402542003000030f07a0f075005002c01d414500c10100c4d0040e058404907084444140822002a20f0a0310b0000190490b20a5140052283c54054600d604083c0090150f41414188601500c0340004c6241c040c0d41c883d80c0c41c0c0c05041403a410a54480d5240a03c42c3c3d500481c0100c120003901d850010b0f032400e1000c004a6003140348039213614001c541001803103000140020500122804100540104440207000b854003a020900d68035403162a18010301c41101c8502e81c500c03a40b0240c0d0101e148078260044040041010308490240c1ea40c10100d40490500406a100745c0750201c0b84d050385020180c100360503105111003a44c1c0e0320006a031000046044c4c1d40c1c0c2010180c002c000c4065802c000d420721542e1424034003818140800c851b242a6641c60040304a250300340c00043c00841844401480c0041046103444c1c00113410313824a40092141c3d0781e62150b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 626723705 1250 626722455 626722457
    0xb0a140609130209100e0109061d120703050105040f0b010b09010e04021b06130b100b0a03180822060302040803160606080d1e110a0303050916030c15030219 69
    0x1590342e0000e011540e01203c2d020f010261410070402d080010181ca003502d4150602e011400e00080804d40521a0b4500030f0509140d803644943e46054406000c69000c0c000400415070049610120124000340510303030040d441200d90140c41341041c2465800c041068205482e84401046140556a4444521240d01008540040e92600d01c00301c01000f132503180c403030201c05005a50410040983c0d201c01c0700d0aa034040c044008081d03403031580074000c11510b40100400404d06000032080c0328400d6100964018040a152489141c20b460300740403900002008090901601c010b014104002e240110081c00281000d40c101801c1024041d101d0140e583c4d900c101e91900d030341040600980380c10510090100c2d10aa03400c0e00d07400040241201c4d245084414500b900711440424079114064021000c01401c0282c00701090030fa504a018020103000e04655104006595014012040d00302004600c40e11103640d69600d002e290314515290305c0e040d08181881484450003184030181c28100b07803103403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 626724955 1250 626723705 626723719
    0x90123030601200f03040510050408071e090e0f010b0a0b120c130314060f0601080403030504031103030a06030b010e0f01150c06020a03022107090611100f0b0a140609 73
    0x2c5203100102075088407851006440303130a4251502c480007200403c00c0e60025140340141c281003540a0700c040c4100d04c01c14606901c000c000300a5450044070391140c0074120b0a180c030b6007956880b0b070b0500f40c80c001080400b498200c109000c03001d4801340b141211a090075100c80d5005441d146811120f03010381032170340b02002c82450004201101d41c204603000e000a0a5010f02c1041e20f13400c200c60709d9481c4447c4125544184000318020b250b4101d0b14034442c21050b519000c0340c0d900ca947c110090031000c1c0080742405043d0310841c180c01000c2c8042c610900d003206001442500d5030074050f900c9041a0700401c034840304071081c0140b1080c0031074040c0c19580c0030142c140000d140100c04680c020520715019004038808109494050340c5900203104540d400c2c0180d10381001c0c1444c1310b1540400a44e080740100c1c02c80501048554020403458100c0b900a1099940421103081200d00384d88080d40d9161a19a6600803d03050b40b030400c50410161100d1500f00d1488004a000700d1910300c94161460b01ca19a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 626726205 1250 626724955 626724977
    0x10b0702030a02131d190f0201030b100e150310050d0c030602031905091c030c170a05070215040f02010c0f0204091a130201080a0c1e0203090123030601 67
    0x741080800c0c11264050032000706200b0980c0110b0082c690000082c061040300c02240c1030214000440f5004181c8207021200045420b548008458039800001c905054031045407403425600c484001d2060b07201c0c0d44445901100c0d407820080d81e00000042d061880d2800d005010164860300042810346609030ac2e9004145411b0420b1002c0c008c6a40c0300403d543c2c0000308014044201805149005140c00c0c0c051145448ac095483c0c0c41c2d1201d810b2414025290f02160454240f094000300c0b000f034601d0909440d074410b441c500440c0311104980e845c0015460f94180002254100046000d00c0c0044c1000c8619003007a035115108400107010190411030040289414400b10032030161056034020000c1194080d985404031282c403001d540480308804010010b80c14608040501c0142c0b58140d40c1c1c034032682c0d10601c110000f441400d40400800c800c4ca010042080100d0b1403003a103076001a00195102d0111a000400d608201d01e42000303011040e1300030200f15081d00090ba03800104c2401d150311031074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 626727455 1250 626726205 626726209
    0x2041a07030c05060133051e1603030b121c0f0509120d0914010c0807050c031f15051e040b10030603150b0604050114070803070e121203010b0702 64
    0x8505039002070101e000f00780002501c01d0444800507082400c6c03940c1a8000490b0401101170507008a0a05000c00c100300008200d586001650364210104c044100d0300340a41034901c0c40e01100501012008280c2e01c0410000034501074101c1e07020081402e00a01900c0030f16401c00b0300c208013038503031070052054001040d01d40b5405035061f56607241003e48100c0720108070700d204686c0d828034410020017040c000180032403161990085c7c03091845042c0c480c850745001075511a1841d40c00352009941601984107508516a000c3c0400700c40d05510780d090342c00d15030303041c40b02a0880d504414951201072000d0010051a00d40303074401d0600c038010b80f0441d55101d00e080c020070080c00a0110555004195450101e1080c0d007591102054900610321100811072a1403d031084510107489941d0180301400108044c0d131113281030743c408150811a80d4100551503440c12041cae0804d944502c0440c1c6600074114090030540d452403500013200c0c00400b5843c000d03110304d10b001d01c01070040345024000010324100359 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 626728705 1250 626727455 626727467
    0x918050613021c0f060308160303090515010618060905100903020d060618021e0c010b0a090617070828080304120e0f010903110604080604060f05011203020d0507170a110f0102041a0703 81
    0x480d040403d8940308a8dc200020404840034010000420301003010310a1410000d000c580a68401c2c2e100d043c0c3e0303d41030000300181c150041001504100580001100684444031803000311880b4040101e04541000c5902e2001a0840a800c940c00d2040c00260303119a01c52400d03800d42405c1c03403180c640d40c511400d44a805801c0200b007003604400c071381c900018140c115500130000c035810b00e10b10021007641d048480b0b0300c40c116480384000d20b43c0b0003403028404c03070000c6040306c242e2003c404640c030112819558105ca560000ca4003035444100010341c01030b140b900100c05c0080703000d080722881c1902900d24006402c822150101400d0002d040d41e42d021251922001c80c0c0151010034200d9246103064139014016208025050b40c40d5400d040001840c001505185810a60306402074081c00c0c1d80d0000845260300a00420341d4001c4005006000e43d1300f100001b4142a52150303240c01aa0690310240341c5032440040c5192a01d0b841013000f0414131084000d05050020200d40d4690b031640b41c1d080440e05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 626729955 1250 626728705 626728721
    0x1b0f0d020616080a091e0b060102011a060d0b03070f050906040c27080f0105041e02030303040b060a0b0a180b0906070f02030309040203070801080d0918050613021c0f060308160303 79
    0x38003045100b1b6003160400e08032050640500c10201c81d06a5500d4400490989900b860701c450030008210740c000c014035022740940310007080c0703003070000d000300340381d80064a070042d0756200c40400a540c250034030684c1868400c3c154042001c0e1818801d101e990034004103090352100004401203090742c5c04415010061051000520668080300c0c44107040c0c0c07a15030f0090a09a908a0340d00b000c000c00c140c0f60004040b406a20690024007450440d0303100e460b000c540400042c01c0540c4006034800102d142a5000c010f042d801c0c0301d46d500c09613012402042895003100c96080203220310402d0201a15582c5c5100440341100c0d880b0440004001141c400310b440c501030141044e41c00b50003c0100510a80d100001c41d049840581c01c48107216041581558507902c103000f1640710f00c0052070340b010719074825004646c00000182801c5a00900115007404980040040301e00900030701001c84514000c5000345ca940580c0ca070410880f03585103954244d02c80c49070f904840184550400d000e070034107009501c0996 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 626731205 1250 626729955 626729963
    0x12190905010f150914070503130503030a0207050d020a0206040b0702060f0705011e09080409110d060f14030316030f090b0c0304030209092109061b0f0d020616080a09 73
    0x902107011071000507110380085012043c4800500284001640c05010084142102203488035103881c84111015880200103004850441040c0d0300015804c01c0154814404960b00581301c403418903205003020030028100c2c08540c02003d812000d41c4c0ca907405c4400b2201590032251fa80e170241e201090550043c650800c00380040420b42038184039040d048070003404203180c04600d041c28000c992070b0489442510107481d0312028007040c08001c603207030300c40e50141c901c0f46034050034040706d00441c04c162503c0e604842e6404209190410015250b001c01e1a03010108030091820482c1c1d14944560100d031081e005410422044088814540107e000401070b200803804580c0d2950002031465a035030161004a001e03002000019502c103001040d080b841c68030074000f603400403d80c201c1c5248240c0200a019500c070304c040004640d840c203000d65451200b00004080c101d966242d680d000d0402408090031420740d000141040b0710001107561008512400341001c040b40d4488488000040180c140c2c010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 626732455 1250 626731205 626731211
    0xb03210c160306060f0815011202041107140727050c090a1401170105063109050114030307082506141f080d0c11180f0a021219090501 59
    0x220a21549812440c2179907041031044d0702460390343c084160340f40035401002d144a08614014891185003602c0d0400f5180014000302e1140020400541250310021040b5160b040300c440c00010068203200b61001440c40550007060490004084172020071305400002c0e02591700c9001810040751102580d890280240803c40d01d5521030300c08070800406421400d0208a0100703035654002c06014010341a070744050100c0f82002c62541119070346811080403094462003080c4440d140d2980501e03040c004202d4000081125450581c2c80006424821440c500035041048420085003884045542203068081e0400000008000900344034800c030800400c4641080d060455003d0340b447c80501603410720040006514841d49982080b001c1c600c03405034039400540c01ea07100f07140240e800b07904882c003407150480d100d21080001410070007a0180000c2500b07282082c8500005e8001e511a844801144210314102000c10544030004004061894540121301507407032141c50341e0000a00c0d698090300038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 626733705 1250 626732455 626732459
    0xd05060106120f020a090302131118090a0e190c0504050c120610120b010c05030c07080f160b0c1c0509041a13020c15040302060601030b03210c16 64
    0x1082d00c1003100d03100441c00d0800d8804207120003184211000c0501545034240e000e0f01d5907023807101c45030304448031403142c5544050854103841d10034002c10125685120901c0540c4900007000302480d8082d10700740e40949410034451ba058800105000740d48440081614016110b1604401201071a0002078005c0c1c1400705001c0807450020103010f581d0704000180c002c541c2c0d1102808801c4604800b10710004000c50200b011200480e0300c5420900c030185050001480c0c0358451521756800000080070640c0215010481e0040500c466000458043c001d0410184001004420075503503004020a540001442203080300c0d0070406ca20314001e0b41801c41c42c0c110314000d00501b05411000c00a4042c5081c00ca0611103001804040088080000d0440b09201080c07919000290803c103c0506284541d16a010355080d5064005126510a60045c1000d02c0d0090004050b6003641d102203019501c04800c0340c15403521103186410a034918411140c413802404c0e1040d00d080d05180e4088540b14881c800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 626734955 1250 626733705 626733707
    0x9100906020415080601021b040204053307050a030806010e090901140a02040e01210813060914030d08072a050d111b04020d0204090b0405010819030c020d05060106 72
    0x15004650301c0d2a4029501c001c00720042d280303130381c0c221406401a0003851082c0070002c0c2d001c1d5a011600f40250005003480d0b15200403440e44800d52a0041d500d42143c0d0f80c949000240107828410100e540f5006030074041c00c0ea807482e582d50071b903a1004040c00f54a50000d6107a0b44240d40c14074404100130b10420b0319040c02050903000307041c0e00d640c0300b0783d0650360780c00113703042041d0080f0b0b0225180b0f03801ea51850780c0383c4036800c401c1109004000300805052803840020980d6940500010201e0150303034880603150000c0038020040d030381c0c04400b9003c501e107000f09880d5030124120790540f0503418000307080e41d200b41080b50304503841024214072071180010000e2050300d80c0034800b1454829000c0350f002c60401d0005aa001c5042e42c0c20340c60a5006155049503c40340004014101c80040c00143c28210002d2201b001e907000b82c0c1050700503603502c141c3d03d0010700c1e060042c140180b1046010303090281030480300e014081340b4040c3c00b40900648140741f00854940141145001707802c001581c140b9611094 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 626736205 1250 626734955 626734957
    0x7050d020f09040501051914030307020901080601060306090c0503010308071511040905130c120c0f0e0a0c0e011b08040f080d120c050d1116051608070506040e0910090602 75
    0x3000a01440c034100c000308503407d02c1c28500040300155108000030900e821aa90031051004611a8141c002400728000584030014100e002e001c41030040c042d01e40c1002001403c8403d640d00c00303505182841c00c1b1109648e001421a41500c0d00300098036540c0040341806202602e265010020312450b10085500101e00c0c20050300c265040c4040c18000d9489240710b008454807044400341800540d540100700380749501ca05020031324420714850760310a9541200040b90300c100d9110035032032088101000750203081446581c500c4d44590a0501010b042e12000811088100025100c0b20032035101030310510070f1220964000308251004ca10407140c5034944180c45e00d07030004c941400314241b1009504d2602260144684121150361000c0c00d0001ca4200040540404008269500f03010401c522002c40540c01d982030b031500a60045c62051a4070050340100c040940c061003190304500003d00c92603079101700b1038007160020182c0030201e840720701c00c59003094041611444040d01d080c80744c504000d07140d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 626737455 1250 626736205 626736217
    0x10216060605150301080c04090f050625170601260405070f081207020603071710030210030204060804391802030906061e0604060305010f050d0201090e07050d020f 72
    0x303940f8080c5401c1c0303910200303900e000038042c03002d00d0b07000720760342c3c0c010b030300385544040700780d03070040d429410289840c0d02c4041c00c00c1d01c2610079035440380002c0707106e020140b032107001890a0714007071821101704141d41b024160044405445103040107d20340c49440415241001d030460303131a10710f000c1c640c5400c1078a4501c2d0ba62407140720f141100c41c030301c0c6000a0060f4012400400ca84041c4119074a09030040e403c00205900041c41d41082c04a80d800f01000f03403280340302d064400e200c102c0301d00220a06500400a81003401513000c2c0030180100300c01d01c10164042403464120394031014032030103000e0360a00c140c04404030304800f403030000c0c540360020441007210070000120341c0003c4a821481c07507901c1d0301c0c5041c1d22085842d007800b40d1000c000701c1e4541c00c03d161241c0c00c918441e14814044a0ba86000404031f91281d4400306c0041d40720700c01403142040d0766000c0341c01000300701c2d104010f0304450ba0001c0c122464512035a43c9191101d00010303e5240190112105c00c6101c5404540da03180c90303130110905030021 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 626738705 1250 626737455 626737459
    0x240d06080c030a030f080a09080a0e090a151e0b0a021e03160201120b03120c100e0a080f040b04030f06180b0613020d09030c1b05060714010216060605 66
    0x700e074480301181030104059100982680c0c0b55400324081c001d05031074a5001038860086241e40d941c815010a023080060042a85aa5111600c0b100000100600c00001030306238104a0303c0c0c40050b5115103000d0b00918122000000d107001001034010312011410010740c00340388a458005800008958086030218880c400c00c2050115659401540d942da80508071005628211580f80da801541c010702d0182c4114402c3c100105d03000c00c01c400401d00b010341e0f69250b415075000114940080000c01e21603120050741080701044252a410840c0740c0d07440050b18098807140000410311414000702040b140580b005040301c507036490760f0307240c07400040001d04820345415292100c0700e0b00c01c500550040c3e40003500b00c8205103a6898200130825210a403152480030a03908101a01d0407010502a030000c4500980310352200801c54100410800c4203508804064408501e082c00030307545440554140c00d401c2541d600c004000c4202d031b1070092082c2e0300340c0e14940009804c4042044100d400c22001c4d2841 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 626739955 1250 626738705 626738713
    0xd0902090109050702030a030e030c160512190b07110a03021509010513030e030a0c090506030d090602030d022a1b03010603110d110d050102030402010e011d240d0608 73
    0x40d841810003164001d80f2060010780081007c0042c1601c690001c0300c1510340f03002640d02d80702c04411000c0c54045004a14038120040d40402c208525160300c003004503a050b0b030060006201c003114500040008100000e05440406010031660380c0f152002d44900a0300508545a201442c01d01961f912050f4114440c030340c4c01a00040d0001e40c0c10301946003d40d14150b400c000344200b5a505440c940c8142807802d4061044080c0c480c0031404401c603040060018a000042d60b0038540305044c1017000b0a040b880600036401400c100c815030000498408401c08040180c48080754402001300c2100d0500d07410010883e201504034400c4007003a02803030b00501030302d68165020f404040c14203860013484090716100c0740da80c008855080223102c0750140f81c40341d10080c40e12080000043c44800c02e80409980b1690301004101c03c55801c68000c034480f14003400d00034585401c621501055041c0120268000c071001d00c09000f482c03841c620305900300890700e68070301e0326204070b0742e108402000184035822075441 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 626741205 1250 626739955 626739959
    0x30a0506060a022e021204020a05030102040803030103060902030c090a15050109080309151209150705040b031305010603120e1512010312020f1b01030515060a03110c01020d09020901 80
    0x1a0503801c440b80900a50041c061603078104a200c04913110380280c0c901c0310a080480080100941d1004000d4010151610341c164145801405030741c03041e54029030b000740e05c104020300a01c600042681d044170b51007040410102d002c0c0c408079080c2403007154032580100d01078041c030180403c190404210450907000b0f071000f0a0382c400c0111500e90291040e213403550001c0004040c5414442070103000401d89048070762920782c4107200c0e02500603003203480c0103041d00710300381c0000c2c240329102103290083c5007440c00c941071a00b00900c800b11840b000d0080041502c6400065007008400c0d00250003d507008207180522050001002e4a80d45960450912401041100d48403820302d2900f41c036200d000c4040c04455603030031035882d0f0750354a111b031102d94107510401c14101500401081400c0c400c110300e94560156000480c0090155070029102c000c42d00080142070400307480d0131042e00c1a81641d8500401c3c1d0540035004500f0504c070341c661011280d400000c00d50382d20491504420030b107503c01c0d0341c0c40d20306030303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 626742455 1250 626741205 626741209
    0x2030c090405130b01091d0a0804051305010f05010f02010915051911070228030623160e040f050c1e07050304090c0905030f100b0a03150903030b0d08030a0506 70
    0x2043c040107160502490042c08140c1d0254401281c9203c1801800f24804440410501d02900d044048849450009060090303080907041d05a0511241d0f4083c8101d504110782424516045e00465041080a04542040754401d4200441c0c5503000031003000c0f070220b415482006030208440f1000b40c0c51400709460501501c81c0318240d046010144075031300b041140c1d408c0141c0c1c01c00c24041c54405600484032400324640802d10100214400d0f00005030f911030207110003082c0c040706541e00540410380020020125103002e51028402c4507464009480b07045800080c00a250406c0c43d07a041510300010868400081001007034003040107064078600d040c2072030030700010303101d4080000c000d41c00510080001c18880d40250040450b5828040009602c41d40800d140860050902c6101d621013200d0501c1d0b11840d1044a0601e04180d80b49160207055443d46079483c1c905080c58400c160b81c40b0294024980310703921000042d42c00038030002d02e2a840f402e20010580003074a918002c0ca1801020422034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 626743705 1250 626742455 626742481
    0x6060e01170424050f0a11120408040f260307170304060906112127030d060f061205040f02042a0f020c040614130f02030c090405 57
    0x544416501d0440e41c1d624006074440004015108031180300360080e1001d942202c01a1142440b07800c900001010301e0000c800742085680901044e074900d2400d040000e030300183d07400320f540110000070403a400e600c1e1441c0a54440c412a800413607140c0c00440046429041f81103c140c510104400d000624050b002100352684039064004040482d1400002c1c0310484042c0556445800740c4e0700060300c1045611440b05446000c0c0031107010101c001220062604aa843d5a4201100103c020314074503000a8405158040807900711242c000f030b4000f03103400e040801c1150002c102200e01400010340e00c02c0004030611142c0140408071f181145442c61003074691055601c1542c01800100d0100805c0d003d000050080c0b40007100d011000f0b10014000c01244104030000c0c0d111540d9600c055407015200a0425584452a500c507508003034081040240c0c5014080e202a02150300d031400041c10441003000300f100c24034890809001000b005400e0392650b000e001001029a020700165450000c00640 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 626744955 1250 626743705 626743727
    0x31b1d01050603190609020307170703090201080604021b0a0516080a1112160803030702010f1406120a200a050d0c030803060f0301020705030723060c1e0c0106090606 73
    0x404801d00001303518480700041800c10307a41d010000180d55417120f00007816680b00301d4211000ca160b072034488071a0b82030035850681c0080c1601d420810b80c240c5a0008095605c06849284a56000706454007018071219000c3d80c5607203003070103d40c44503000b4a080b64944607200144d10031406c1d0745500103950040410340000070341c0e00000c1040d16800c89410880054207622174502984903400407214003c0446807800c0c0a000b8000040d81c5030319000030000d00351296a4012034880c3d090103584500d03890001d4855030411022105a0362810640c8229450400125000740000070000c883c00040f2a070000c2c41000440c01342c40c161001c68554040c05141d4034180c0b40140102c0b4041408c0011401030303006190031010041c05030042c0240180000d0a9820600e001d6440d0340001900604106d00400c0100d030030007407090500154203102c5002070b210700005204030145034001444003d0340180301e180741e1000d40e85901441d1642815030b0402d000709030358000c040300140b5101e004641d0500070b6101d051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 626746205 1250 626744955 626744959
    0x90b0c06011e051305090f19150f1a12070302010e04050c0f030703020c070e09030726040618050901120b060d0b07030b10050408071415070803040b1005090103020415031b1d0105 78
    0x480c3c1230180c3c1d00d48415401c4521845200380d0358030141000b10a00c2d000341d0311072900c10032402001074901c0c0c007040a1001c043c104400303180c1c400241040181d0300071030301c11046001220005a07994a4084003c960700c14800013102400e4000700b013010181d050f43c050621080359004460f0243c0d22070b01d0540071940d050783c4c4076800d907206011107400900030141c44074030f080c0503c1104000d040650813001e4145c0050b0098404120800710410040c10a91b462000403c011501141d903540740100203a21410000b0b40682165465000140703640c80755040450401e80c007103048215885c24400007001828003aa0351446103000c100820901882035003650140d0741800090400c0d07610b001c3d001c1507903001c9043e105400020341e0070812100c03400a00900f040900402415550707141901d800089044024a4261a000f84071410b00c0140c0703480701d00c00c0c10359606890004021524580d203030a141d49a03170000b02090b035031460070300030407500112503011244041007030044030310080614030b040102400703041e0f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 626747455 1250 626746205 626746243
    0x7170708030f070b070c0819080901020910080a0902090c0d0b04151202010908010c09080f0a0b0c0904090b0703020c10180b13170307090b0c06011e051305090f 70
    0x20042035841310b215400c54050f0408160700310295450f1030880d0421010303c08041003142d5890202608080b00a9110350690700851034104a0307000540403104020004041000d59000031740901000d600c46260180c0007005642a40b50001007111564802c540d24040c0600341248117165050500481d0008140d08840a40c4503080168001d246840d50f08140c1c10401032030303c00500d201d0280310740b44840e111036407604581828031100b286040c4840242c000307a64011504680030684014086802100c4800b906541d40300f0344002a014044022028080c480c030b4005010015030143c1c010050702d030881041d01d1006410318080c0b004c40d056a045e100c40040c070400c04000081c004012160310140100c081c1c0800429a1210812a004e0b0303030303195152440010600c052070303400208180042c041c400b002464401d0101c2850340b01e00044c807078480824107080a49159466400e81d5001600300980901c0124400606a00190805958404a60042d03122501c804400070034201c103034480b8510b9070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 626748705 1250 626747455 626747467
    0xd1e0b090a0b011b0506010f0b040602030f0307350a180b060105300f071b050c130609060b0403031d01090509040b0a050106110d030b0d020307170708030f 68
    0x4406048024400741c108584442c1500480132900b10714421107029070020003e940c10084040307203194035034104800400d81480300308030203030340002114050b840041c24140c581e102c407441035505140c107400d0410f004c441c490300440d8071205000f00115070710440421004c1a15110020b0b03040f1888400e0300c4070080e906150310008a080e081c80b039a0800c2061500501e0700700c07040301c24030b404003841d48046c0c0d8007100c0c003e02c000d89003a5211020b81140f506003041c0d1035070511120260040b40354502040381e44c44c0541d07082d41403101c00e01036804801c10203480c0b0395031041d106220b000204524051045200d25003000818400f1441c01a2410341e6030544400200c51151200311f801000400c41c0b05042105806000c030f0b550700c48141c0140540c0c4191581c100508180300d0403025100141c0012040004d03142c907030003168130005668102603019003000141c211940000c501d40c4100164040e4051044010000385880100c0d0140c50315840d41080d40c03482903ca2140d503440e481395144601180d0030078424 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 626749955 1250 626748705 626748721
    0x507120c0c060209030307061d0c031b0108100b0318060a020702031510120c2102011d010507050312090d09060503010303050309010212012c0f28020d1e0b09 69
    0x2e05002e61300800700d84c1040c1d850340d290410380303041190314040300e80b424044040c00300040185c840218003c9028094401c0c10b0410710000c202183d00c407504014040011800c1d404c41814080c01409801007516580d00c0e24081c02040f0b51540d185581039442401c0004401d02800d00c01e562100303030b008010700980d8207011001707090903401802c0c1605400500b03400003480c901d03144000544922030351030000c5042c03804a0851201c1145e400090703100e007882c0d54120050b0303031110308200042009001441c031a810030004031158014910f0090491100140c1000040d182c80c0135103104607410000c941030700e001e4010480e006445803180d00c01050f010300050000a018101031580003001f50001030a00c01e0880000311044002e030b00020154404908015814860007103a80090388050b00c140b00c1828045a10303c0348003c002c000c1c50a09a801049615084190003c0b526800e0241010b42d210414010000000e040245010350b40c40707228101c0d100c00c0d07000350240c000d81c3e080040c5402010755611032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 626751205 1250 626749955 626749957
    0x90302030319020718090b06091b030c0c060a0501050a0515121806131e0302031c1401080303100e01050904060c0212130e0609060d03030207110a0602010507120c0c0602 74
    0x400ca030540c01409130200b48450382044954400c4d07241000461017030514144550384004c007500e5140160052410001403520b0b144103407542c403c0c1850419a41d60711480c4410160150080501060044200b4002c0702c0c8180c0c0c2000c2d050b02c404031000d200140d50780041100e4442d4802000f214880140040101110343e001d40c2a80201e40c02d403c061111511130405d070a0440484200c10040809843d841c20b100207208000001101c0c0e220002940c600380c0c80113940c2c1c0c05981800038840076584003403082a8440e0704440164101c84000c0082544c40d03051040d140e80040f14503800d0315100030380020708030f8094400103040710000350009d0419200e40d101d84010700100c000840075441202c00b041650706242c8000c05100020000c9000359a0a00540c45681e80001d0a118130816484043c4822603403100c0b11148034035498140142d030f640e000d10301004d00720b8801c903c40da07228070540300c001202501034000724840c200036521402c0c4074650341040c0c001c48108480c0f50b40020a0310400800049050b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 626752455 1250 626751205 626751247
    0x150203090a0e040507030c03030f0f02010b0d02091e07050a021b10050703141c0605040605010203161506032907050306040f060e01170d030b0616020d05060f070f0903020303 76
    0x40c05c1e40c018079240d40b69075080311502d600441c000380e501440c200d9203c4d4043d41c801407001c82d900c020f0010009900005d076000b0400030000c1c0c0f14951060200344030b00d0042c4441031000790b800e80011140c0c0317400540a040c54000200d443c4c054050101d102c043c0c0703920740c9080240203a004010030280c10b03035440d040380d0301d4120141c00c40a20520611504c07420006102030171001c110151504208040d15a2031800d58100d544103d0081d42484c00a00c901d80c0c000c4161440c03911035030400c6d41080035608200030100c02d05026414030518180008c41800b2001c145c603002020030340b1a100c41d01c4505064681441000c40c7e101c40025014000701e48186080e41000030380c10400c0340c010030b4181d102c429860b2201c42c281c3c080c00f0507490b40c20302c8010607403043c00a240c005041e81800c220400004020a0140c4a40803106213503000d411901300442d55501079407035440da00f210032985149403009507813900000c2641c01d44003050a110012429510400b00581a2030b03000e000b8508000700c2002e03140d420495a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 626753705 1250 626752455 626752463
    0x804031808011505120706050c03190f1e09062f06040311030f090103150909061d1902131b0206010905060d08070f0302120c030301150203090a0e04 65
    0x6142031191454100a0100151064a00016548140d079801c145407003d81e510060050184401001c000d120100b02c1c202114a903081283d9144c50610b09642513101e0740070300e0b81c2d541c2c810301000900254400c2c0c001030901d86079180d241c0100c9816a22012302070100c4020400141850412b0002520811041845e103d808802071081501d0860030924001c0e0b80138280002c0c0e0040c0d08000515601800105207601040d000d9403604180c07102174070700c9205256500b414152610310801c08811060003c40007440010300030010305a5501e0508080e0800d0b6038520040802a59880035008001c21040c1c0105241c04280c062078076107500307210300040140421130149940d038103a08030b903032a03500f00c074002041c01d40c0c041d01310b1350704110700c0004a81c00035120318003401070318a801c800203554038110380c1c3d107070b8100e03c1d81605480d85107000ca1508a00800704d10900e040401c0020800302d0000156045c5e4803603030200c00c000940440126640c1c080e804440d07a12031120701c010843c0d5068000032642150103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 626754955 1250 626753705 626753717
    0x4020409081605010203061005250510050108101407210b0607050a0606091802040e12130807050301022b2d0528240905040c09050f07080403 62
    0x11412a03030050303080c0302e80036140b0303135000401c20109107801b1440205071640c9003005820300c1001c0307102d140303441049001403403022044200310381488800c0141c024038004a00081c000356841d101241d03201c0c00800c001c119610b08014600810080f40c2400500c200c0241c2d44549041440800d14118440741090420409a82e02080c5010380c036800001c00b1803034010402081407915500c1c03c1c104940056010900003458000101118608030141c00040ba40465001c1041700c4404003450600010b013164000046c800200122007950101c011420ac0c0c803260107803450703140e880c0c0030b25090b4444c6102880001c198a00c00406140c0960301800c121240510000341c0c840582c4e0400d01035500342034045240251202507040c41165600585078010100e00711070b0620091141004024070902c05840441a240d45401e81551b5021049820400340218400061a690141040105401e0304e090790003401a600200b0141300f10301400d4041d007825400d900441d52202c4003242d6908c00640200c0030800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 626756205 1250 626754955 626754967
    0x90806010b03010e01120305040608150d1103010e12300c03011410080a1a180103050712030509060706090b0412030f0b0f0d05070e1807060c0b0402040908 68
    0x802020340603215510101d680ca50500714403194541050740b20300165103903500003400190b841000d85049031400d04150a03c1d40712401003a1542400003400317500800202002024000d0700c4950100c0104245d000b0001100d15040c15a00d520f001c081903c80301004000500c100405001024101800d0800c050304c048044040b8000c1c0d09415501c1d901e9262000c00107106001c240108000c0c01e03001241c001d00307007200304000540126030091207030400365603d5005100c48c0000c040054004c0c1d00c010141b541920055900001c1e014080c002510b00b403294082c0400c0c0001155401c04100ba01034464504002d0420100300312540003000884d007040e25541c030140003601881c2c1c0d40d401588586c01a081d44240070800800710750380e0fa40f01ca6940c5040c201948119110440100355201090340c05040c00f0190381031a80c035220307140d4001188034541408008181580042c280c030110000d43c01d60342495038480080f504010203035405814001c9d04030206006107040c0d800705e035010b445814060b04042c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 626757455 1250 626756205 626756219
    0x70c0b1e120601021c3603060504060b09091504150c020c120304050a0e060f060a020a0512070b0a020a140a0f0206011205060c0c0f0703030e0f0a08190309 68
    0x90000003505103541c01c5441070044942c3c05203e00403415070400c088901502100c40e005003102201c0c042c1c0c10b0107030b10b240b2110410304030000c00c56443c5440031400008003540c80ca820b100130502158140c54003803400c001407100c2e26140450314081e0055070018018054454483d800e406400f81c41121007417081245007000a09a0159483d900d0341ca40144c422010000b044c40301c914000804074138141c004200501455a50310308000c00d80d03c2030719200d80300b6034891010400da1501800c456500010208400801d950700180e05000d07644540e00b1741c1c280d48014000000c143c040c5e00c3c001000d44050000240f070500c50f035405000c0c6030b0010b20381712300300c0e811040d400310781640281107400004101c00810324081b034041000700d00400101070380c424902e4094817150340310b031030203020715400e41000140781d410410108030540300d401c0b0800940704001d50f245000b4084058407100c0d140100840c00b20b856092901c034000741c00301c443c224003510005041050458008503441000c40c103109102c00d001c1242 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 626758705 1250 626757455 626757457
    0x51303051912020c031f020708030c2d07020409050114090f0f070506040b1e040f180c0804060b0a0b03010f2d0b0702010e03010c08060f06070c0b1e 65
    0x81280715640441c5081c15041c000c480c65404510b032001d56003e0045403a55440004030104c0c3c200e0030180c0400c00040c1c1c031002c1c0e0044c0c4541c05018004500200c00c0c00740f121181001800304607030304910a01d1a00301c40da00f2000c040700b03800c1c0045005800307000110150910b600b1610b03c80e07109030000198003001d02d41c0c0400d00703c0159080e5031140d1140d808210510020400e00d070343c4601f0b0307800134480310b450080056500c3c4114007481c121170002080d60582841000c0180c6500c0400d1007070603490740d4898010305000022071049802412070f03000102001c4a5511503100c10854980e503c0311595141c1d110314002d0804c00c044244c0203000ca44000412100d114080d60207040c080c000c6091083c904007808403654016a10b02d8074031509424020b0403502d003000300c1801c69a04d0f1100f80d4890009000594a0380245040d00d6055404c0405080700d07507501800507881000d04030350740e1698204140038804079004482004210310840d40c001e0222a00c0072002d84000300d604040b40d04e4000e290000d60070780d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 626759955 1250 626758705 626758723
    0x9022d030105150a05191208090a090b010c0b0403120e03120c0f032a160c0902191d04060e09070e040b060906010e041a0108012405130305 61
    0x451010001149503140078000c0701c2d041207200b0503500b5202d001c0000524050443e10a143c440c50b0400303d10000c8015031002c04e4010002140003044442c04c034208a07031158400c1903a2480740b10101004291040c2c6885048403901069448a2000860356a07205500344041c0003581801000095100d040242d40110760a017580440590385402c1c910a6051300d40c0806040000940030501c81381521803034030811389512507036036100c08440c401c0e00c60180e0b5802078542110000c4040000d400d031104050180c2e00400b40d0300c101c0b0150480ca555940c0c8804030b00900c02109503900000301580c070203510501720423030046520043d0740200300380e40300003404503003c0b5404100b04003030a6040103c030f10010322214005043c1103e903011079180c60b9550a8a030600104050700c900c3d0b80c0c002240190744620040c140c00300004e0000c0100d10801507040c4080a042c00c0224005542500085a5850391100d0580241d000314444a141490741006036800d80044c3c850351684550320a002010072002c00200b64 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 626761205 1250 626759955 626760019
    0x1090e0703020c0c0d030824030a06020a171b09010323040b160801170307050607020606040b010c050c1c06020d0b0906100206010e070201150f081e100902 68
    0x1a540401800190420313034100d601c51311840a140d02c520201e0f402601c2c2c0f640c040c2c1da0701110b0300c2e0200d510442c030001c070141c01036042d0140305220003541086080d40c0241103c038203d03129a0758403000a08032000202080705c2d050071022005500c1103014822901810244905040106110012605c0624507e240c001c03000c4940c48000c0c10300083c80800700c1810f4118020306418080c02c008014050302105040c49200d0010422440f03502403100d09109490b8042d60110694102d81410080295618802e8900d50301c21440e000700e4901e25801009001041396101010740501381b900343c1040602010100c904030342da0400d00401c000a65180b00a01e4450944100000e03c1720a030340610240d0917008040a01529014030f07140720994002400380c0c1160040c0c003220320240d0b0348035822800350030030b6050526000751145d004a00740c0810f502c0c150544000b28222004003440504058000c0720b0b0010803160b540001c00c20711703070300a0560080740d05039001805481d4161090b44850010000d130012501c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 626762455 1250 626761205 626761207
    0x3010203040c0905070c08090d030c152c060a0e0c061c061403100b0f0a06030605130213060f030b0a080606180613051801092103020307050f0901090e070302 69
    0x2000f502501c2c868103800400ba80360800340e0000f55a01c001c058456031409500c40c60441d0b591408040c0300f84104040341c4c1d8008114a0032460b00c600c8032001e00f130b098840030313601641d0400040d8280c8442d1261034901074146e00412040c2c60b0050614010511103c2440044c040c6c8940e50140c0c1c1c4800d00107203c071400040000550001132120001142c40da0303007001c000e005c8c00ca1741c3d410160f500003d0621600309041000521813281400062914840071000c42e00907401060019400b42c03d80e0110f01161010b56101160348914010503080344240488500280b400100601c459071151002d104420803604002445050700350000320f02030103076032018403654421400c004c03840c00d1041c0e00e401e928190b20b130580c2c0c507800d260340001e10181c60341e40306a13401c664a5002403884104520341e000ca000009008104490190034062455124075001c06070204c0d5a4a000e02c0f41c503c244210f030303c0740c0c9455585a0804401d000006040ea111841e29030404c0360260020602000390600f45001d68aa62001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 626763705 1250 626762455 626762459
    0xe06070903031218030e040b150706050f04020a121a04121209020328020909030c1b0f060f070c090e070501020c03121b070312030e01091104051503010203040c 70
    0x281290500c1d595050050f0424103444004451348108008a66050600c85280f00c5c003030000c50018582003a045500c40188a04040044100300041501c28050340080c0000d9840c0a5201443c12050b07e00940040f03030810700b00410700700301c0c0140751910b1142003a5103041070174070740814104009507015185405514005926207401031400d040c40d04126100340080e03c410b0f0000b903100d40d44240031180ca400c9845545e2100707001c001c40c10030384660003081702c61a4140100d0707190b0382c3c0d00084000c00c041d00c40ca006020b2080040c0350351440003500200721241d405d90070f00a0206903080800b20900380b031004d105003000100107044240280c8031004000600e4003844004070300d0002c403075004d0381c151b4104440c40744803130314003241e100c00000d0104002541d581550070078000d40c9849a203030318090301032140c020082000c1c00301494140b0400341d0b424480480b011004508892081c84000c21519200c0085405400e042d007000d40e0001e04c540c14240200280404242a80d100721422900081700c5082 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 626764955 1250 626763705 626763707
    0x1e070510020304152d0e0c150703031401120f020120210a1d010903080a030b0f0406060f0f02100c080414010c080c070804120305090306160f030f0e0607090303 70
    0x90703400d00d51161411590580e13610a4010303a00e0b071070b41c058107602600c400c1e5180c0031b1710007080030542c01c00c1d014007802d1070516103041c01466a00300001c1140002c0c1070403c0d09a541c1240b4000307d0682c0c80070310307101e040c0c54000d0352103040d400200c0c9030407814801d90784040b540c42c2c55515030b04459080c00b00080c00121520f079604400e0151250500c100038036050007800c0743d5660080d88845290121328002001451074130060700c03280450740c4001c18403140050f16202455040d004039032010803c1c0c03140c40f01d8010032001c0105841060041a0000f2880d00301004140d11480802c461503032680140e03801c81d18804000c0041d40d002c0004100403038105018001040107075400382d10b00e0b030b003404001c02c002801480004d240c2070001d800c47c0748004d03010424400303012803502143d00514810844111000303040c9000b81076a013000f0302040c40390150000041702e030f41c100036280c01d011006036500c070810100383e4000e07002007442008405040e503a80e07500c02580c010402c4170700c2c010300b05612100380c1d107480c51034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 626766205 1250 626764955 626764961
    0x90a20030609010e03070605040212070b0d0507021209060901030f05090109300c05030c060a05060f030604080a11030d0c2706090e15190807050102031e07051002030415 74
    0xe04109030716044000243d13030004000d40303c0d410351281d80440d19886d580000f4601c1c569440c441001c40c002c2940004211000c1c200600002900b104140001e6a422000ba030b224403110440c08009401004401c100f0300d00b0000815020300141400030714001c444c0c0c1400100c5000b1150305549039941e00da08410b1107840705d0b5400305030913088510031211705002c240082000d1604081c8c824886010941c2040000600c1a1022203011100f2110a442c00c840803502500c016924140910250205e4100c60304000c03441d01d1065401210b403d01d0105c0b105021265030081681c0c070b401a010034458010118800e00504110310f903035a0f20528443c00103214885916640440140100510041048110340016110f0304440000d14901807623031742c140c00000f4140207030004951003400c410740c0c0403800612961100a5540070b10846800a4954005a135688601c1040300d1070700340c405080041c0c10300301b00010460148514169014030501c25003030001d0380c00c1500c040f9250480485005118030b80e0f84 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 626767455 1250 626766205 626766211
    0x130306020c0714030d03020c150a140603150c0a020102040f18111204020d0606170d1107060905060702120a0f1505010b09090403230706060803070812090a200306 71
    0x1840444480e00f04000103681c0d0b213402881c10040c55008151170055000c1404580c11000f0004485419071400983c0d4500408800021403001079040012034214100020a01211506129509249e03296a01c0d28101e50f0880107450003103640802000c59011507452104000b080408040b100459480490304141c40140d0b1a28003043c0050081c100600b00804c081e64001d0340541d8400c0c20b249042c200740010349895044489090a241e142c2c10111000103140300d505200d0395145942003400d201e840c0c0e02c60303046105000005003a00014401450103c000344030b41840100590305424508a03480c0c00c05070030800c01d683c1d02170344d04c40c040b092050f125003000807602505820020341d03062200340c03511400307407425040c06445080c0026041601038204280b50110b01d403070012590725284065620340d400208110b40203410300d00c00280c150400026922030790b511165003410310070040c503900368401c0010005d0601c0d200c0c4020120204000341c5001d02c401042d0200b49002e010b40d40c09041c5000c07405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 626768705 1250 626767455 626767469
    0xf0d08091002120109020918010308030604050a0204050f2e0504150206130822090e0708060103080a081009060f14191203200303160c0213020d02130306020c07 70
    0x10080000c000243c070501d203064030441c8000686507182d03400400c0700055000141225079002d1000402070289401c055403040004035014049580d0b6020400164001c5109040c0c00505040c2c8002c00b030b140c0310100074054860304840c1d40d140500480984030045c81100c4a00119400007424820400f20030640350310041180010049030521048252000211010207030164502007000341545188030211040d4040c82380c103041c2c5680d20744480500030403414a210b500e0344a8040001402e00e40400c559040301d412040841c00d10003100c10a4403032060092a1508607840076402041c035892030f1255401030000c044284034030b2030400c1e840040c0021550009442140d01040e207040c004c01036140b690544a10019602150b802d6250a4850410034804008040a0500003088003440040a58412000d43c102090494088601a140d42404c54806034000744d8005001498441580090045001100700103117031000102d0240301024841c0c00c100d5802e500080c07802901441081031038098000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 626769955 1250 626768705 626768707
    0x19091e0501140603070e040c09062a030c0c032a09051005040f02120f15010903110f150a1106070203180f0a03150f110c030a0309050f0d08091002 64
    0x10005000c1142d4030b04150303107104400020008500354403500380070b41c0240001d071090090202c60000078129015902076840000d6410812941e06000c00c910781100c1912290350703000055075614126489a0201d4040c0c030f611040103c0000080d4041441c1e0990400301c0307900c61010f034950750640c00ca5940c183d11030030500707003800207011b01440180c5060003198011100080e9508050112401a0054005648070240e0110070044141c41010910344200c0100030301c80b00c5104500c00648003e00d4600000e40814103182e110031850900380c0c82d80610290080103070800d02001d004803a03883d840740c070700e1400060202000d05015030042000b29045030303a0380003031800e0015440300c4120500e0b11103c6c0500c01c00d02a0500076080c1c032091000c0000e550801c046000540d0914001c601501c2038221043c002c82c035010400c8580a55031058500f00e0230784001840c0340c90210f40f422805880301250690725406420303c0000d16180404c5494601c0025450341034032494018601c600380001803121404c9280 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 626771205 1250 626769955 626769959
    0xa030b0703051509130c1a03100b0f0301030623130203060a2f0c34061d010e0306072703030504062706030207061503051b19091e0501 59
    0x24941c2c403000d034403860110310b90116105c0350509641800059203d03400504008142280100011004601c07514800c41004400da80d182643c141c18490300180340c10000090005100160207a0841100d81c4504095482103003d4040300c1d0443c0d120a540d03c04020480980740001c504007400000c0d40f10b054542c04220600c1201c0040011802a01e508840d04a005c0b2110a121050b1380542c3c00700c2050800311030001e5082d2440850301c01d5008108412640c1c0282081000d0307501c420302105131080d5684403200d44008100704030545907102d800d07074140040415020143d442c108000b900c10480c5603140c030400a2044001440c05009440c40002c810744845d0500200790004120780031a4421b207010410180c681035a061960b01c841040800c040201000103200d55042e006001068021602003050003200c03044001807030300364032004240d60440902440002201d03220040087c001418400301c0356030030086400c1ca03082d143c000000b8251f98070040b9001c550760300c402501b5400700e0310301004954 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 626772455 1250 626771205 626771209
    0x50a030e0c130207210e0a0821090d0204050403031b0203031308070c0b0706020d051302100e0103110f0408120a17070504091b030c1407020913020a030b07030515 71
    0x41c0c0c0c0e00242071205600011400c0070081440e00300403203500e030303001c11054617100c951000f0b015038a04007115110b00c01c44100070450150208000001d50b141f455207644a480c40c6a45007841c1c0c000718a001d0740002c00d00c0c00c00000d0f8840d40035162240303200340e500007161600e01c1c501807140b00315081614115401841040900d9101b110045032681d088039140340c5075105071070a4581103940e90880d003009000480d180003040311a4000d410204da65050030301c46982d074040001c50105c16020080e501401c50140c0e120f0b02d41c002e541503800e820040c034000c281400b030f28100e0942d90f800b45404045000000070100704d005e0f428058501544039089105280c0940440018003080041d103c0e868040e131040c0224400b036000e04229002406049802d11140700c007008440c1032a09909943c401282c01d10141d248420300c5503800c4000321a034914030701c0c01e1018031f409002e213a000041401d900d102101725218056038803840140000d51248486c40064602608c3c010301361440a010842c24014a582c1002c840d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 626773705 1250 626772455 626772469
    0x160c081206100c1a1f03141903050901030c020c0d030c05100903050f090402070f05010510140303040b090f2214160806220e070b03010b040e0406110307050a030e0c 72
    0x151040c034207132415211a80c2a0400d407000300d254822504091000008216600620111a504031429100350b8841403e00404031001940001c2c0014010090000c142d800f99010340d6109080d441110300508428010900c50441c902e401d50100d00044004800c019080046852000c000b0070f043c00b0910840d50081d02a01860104413200340f00890b525a40e900d0720307415a500280c1042d40020003201c40e0412134002c0c801501c55071107003218400c011030350500c0790f083c651103a24041e0096180501c8e04241c900340f1740000c040c0651045c012200c2558135a40e01420000041d0b2412007078842c400c808200b981100c10318458070745402ea00504020580100da507800ca0215902c1c1800d81041e81c070700d40051100501d0070f400a99400c1900907480344800f551b8000b0300f214403400116200c203a25581140c07214042440769501011b4100014003240d0028444550841d103d0306022880180c2078803d42d000e07400440d00840000c0c0c0c0401c071041100e0b814000e4045030040a00078001440140007c5008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 626774955 1250 626773705 626773733
    0x150806060a05071e0b0601030605030d05130e16020d14040603180c03050102180301090b0423101b030e0c060a050408070b0406080f0708160c081206100c 67
    0x108940204000c1420390140b400c80e589168041c0e5104a080d140e00c00c40760690140c03030340680340d101e0b06800203442c0d54004c0c03048405940c001401450801210082100c49500840c0751090500324240c0025030190300110b481c0c042c1203c11905c0020400c10750000345003111880742d5404000802c105402144862012501520810702e070119084250010000b075581c220000207100d440744650002c18040c06602800000d22101a10106051035008043c241c500392035010301b6590002000c100040d2003d031a000000791003000d80281c1900d061703102130030100411100042c694032002c0000040000548513039215046050800c0340301801c0213203a035030703059000740b10340181c0780010400440e80c003540590b0300030082d65044850305902c900041459030010700c2040c001c902000c01255505007941300941c41841266501400d13a0b489500100d40302003000f41550034050481c80b030001041081c0010204e642e42100104000c0c144031003408641c0200440d10401c101000c0c0251002461000c0008a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 626776205 1250 626774955 626774959
    0x10b012a0c0e130309050315010e13080a0806182401030623090109090f0f111c1a280b030f060106030e0309010e0127080c0406150806 59
    0x1015901450500c511090303640081c041450741c2c10401109001009201c4180382c82a82c440d25026628424036a58980c2c00005131701e0b040742d0300014404d43c0b49004659a00c2420240b0850f1503c9007915582c2007a480309110400040700d030420040ca0f810700400c40082010a580c0c0300a45180841c0803081013003041541c40e04a90341081080e54913882a0491400380c9a030305400c0703400300101c504072030195100c06000c6002c0c034031203400010015403500c6400c0b00c190704000c14080d4488507a68200d000d00c1c4007242200c42402469a82040792100f55507140c040c07900d440381e03640b00020f50034140446101c9070395a60f66903140d00100b02030790410102c0306075103e050003083c0103c82c007809e0705c200c007030811421280d802d03204140400c1d03052031000a02c141212220348003000005034880b202901e0348583c100745030100c2c40c5d4282c850460352203003408040022814807400062203c0c46000700f02c84900354840112903001403284440c0346080d1262a0081103134a11200251022450107040e111004180318 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 626777455 1250 626776205 626776277
    0x1a011707120b13051c02060903040b16240207050f0c10261611030408030a0503130b04080a120e06160c05031611060a09091503050a080c010b01 63
    0x1c011114190f80044040e50000581d41c0c000b0b8107400081c4403164420790b0000621075100420f205c8000071007298103441c441d0200d186072144644102e060000c5401c800c0318030051104100d070091a807510350340118540004050307514000c0341825864101c1d210102110303500410092004d5540ea00d4428041c941c960425a03004640080901c1361311440752880351121040800700410700c0e40c02401c15600b20503540302c0038240d41c01e04100c103640740100d00450344150320411a9201283c001c0c0007840c1d108954018140b5410040d540d20b41c025501520103c078034440100d40c00209075040b003280c0e0a0b07440d07400c00c2004028a9440040d03a1517002800101403a5020006a9442d9102d290243c100c3d507005422240d60721203140541e1072541e000c98050b1f81010b0307603000001c0146048805c8541c0b901196130b40782409400c10a40d03030300800282d03071040c0c01108020b00020001e44d0512481d480f85000b48441c9469004031202142540d603c240d800e0b040024032129011040c449034a090224010903c1d11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 626778705 1250 626777455 626777461
    0xf05131401090b040b1201020706180b1506070609210c170304050c0901060207060e06070b150604080d05030f090609061902090d0b0a1d031602030a1a011707120b 71
    0x4a002805800200382e01b09901c0410038201180540003048030a106070741c10001d0304003990300301c01e440d040038900034030000d4110301040d04c4d21500c814140039030300d004050038a000c0c81d070707074480d02103600c49034003150b40d01c14004014101c180b501c4040d80005185082c081c006820380e80c4c48444c02d81c044030383c40c00c044e00080045020303c801000f105070300c1100508212110f50319207401941c2d0b0f0419200e0140000c10b6a980c0b154641014400d903622241c1c444804a42900c0715440100a21804101e00303030490400c1c0400941c102041100c829408150741f5070799a2030030a4036041d9403110303001300b02c4030f40d95000300280402403e0006101707500c0a046994000c0072150300603001c003e40704a0940361341c091520481306081c001c080343c40c0c90003110018810420318198800c50700c0c00d20b00014118501e900184411101517075040c8d02d2207a41807009081e950207080650320384414005c501100f0010301407034401803002440003500c1145021001006002c05445c200303d4017000640300f030700188070230403403004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 626779955 1250 626778705 626778709
    0x3040f030618020607050f070b0f04090915021b0106090b0904030f031b0905011d031e0f1009021207051507050c0301240509010f0b1b01060f05131401090b 68
    0x14a198540c002c0040717607034808a00340144d54140c1c04134015094042c420002400100101c102e40300c03c52410040c6040c603282840c0c2c500106076101c019160400000b98031000c078050b5200625000741c2009003a0540d0310f900fa5000e00b1a501034100302c11051808125049541c0c0703041055500c0f03030f411f145c00c10403d8500745048001c3c0000303e1454003ca42103080241090790082070711410380d202a81c40407003000b1001c0f03400710903104454060f90150040c44a03540c51030a8075416201d035841c45422980c01c03415a050085c42d00c2c200322008100b44e45d07681142c8007146002107005502c1c050712001000c07100d0410000900f00e11061402002201d4000f41110406c4014084004942c2004008110b00d1107a4003c085401440000c1d00310350b460a4100810366207004015603040e03c41e040b5034002e00f2800c010311419a948040c00e0224100e600d025440041442409000050702008070b00010103480e1000b03002c0049a00c00c28107200070305240c800c80340100b00015090458031020404120070b149000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 626781205 1250 626779955 626779991
    0x5090a050c0c0109030f0f0804020915010e03030c0c01140309070b07060612030806040f020726070f150f0203061e0114210606040510050a030605061207080903040f0306 74
    0x80420b05942418440810305401c400300045508594550114003c00760204484185040701d001f5880707135034000840d80a15481c0f0380d4080065060400800c03504012f000645907400c011070700c2005502c0301803040c00700d582c82011140e40000040c3c4180c10350038010b03441501d80c01e4034010940700340320200c0e9010030f001c45030b00030400501d40014420301c090482d040040c038154044641314022800c012903200114414800c440d0810f80122040710354a414061910005c01c800003d402612400e0107402b020a0100300d0700c0e0080b61044940348540031070b00c40d80e14144c3d800f45681010852044c410402e0315242d09070040031001c840450305d451445d100300103031190301900039900c0d070804022030288a611006001c2407d0850701c03026905041e0346100800032144581c0c0a8190000b026001401ca080d01034000313821900000e003008281c082d00c1e0340108080d900a028aa64298500000c5c00501608a5511500310410101552401341400c20f5610400190310000302626584d003880382c004c1c81941 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 626782455 1250 626781205 626781217
    0x60908120109021305030c01050d0203180d09140319020d02010c0c151808032b020a0c02010f170129030109140f01030218090309040903080a1505090a050c 68
    0x40314080095840e4140b850080d0030401030560f4142d40340d400804c8a140c00258020709440c141d4a00b494012880aa140070b174002411035840110100c8142d0061102480f814410380815503400c01010710302044041544031b0340034003e003e41c0000d520f4031115507002c0d004115840d01030302d01d0904040c5501c012074448034041030142145400c41000304912031942201d000c445042d0340e07a1140c015010042024140c4107200e4901a50b20402c40400d8031b500f11018030018211b0b90303144e40c40400d001209102681e1058888000007071210741d82c2402c643c1c01801181d1690761911b41036a06030a0100581200304c010300480035500500100b04c10340d580c1c0c0b032a41022410480c03000396140d580d60100000640000382e004039420b001030002402d110034100340306040300d800622400400c2e8036120204100c0e0005040d40c546400104105401034441d401440b10300c2c1c0c480c0da01e8405034a06403040e072089030f81018000010802c0740001b00b00c0d50361050341c820b80000801000058a46444080d402c0d288515 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 626783705 1250 626782455 626782477
    0x231141305091b090f0105040b120312060a170601031407030c0311101403010614161104050c0901080a020a09050d1a01060519031e021305041a03060103060908 70
    0x8041044580b803008141d01041e0a841603906000680300002c2103050a011a03458090580441c010049450683c000400c1003a0141c0b800c2c1c00006000e14980c00c550000e006060810800814803d031414020385031001020300301100078030006040b8072036450b03d0042c0f0010b0101d001030035900040c401c0500252004582c02142000e540e541c1f4500049141c00b0040340c41e01c0740d180034640a0f032040c0151035111410076070140240c82c6a09044003a10000f1503a00c2003c258070342440580d00c01c2c207100e07101980032809400e00c03203541c4400c4000c20090720802030980c1c8411000348140c0d100b51b40c0100d60a50040782c40b1101580701c1038005011103001e0981d0b841550700c0721010403c1d80900c4506004075040d82c0d8030484903403c0340e80b13803042039415106a070101c0022511014111504a20a60142000341c886682d440c24803114645298107a0308903030750b8500615030703015040089152601c60040d0444041c038290030110071560000341c43d240c0522015110f0350321010801c0800c4408402ca41b01c0400d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 626784955 1250 626783705 626783711
    0x8100315091106041205010c0305010608010314100c121505010c0308040501090f0f0b09070501170a1e060602010b040507090b0d020702090f06010e03060105130c090503010603050102311413 83
    0xc1d030742c04440b9840c848174080d11994a004c1c0d003250b016110b4041ca23816036505403500c4295074a5950340714001101064048505d010351652800001464010406695100d9a4030880d1599200e441002c44444441d0740ca00911448400c004c241d0f00442c601510b00d80500b0601b5556843d408d040d805000b503070900510182c01d0007c0b400401c05c0c2000c400d0b440c180501158245580c800101c00c0c0d851203940111b50200f05a9410b41d24406182d4402650010003070a020550041c60408141450740d0f0b1820b42c0c03940303502c0701001e00605509100789188401e04450901841c10311050141034a03207203024203001070a00003070040a110b1b25804943ea440c1d0701401071001072034490480825480161a4540007410110103040a0b144c00503242cce06030f5900419082e00c0001c0c07243c1031002403e40c88204024003218900000386070307800f03100b614001c501503000503940b58444c028510b80c1040000d1038102c0c0181002d1000c406c0307402c10f2020703020340b007080452528400c40c0c040000c007048084c0d4190280141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 626786205 1250 626784955 626784959
    0x10020c0d030804142a0d05070e24150a05210a06060804030e09070207050a0b0c0105070903030203070b06040b1c0209090a08180a030507080106060810031509110604 72
    0x540058074510681c007580c201c41c0208102400e09850300b9840150000140440f22801da00e4000032170310301c0ea2800003c08001d03030b422284d80c0c0e84e4205101e59000d4101c0103880e004011202c440d00c800340440000100c400301d00c4101500000d640003011140300c1414000104400d83c1e140e02400c102c0d4500c0c06c070340074241c003000c58019500d9014203048480010107420404005940d5008001d041e0250ba030548030200702c101c940041c4020705000410200451041c1440011103484400c00a005040d1502030117a45441c2d01c1c081c0303801e50388003078224401c00caa0740c0800c0012030b40c080181c940742a4069070b56200c41c0c890400050240041d8110503a001c0c0b000002c0e880d070842203408614206101f030b540301d400e03559034040458507071100e644007030400d03d81000b8980c407410040e51502c010502c000e1041088070b8607529140e1400c1e845410984075070395190002c1c002d043c1c1080081e84e1045140865140c2d1074150354608480060703401a04000c0d9860ba1140002c00c0098180c0641d01c3d01d003d05070315207980d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 626787455 1250 626786205 626786207
    0x2120403171e15041d0606040f02030c091210110310060f085106130302150403050a030914060306010906050d2d1a0603160e060703030c0e041a10020c0d03 68
    0x164080c0c0e000c5100380c0c54040c00c003080c424039002f03803445050030207825406d041c036103000c2c04400414443d150a41340240da05291066209106203a0283d030b0b00000181c40e4600460100c0a0085a0b003003c01848208e0582855640d0b0001505a0045441440209296003071602d241031030032614012100c3e140e088400d4030003c2c803000d000b8071805224114480342da41410188840c2d44904040801042100c031000c1c07025041c10070420340712407200406140740c41c0e56a101c90341027615480d001c80c0000d0030244200082482c07d26038062104013100c03410f00c0c40c144100041c00d21441c4e413080105004000c20031121140040e031005080100c0c0c0f00c004012a6401421405140103017100000d0f6246080f0381d02d0752540802c06102d658180c00307403003c0d01d036482e001090040701030301c0038409003000074001c1911446c2d120340c8042e00c0c00f144240c4000c41d081c045c0d20405841010702100150145d8a4506081286400c0210120705800252a82c0e1080c0d0300c2e00a04a00b040700e1081d00d103810010b4010703920201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 626788705 1250 626787455 626787463
    0x61b0b16120c0e040b0111060403050403050607030c020a0f050f0703080a020d08060f010809160909020108070804020102071a1b1b0a14040f02120403171e15041d 71
    0x681215600c200c00d51aa0901d03890403510710600e180000790321050701d08118100381e4405d082d00e0b0814103200ca160b0075502e1056240c24000c4800700e001030000702e010020003404001083d003085030b500382440b20440940c0001e5491180c11005040b912040c0004c005102082c4001c60100c400c20f015240e00344c9c0c9a04205041b5071000328498014450031458030180e91040790031038001d8900508c100b84429004004445507070014205800b94002c140030052038407040d002c0310700103100a03030b40800e602d0b0b014000500381c0310b0001c1098060081d80c0c020031005070703400724201003900e8180d052220081c448003200c031312a0007180440d04088000c00038245000c0000100701303400e01e14031100511041030a0041c03020b100d600740f050000901c1e604645800c5482c00e5000b120000b4115030005003401c040070141c400307820043c2c074250007103455032414150b905520034117158040710000c0340701c480e104040300c55401c240c001084800343e0427280074170800c00d07501c50b00080200404009106420301302c166000f515 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 626789955 1250 626788705 626788741
    0x9020f0315060f030708100e1c0315050d0f151d01050603060c070807080c010b060706140a1b110f0604050d081608060405040c090c180506090901061b0b 67
    0x1241003901c0c81450300e868002175590a840c0541c0c01751804401065005003d00342201c04444503008503840326424045c10300c90b48440e0110b03568082801040c40e4003034459800b103500564002d00c1600c6a54002c01c01498032040050350000c401d61119031603003a01d60092a40301000114410441440e06000905401c09805203404074103503a5252164502d4040d103202d440c0c0c0c0185034040a1000001003080d4402800582c0400e200101d904800c420000e86190311429084566560311b1099600b411142e84c1101d5120001107410440c0b513580e10300260210200302c1e5014100305d1503002070b2031442400c1c03012150846da90022501c4a040c14a4055181d080310f204034000244644002140c0d01c04014a5a0302440c0c0c0d80ca42c10710b29281c101c00d20015040c000c01c03e80305032680c0b00d07000400248501c14000601441e940d0300540c1c0f80302e80c00040c0003540d11303801a44540d0301403210641c690b8500d00c61504440d210b04041c0042041d0101c00200e4241c0101c010300038014070402c20480070101c0d031450300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 626791205 1250 626789955 626789959
    0xa030609060b091c020906060310030b0109050f0901200904090c080a051014010e06031c0e01090501020109120c0f06061401120509070b0d0e0f07030203010e0312070309020f031506 79
    0x41088002ca003c0c441c1c4032044c070070180d0700c1500c050103d40c1c1811301100950700304d01e440c003000c4141902c0742c0b2409400c840a0b8400d01c41c10340d48004001c6201c00340408281c1140100d0000d12414050004d50f2424a4035807429100d0110005540070040d50b450740102ca9407a408504c01012690325641035450300c40094003a00c4a0141065a040c6115540714102d440da11ba0105c007500b60742081d9030303d02d840384000e003800d801d8464081044203c042803c000140030005589240090100c54001070060310341e03920840c1968104158440000c0303240309182000206032401e890f0201540c00d000c00203108a03136000c0e000c40e1400310041148000340c103c82020081c01e0300e604252182006010045a0b021100e0b04d0150f000790409200c3c0ca0340344001441d03400d602c1500031862880248040b818900c46440c01802c0d60b106640800442c1803e024081c41d51601c40081c1d03080002c021040d10100707000401200405980d5400801103650702d40200c0c4e41c4d4030014003100c880d00742c002c0080b40e03280000e4400d0b038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 626792455 1250 626791205 626791219
    0xf0b090111072301031d060114010207061d0114070b040203070f12140c1201140903030108030a1211040312110c150715110318011406060a030609060b09 67
    0x180018600088aa0448800302d840e0642d036074000034800d1043c50080c558504050711407a1815040604401e0f0001000030000a04000d514284000a00421506080d41950803011040260030b402c20a034214041030203010149030303001800101c4d841015484401940b00001c1410400d0001c104e04480c41248203400f101c80d5543c84d000c01c0b4007085075520460800c4481c00107203c000400d10104421481710800860303109440c402c0000d4501c1921002240c0e545c0c2d5109020207400b43c4540750b8503080f03481d030b402a601d0b55041880c4d41d0f48910541e41c000e014000c84119105c040209580480502902034400030b45a5859203014480703600d031910200c00248100845900030f480100300c95203080e5004000784007031800f84007414440e0300580c07026540d64080c644124000340f01402020442d07503082c0c1205584e4a80b6800100c41c9180c0c1d9021031301d0302da00d4110807079090304c0e02c284000e4001c4c00803940d4a440340d4960b54114007509403508590802c40c00c110b0005040c2c03046801130866044111042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 626793705 1250 626792455 626792477
    0x6150506030702070f091505010c150501290903071a04050d0b06030607110c010f050c0d030518070f060c1b0e0a0b120c0609030f0d02150a050907030206130f0b0901 72
    0x4299208400f40c407103900d44260382048550b02a5400b12100c0b031051120a1080c039220b40c444bc110344099000d012042403820452580050711103103160b00712100107046040044101c040b0b65075220a000e1842152260080410101e41140a42e0300403c00106020401902c03482c0100c09200144c4142e0300030b100303100114841da400799640721411001c980c01406012080e40044070b48945440a95080c00320800005402003403e0241040d1100c440c0c402083c141000c41d40c01d40d00090448445100303410425003840a40c44070704103901103905030700e004165076071355060041001c0b00c1949001f0454098000004420320708044051140c28030403020403009412038288404403040b8400002260852249841140760942c054010702d0b80c007a040b14420300c0c10009951401000c0208200580d0003009070100052103900450f90003a1a50740902585c20140c0075190358035858040288141004111000e40303c0100c0d10100042100c419500307140d90b59002e012003c0d50041030902d00280d41d81c010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 626794955 1250 626793705 626793719
    0x11010f0c023007030f1106030103050c0405150301022109030a09050d0f080f0d061d04150b0d1511040b0703031109040c05121501020a06150506030702070f 68
    0x5040a6802921070000d202e03465854034078801101150b00b00c6800c00000c40b41a03044100300020240d8800c5103400c1008680d41001d17a0071111702c1d4a203c0c8906410030041c000100b000c910510141400c0d2008034030781e1245c6040581d10100c40c19801c0c0c066101150100150344040a41550003000403903951490702c860b00c845850344100406400420000c0f5410071213802c0403080c50385030038007884d603285500c01d26503034802c0c0650110b5084045a9408250082e00000074810302c00100807601d007a19024062081c6a0342107400200042e140e00340d160781044613250300340c0144640205c01000c3d44181745c0301303180030490f07611035074903900202d46007400c0c012840c0180801c54042d80d00c1054403600b0450f42b56421400361400231180d0b002038006208000d21a103450040701d60a5145840c0c0715222804103500e401c1d080001000580810600c101c1d955240c0d80114015410a4102001150b01901085e222010511580c46560030081c00803c2000c00d0b640860442c054031010f114000520741d0f5940 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 626796205 1250 626794955 626794967
    0xb15040b0d140a0609030906021b0d0318150504060e0d05070302060f040f06080114090f01120f3002010b062b290109030c1215050411010f 61
    0x500790080c45091161002c1802c5540030002d070308020003107032080c001c0c0380d40b000d05803444160120b0100741034840900c541d1380c050080c20107146205604040d05110203001440c0074150101c05024040d0465105c0c85021400c80382c03401406680300319918041494a0042c4164864418080010b11a2340c2d12091340c034045c100111080e4211008102c0c550640d0200700d03556100d40c0702040d844d1030802000030f85a0210040c2c0700201900d403141e005c258540003420f031040e05204400380c0300d55844000c0201800f01c3c1412075054138400600034003a0700c80340ca40f000b40501d0a60303010b0040486104004c440031091000329951450140d0038800041c0c5074401a0700707032070403130240c0382c0d1121042c0a0001042180d0b804080010302c07020902105407007200c140c0301107402c00707503110524600400741005d8100c040a1026488002032a1510b202440c2da1106040c4100c1402405249a80900e0b80024015445403150b0030b02c3d40c1030700401c402e042c68500720f8003004215240d14086110100140d0480380164 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 626797455 1250 626796205 626796221
    0x1062301050c070308090117010e060108090a050615010210020d150e0112082a0604050111181c0206030c091c02090f0403110a0b18030c0a24090b1504 66
    0x24005141c2113086079101520341c0c00c5049090b0410145400144484a42c00801402000481c0884445041c81d1000410070000100580e4090b44404201c400080000802d250f20600342680380c0c0000d840c0e00c0041382407900304140f030503100b40041245943c003039960f48522441c0f4400c6400c0001e05a541c4854100c00310709209400c8c01c1403100c2004800f04007184001d00e50303058607809214880c0c0c444007490000c8030001903117400311340c0400100810001c00348a5200058108100d46007060034a408000c40d0307c40c0c051010b402200e400d441da40c18601c040060900580c1d00030031080e224a451400340650341c2051034a18404d500285402210f000c4c141103031000c0780e40162010101e40d440040d0107141c1d00307000d042101080506014516484000c0c070440190328829401d2130520704000c0c42820420103100061000d0760000c0103d0038540714005007078003a00707520003500c0d0040100740041c8c407507100f070104c2c00310001c0f800d24080030100700408800920520744d84501940c1189944d01780700850b5504 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 626798561 1106 626797455 626797477
    0x60a0c12050a0617010218040b0319210503070f0801030b18070e090d090e0114120705040213030302060912091201020f0f21240d02030106230105 64
    0xc1f008079044030301c0c2280c0c00c1c400e45080354002500d619045201c0c035a2203200181c031408001c0c0992900140c4d5400040300b07051085102800740981e401103645c000080c0180082e00c060311300550030f141c181ca401051005c056a1901c4c4a46a01d0b1640782100d111131140310000251110344414943c451a13040e8050202c540306000f0280100d030444d00030003c0310492a006100c9580100000404a4400c5500550105000001c141001c0c01604000c1d04240000b400c1009500b40b510240112840ac1c2e084030007075a41c107107503503448001454005121400801c03003121a45800c6803000306201c220400145803004540b05000180e000c0c1c07905800e22170000c9410000f07501401a040c6400304039030410b02b583d26000010080100c0c0c0c040460307e00d070002005001154680a2074484201e501500811800d5219089204400e5111001102e009040001c0c61032139449039060750100b03e10 = true := by decide +kernel

theorem cover : BRFrame.Cov 626618705 626798561 := by
  have h0 := BRFrame.cov_init 626618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 626618705 ≤ n) (h2 : n < 626798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
