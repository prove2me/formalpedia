-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4452
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:39:51.263018+00:00
-- url     : https://prove2.me/submissions/a2fd9800-1c30-4f82-8f10-9e01e0a21b21

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 800539568 ≤ n < 800719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 800540818 1250 800539568 800539583
    0x1b0a090f05060a08010b030706030c1b0f05070510050d0504020a05060304141c050703030c0216060306260d1b0b01090e19050705040c0c02150714011b121503 69
    0x81c000d0900d8483c910001a103a881d000708000c441c0800040d1791799045120b81c03024540c0e07400304101d0051013075901d621030802200d501c40210358039240031850102c0c851025202c0d801001c2c0042040d10f402c2021421641c3d00350785060506040d44452401818058012648114807150004654850070043c1d88994000c0e10781e841c4900c032555956090480c1040c08101e05188134540b1031031a034001c016508559014070300040d00c0350002c04141c0c40e00000d00080c4a210f0b050442c002404c5a050f00030b10181c414650740c02c00c1d0b500c41034444500348030040c40708a0058002c6001d00c0c0806200d070195813000c442408060315017031b080e0f0f100c100c1107541c05c0c0c000040d200c1d1a5840c0c508183e104000d002c81c84400e001140d042440c05440b4941c5030249405494441c50320785907803074001380c4a01807440700160000c02105116920414520301c0e80c0c04400d01301d034081e450741058100400113208248000c149041d20020b4101c04000c2101d4204c400c0400b890101c1e40ea200f2920318101000d0740001544c403e628 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 800542068 1250 800540818 800540821
    0x15020105091e071e150e03150603011509061d010f060315090501080a060605010c0209010e0c07020603010e0a1b0e010e0d050109030f270e0709080d050706110307021b0a090f05 77
    0x80c17041c1d101c40a0045909200701030740f84081c5a100025a80041d00c2d40785040c0344240c4801000901604612891130040048410f001c6242d4645a00c140200c0700d24008116101b05000007100400702c1c00d1050441c01c51840e00200212400783d0080540410100c01c00d011941d1100300f0507045400a81100180b0341c80b105240702046181e200ba00040c0c6401d08021000302110790019045442c140030300442d01ba00354020942010044090382c040039401048662650386400b0388040b036400481c0c03440d00c045d040034101001201c5458000c07404050035991142c9940d40e00380151030042da0b1148182e0040d00481c02100800e0003846841c041600ca503440c406500406a0000c0c09402944071070382c40e42c50305403a101e40329088800ca0300d0880c0d003005a2000c981d642e650b8140d4441100350300c84407007801940101c415150703003c0020034480d841004100b010031481183e41c2c1540c001299a00056442811240c180f034403c540d40100d0310070020201c1d68841d8a844000085d00d00d00e091541e1050b0320b610 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 800543318 1250 800542068 800542079
    0x50408040e0a1a15031311040c0c02032803030e03071403070614010b0912012a120908090904020a05040c09060e0d051905070510050415020105091e071e 67
    0x203c0000c420b2800320782450203902c102209000c2d0f407001a0440360901d200300c030113504110302c1040034550008024405c000c00c40c2208405043d1480301d41003240b00703000f0340c0111600031308800c02d2003c0801d4103130100b000d515200e6030b0950080c0703040700140c0c1030703440240a8140000d80c45540c40d01d500c81100065500d860080c03521006a5080c0c00810040000039001400f001941c842a5070ba00e14003103d0344c002000c003417550301c1e004100b550003100c0d100c903a2880300600480b003407230004056003181da51003815102031141c081c00c407203010100800b0701104121440d00b80c0f500001264105000411840341d4650f20700c009800c030380a1040b0b6001060245800b04841c0d03410521800340c420742643c45070a6030ba40c954035180c6039075040d903107901780304007803400030013030200810107600074103000703080d0401d010b90b0714801a1190b00903215110071031960300300c0105030b64418080c0500803100c2400507d00704c054509038407004920070380c42044920441c0c80015803031205240c40301c45003854001440f03078a400c12 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 800544568 1250 800543318 800543351
    0x307120501051003120c0f0602220b0a020303011502150702061005030c060708160605010306290a032603010e09210f0912010c0305180c09010504050408040e0a 70
    0x402c62008440c3c0c014080001c10b030703016108800c40318940390210121460f4a0130300d035285400e40e0064401c0d031000c80c221804020600c040c2d00f80385d070002e8940c070030310b60b4074030340501c0350300c200300c0150016001840100314481c2e0001ca4040301d2600e60050350031001f04240410341c0700307400f240c401c40168030040600c1004465001c4840181802340c000d0180f03c004071011850500c140f550040220800142e240d1003044a850030900050b8048000d001d90f581d2030a15201804e04200080d41f050389da4040c0403148040d00d04500c402d4a40580700c0c6040c245152503529070010740700d410a6071100389103c450400a0801c00950280c020302152030003d04020511526205c401505d0b0009140f82500b55010f05000c101540c910900c0020070590b1402c00d800455514240d14903c03c0c0e2541c2000e10403107030b45400d070b049648240f15140e41070b400107009044241c0c2d1501c4525426410030448001403249040940040354001e000d142e08a1030640c1d0341d008034192507001c98075100d4050360b56500c4801c00164 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 800545818 1250 800544568 800544571
    0xb36060a0f0308030a06030206040e09122115040603210302031009020c1905011a0a0f030f061b020307061a01091e080d03020c070509160f020c030712050105 69
    0x1518503111540c00e104040c244200140070240c903a04021000400d0010300750410809540d020307141c0380e180c0b030b920141420810401d5070300384154003e480f008003084980340195110b980d00c600c00071508411884040704985005403101103801482c04525030700b5260382c007482000351304c03521001d4182d4001000e480c1202000407401402c041c010402c1c0080503919289420989901c440010303a10b07031071410000c0c40d100061110700c02ca04803190309001070020641c0211140340600d005100810002010046162100d004030541041088418000310f8080300054a1041c8a51700010f0380442504a144150740304400c414010b034000070340c61041103400c2c002c1e0308a01807810300540c03441d041100003a040701d515028030b80c8c81d400000c800c42c003a91082c4e0208401403c820060302d90f41c2190000040281d400501d501c54148a0040c000a607400e01384035140c40f0b003041c120390030040c0401a50403180c094119608204601c01c0700d9101c0240e035400e2001c0700040441e80d01c0790522555910300a42503840 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 800547068 1250 800545818 800545831
    0x50108030901020304032d061d07030507060c0305090a0f03120306150e010201140c0a0906080402030c040b1912030f0309031e021515090c18040b36 65
    0x41c419100681d800000b81c500b40c2c0d91041650f00c1d051041203c245281404040c03080055403110740f01c4080c0700c0154441c14048407042c043d0002c200c0c0542d00d80740d0350b40051200034a5980440010440b00b0b10943d69501003500c00c0c1340480c03030084288e00081d4080c88a82040070304075401a0302f0402c22240f01e0f204540700c01c09050038011a0b1801581d0784240c0358091442092040403855080c0b243e00c02c4d44080542c0b41805100c4007a400c0860102015070803130446000801c001c01004075102d40921540d038442ea9004004000381c0042d4003d0002902180f40444c2d045280c11400e6000c0c003070305400300009000380032540380c151720305410000e0404281d129580149494140d4208c0448e901c000500c17030090481c0e4000900300c00350071049290000c40e40c0e282c00d01d4080c2005001c116200f01c542d050301d01d00100e40716a800d0300c480ea2400201e125260101624000340c10301241141060f401ca402024401060b0096201907000700301545506080070289240e202140c400c034965503414825080030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 800548318 1250 800547068 800547073
    0x30528050903040b221a0708090621041223070c030206030c091e060711030f0f0c0a0812180109180b090a020301060e012f0303090609060c090d060603020a120303050108 74
    0x46d14081c0ca4903610a140c0d0117001c8000002d40306c0e026403265011541c1d820400311410880011691096540c0301c000e5a007101c1c03040e074405502c943c007845a825800303440010081a03008020040c1c5c441c01a0f800014100e4a0b24180e039000800b41e501c40c00a144039042541c149036481000104001043e0801580b0301858102e4482410f0306e621a1015940f9580c1e20049510310300c0181400281b501c0c940201102e01d51151131142d210007070000c1007100b03030080142e80c000700058881121584980c0014a240d490030760505c8055940380144601200850040c10042d0880382c951040404c0c540b011008100e070562104c80340b42150070080050b03580305000a40450555040c00d40c01004401c01d0210141081042c2128603501e19244401b1350701d03030300e0041c0700b035266040c02c528041e20384d0002c230b9015096000300c50000780d0801020880c14400c1b240802c01c6032400c060340b410401002c050500584174159a900080700584403d0003e0001c2d1102c2e2000f002c0400852030010103403541600594201d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 800549568 1250 800548318 800548349
    0x20111040b0d05060d0804080d030b06030f040b070c080315182a16210c0309030b04060b0307031103070b2812050a020406030528050903040b22 63
    0xc1007804103403503048409100210745602d4600016400810070000074216000004001075400b41c00101d421101302c89403002d22800c0d032103a04000386400211240440781080070300160028003a001226405043c0c0d040017107240c0d08941725945503070004c5400c0d4400b19071aa00443c0c0310b14104004602d014208144d006107071034040d4840045881800807502d1040c640c04540085444039000e0341d60b84401d40443c09a0110f02e400e101c0c41284c96508900c050a06600c40071086500c10f240e04000f04e601030b00c40c241c0301c61030341e5142009401c0c001c00503950315541381e481c940c0f542d509011040007180588070040341300321124101424082e4030343c000414100204641d04a100c0b42085070300308049036040007004440e8a00c1c0940c2c0340f410150203812101c0c1b07000e00308030301c031140740d4042c105031669039a04025981d81d031001c00100e002c20310490240c0202e401200c0f064a42260003940d800048242902e0625603903219980c001c0e00580300710108801c0b071400040c410071b50400c5483c001c240024941b03401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 800550818 1250 800549568 800549579
    0x1302040906051810051003140f070806031b0f01110d0c030f030608122d0301030c0605070b0f040309050a0315200f0c0c090a0509010506031204090e0a0f0305040602011104 75
    0x1451390b540b181c1409100525a040203650081e8480c03610b144856100180500d001264008036180c1101d107003020840318800b00e0a1400c002071801301800080c2c00f1b04600310b11510030004000805001c5504204116010103034051042c0310490090340943c076054001141890701501081004171450109881c06908018050000600480c3d00410f0401203955490b20901d14081e07203000610003898000c1259200655502d03640118100c030f0045c650304580c02e8480320304407814400d01e0f0019100c201c901002c511016541c294068029100e41403207004181d850000c103401d00042d610503a50a05c1c0c40c8124020091540281c0f242c031818081000304980524840c8496406a4940400c00403070214070b840f00540108240309142800800c030721010719040804901600049445021399400e2002160140c1000920480e0507544030b40d0060801c4e0400048200038003180c2a0161781c6c0c400c0c40440004502e000d4002c0a1950090382c7d46070344c036414002c0207401c0d100a0b000064461108000401c030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 800552068 1250 800550818 800550841
    0x3050f0c09010f1206260706030203010b0a05181203071b0503120c10061410090302060910050f0706022101060504090e0a060c091d010b0d090213020409060518 70
    0x84180c25803d24490701324031507030b2000c0100a41e4011440707a440c05025820f02107101c20341354042c480200220754000e521010110140e02081c410700044c1c0e0310a00080050f0f50003034003c1c01c00690070614000b554004d5000240b00900044901c800503040081c6600138020101c02c0340820202d902d00952006290134082583d54000e00401d0111000218101001300d00a022a60745a00a468207002d070644800d40300401e45103031f00905200304c0080f1010349595000c2c0014004a0346c0081c8042d041c624240c05026031800940759600400404112110b5035203400005420001c0c0914801a1200c034665060034a03403120070700500500039100300401080340d02800301c406450659134082070803085c031074a00303140050318500141024101411075400a41c05413500040b16804401007080420f510404191404280a191035241e070406c83d41c6103100b007941040c1030061000d000390880c0c0c28202c8400c01241c00c650009400b0940b91502000355240042904006100700904000c41d810603400084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 800553318 1250 800552068 800552087
    0x1401090b1516021212030712140105040f0e071206140906191803021b010c02010e060304030203071505010303030605060309031b0f01060b1e040503060c0d0b06040603050f0c0901 78
    0x100388010442c20b0320841d02c0724602e00345504104001c440f1800c58811940311143c00844d501000158042003074000c58186000d00300701020400444007071a402e10040c00040e02d0300710b082140407611880e001b11003080c204949002800c240a000b8004995403824105941381d1030a01d21020f4108801d10802e10004900c4a40207820700c00b42191a188640e042c4001e00225880f0304408000c0c50358100900d034010405184030030010301e41c514000c50942c01900c043c100c0380000f03030014050303005c000ca450070140021350f0007030300a004403814801560384511201500643d40040c06449000400030580c060003408090181291424110314050201c580d4a02a1350f41c4401030f0b981c107105004c0700302000d11900940341207420083c01901e8031985071009950000140418141101d00b100c1c941c00503040035102036410040107040545c4800c01103000a030052940c0c1c2405654946085482c2d6403502c00510090450741c8001c101468042101800070034000e0203d01d004171304002c4c1e0300c69680d000d078603403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 800554568 1250 800553318 800553337
    0x1204080709020f18130c030203100e09120309070b0c0a03140a08060f010903140f0c030a17030a021318230613180c0f150912050c03011401090b15 64
    0x282c25100b0000010500040d0f11481e1085d646040305a41580381d05400862180b80c08031410444181c0d98900b00004004c02c5500041607003088071405451030041009603001106002110350154503494196255840488071140035808001c45030700301500305840000c8054048400f0f800c140c0c145130086d02010700180701500ca584044890490b581c0204106406035400c0484035441c5002a9005a985c04202060140520650356103040c24500010120700050b07010302800120301c0c0321450103880342c0000d042140c0750741e028829000e00000f003000410040102085444000c02034840d92022201e80194405c904080c00078482d14282e80761240766000302095a606e001c15200742c4520303008180c0c0b44050a2940082c1c00010240f01e409903a180035100d104002e0300d8196a1149d207500305400500f40741002c00c41c41311080000c1c43c484489000c0c0c003400381041d580d0680a80c40081d003181c4002c02c04030041851000140918204e505c03400030700ca242603610714040d56206002e29034074043c11820 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 800555818 1250 800554568 800554597
    0x3150601020a020d030c050a080d110403110607020d120f0f0305070c022209051e0f060a180204020c0715050a02100507030212010605070b1e13141204080709020f 71
    0x219410180b0503524071b00555003000607902d54000c0c82c03826412607841a500750002a04210510b65a10145001c031811254020400e500f40300003001402203540200100780d81c002100c40012000c10070407460311114110303641c1c0c1d40300d900782c1030300c0050b00504000c0701c114101484c000803c103030f0680007000c030012680c046034401608103c1811240740740d580300c458000b1540c103008034442088000224802c03521450707100c42500140e003555541c1d81c0d042020300302000f54042c5011418036a51075014001c45551a41042d580c0f003a1600401c090343e0120940c07022541c0b0582c0e00f00420030811a0900d8a55a00d18029190841c40b0900a42d10400c0c0c10650300802e07074540c08548154000c2d8121111b040c01c481e8003206d55a0344004c0680360b6007146c08142d6030515000300050078100c00c2c080d007200e00d011118144080c0c0e102e0001030007845159080454210707401c121264011030381000226900d23604418041d6407242059611814412107a010501d82e50060003140640d4140c40190f4200b0541e2801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 800557068 1250 800555818 800555839
    0xf0509061315120c05010c0f1707060e030901031a031b28030c0603021213050c031009030905030d080610031107030e010e0306070f0c030314090c03150601020a02 71
    0x401c400410294460401d024002480000c44051a441c3c0c400380740d00613a208050141d0f1440199942c41c1035400040120f07800b20300ca040018000504054140c5c01d01c0601810548541c0d41c040c116141030030740e900d607584045500b10440d030f418022651584201a885102c41850790082603071099121414540003c0c66880b4050b039440314030b00201884050340d02c0706400003218445094201c900e00040d00d002c4036103003005ca0024000c1c001c544120004001400185d9a401c2301c1006001c10414200c1e102e00400c0040072003580c040106174602c0d01600000940d07002c0d030345009030041794564001ca00030f400c1140f401cac50b40398100603850ba10507004d0b034403680c0401021008400800c00303a0343d1b8041d503c5010610606040e030100d04034050800070b0300c401143e0550b81040640d0780b4000c031500f200156021384403d000c40e1150255101a610904010030104142d00c15440100741c00c0302d00103050703846540d440400349020452036001c00007500112400b41003600000307483d982c078008060301a214451 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 800558318 1250 800557068 800557099
    0x60109030302030a03180b01030f12090303170a02070b0114102d0c0b190c05071113020d02030f1e0103050d080709030615050a0503030a080a051008060901150f050906 73
    0x12a10302119074008121103c7e50703140d140c10707203c12120f1107081e244418008100c11885000f07003030110641e501504d072a80a0884030210f00303812078001340350f003a0031502440110000b84080d000e003400383c9000c0018083c20f040f0a81030242c40d18107480e060040150290703244800550600d124801103480c02c4100034043d85160051310030007a0081e000f040080c5800412020800180141c1014601d0a2060115000641c01114a80103141c0c01611400c0c001d901d041442c9444801c0081c46c50007143c015040107184449413049800495100800b110300d5000c02c00d0340800f2540454140c070703c4500200080d410341d100c00b80c1d00c2c0303041450308003480740c1000810101ca00071000800190340c00103040c000f0802021502c00ca034070242c86020301441e25046c0204030340ca40401130310b0099140e5a2210344655501c4200e00213440c0140c0b08800110401c900414a40400d01c8214803400c00000040381800c030b102c4003449284400c1d07101d17050710350403450300303000c0c075076030305411a80040c0c044503200083d00c50301 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 800559568 1250 800558318 800558351
    0x7050a05060d2003060312030103032001180b2d07051612020d1101290f0301060b03010311040605060a030213051f02070b04050f1909051806060109030302030a03 71
    0xfa80301258041504242d03010028440000394402c80b825010b0f10201020f22240f8580d03030000303020017404252032114110140280c000d800d00300c6030208002080128192060004401d441101580d8500c4004200424848100104422202c021254141c0000c4141540180c07440242c051020007100094440444922a2040c05020707000321418100d0321020030042e40e1000b03c0d919000108958640c0709450318010b100360f40300400151000d205065081030220740302d05180b00051b0b88280c000d100d00d5142c0d1000d00c1200c1c046c00624202c20b6995041d42080c0c03071007000b9070701e003d407040d03041803010f00c030310713103031035084c1d13004501c060801517110814008501c075441070940150750010070342202a10040405803030745210301c03c96000c0d10702240d111009021548201c0c0107042e00324940d48070000241c14609020f11400580103406a4682e0f212000039090b41c50658116042c1c19940e42070418448091012030b4002900742010901186107641c0030303450307009070341c4800d0a040c0c0d194140e81d81040d07003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 800560818 1250 800559568 800559581
    0x30e1302091906030c02010c020705041d030f030916030201050d11160602040914130206370e01050901020703060f0b0a0915120309030b18240907050a05060d 69
    0x6005545412004600b4a501003081c07044200084c103000c010b03a1580d0041c414201c15201950140849504100c00d100c094144111407000080d0388140510803040103002070010310080c01c0d809917580c1004c518151920182d43d81001c070400791a40c003000144e070440100d9040c907510102c0030a1107606550000d00764002e2100c01443c00c00e0b4541038000b00b00c0c4c5036008105440410070200042c940303400c07209041c200101c40b000710304988618000c01515081c4003030071032001c5220b101e000d00c04581205100041c103540e222104408011031303002540c1e803c45241c40c1d08400a1070400e040000d03090000b903984e0321234030014000a950394202d0f0300d084405d411001072000040c00c110795030740c0e540c0c4441d40100580e09425240007101300000c944400f96504018103d9095542c0145c01400c5031a20b40078240e0150400c074540110440c004418141409145401d0009944800e0080c001c0400070618400040ca000d080750000b03041030100741d403110f0251381943c0043c1c40c0c8070b4a801c01c4224260080c040d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 800562068 1250 800560818 800560837
    0x6032e090f03021612050c120c030d0c050c18131707290103050a0318150509190b042303010213081903050906030406091707030801080a030e1302 64
    0x102410901c00e164002444113013001c4086a1030240d103a41d54220301810040001c000c045400000404415181c11100d41d50f80248040c15607001c15030040000e40b41103840300030384020403000c0210405000341440083c1e60348105880c1035440d0000200e0004400c00014801241004641c030b000f41800320041028244189461503d50b507040f660034031800302e4103005540c088540694140c281d9040650001d02d040f00c1c2c0c0030000388521103041d60140c413a02e944180ca001180b9801130f00052551840c0042030b03440d40c540d2107140c1d40705814414030118030201c0d480b4006039090240c0400c061200c500c1160304481c00c0384001c0d00009403101d2042c10a08403010200d50641c0040351001d4001442074040c0100c03002c00d011521041c29000030b003484449010009000f04805002808607418840001d41c0d019204000006010f0300a42d14005103075100c292440148002040320020180c0101b20103000d8400352000b482c00b5901c030b80d40106007580c1448480c3c00356044803951408808580c0666002d5107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 800563318 1250 800562068 800562083
    0x20703060c050c1b1507060209030601090f050915070f050c010e010b01090806040c0303080a09170a0e0102010e061305150106020a1505150f0d0803090f0606032e09 72
    0x1001c1c00401499904401d890040c280504c3c4400c2000d19502040c100c1d42c0c11000d040500c2040c1c0100001103140c102c250b0a0741c10726000c200c10f0705c0340d59040c0310960281c200140001503001680b90030004941d0001d111055136400520071000f80c0303038210042903014101d840c0452401c42d103903000300c0300b50082c02c440c0c42040d03003083e1000e030b04881d06420000c9903010030707130320340d408039503501713070095070340c601945c0c05866001242c4061000c603100c0d40c0b519910503a040c0b4003040c0711100e5900c01907201020705404403110303c04035501d84459449140910007020910080c4039a81c81c140307203540c0710340001e0305080c01c000c2035041a80420609004012070106080000d50903980d603103801940703039512200115402201c100040c12038060131301c101c5001d440c00304202803181c480036003849015004108000da0024100d44a007002441c20b2000b50304c50100d032405011010101c0d00b840d0310b0075001400c400e200b0741201403d64030800f03202805001c0c000c84095002026100603d1403401003170445805043d01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 800564568 1250 800563318 800563331
    0x309020603040b04050607230304020d02091005011101141f050909030304121b020114090303070804030507060e1c02010e0d12020c150f0d180b041205130302090702070306 75
    0x320198250f6841180594161141a81c40321000c82c0c0440403d0415640400840c0816046126147c040e551203440036081e00504619500003603810300c400c55013032540c01d805050a02803560302c001c10528500910f8003d04c41441c1502141450a40080c070710802d0f0200080f10180c945520f039244002004060032101441c200560b0040e20781c3d00440703050728284039200c55158442d2242d0450151000a00054107400701940e00444030600380008510201100380f2282025a50500041c4091446000620f50b40d5240d441e0182c203100d411b80c410000e001104101d1482d907290400d84540180c14141d5400c0d03040814401642c101c00d00307886003504040d0100c0d0000400070f0454520035180d6441d000c03224400311940c10854003044c100844111003c05014511203202e01d080a40030940b491000810f0b00d03400481c0305d144504641809030380044001041c04144030f0071181c540381c82c10300d52074014035104004105007031a44082c44000d00a001c5400041d100c10310a120440123541d22a8084c401e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 800565818 1250 800564568 800564573
    0xd09020a030506010317090a17070810060609080a0c05060c03040b040603020c0c09063a030201022502090103080a20060a0b0901240c120206071428030902060304 71
    0x320f000900044130301445a151545910fa00e80d0700380c88698100030a01100300d8103209603040c0609000c440c2002a03c24154080749402062003890403054a0080019806160a43c010f1042c440c940c8001c6242e000201048e01060b01c1d00780c03d1060310015030300141d0701c0a10851240c610311031030340b2000b006100402c0114683e60b25400070300e8480c82060480d40f484030356008001d0b442900b80c0d03d207580241c2c0f110050b80d00001c4940c030440341c07500c14004030a540380000d148028040a50340c007240180d43c000b40410b010083c1690800f04004095048a0b882039507902280501006000180030510f0100710340d58410311494144280000b002d0001c9084607120190700d13581e241c01d90b04c0c5084c550a10041040c80d003040071301d4034101e54001c0414103003044411101500f0040c406000d00401aa80c0e6010001c2041414448415411a4010308082c6086000140820022512200c416108000e62034100440c103210395060351501040c010080f20381e440940c000c21300a00000d4003c44080100400d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 800567068 1250 800565818 800565823
    0x303190c0204051501080402210106032a06270b130f05030307020f040c0c1a0702060f0c0715150e0a0513030207061b020409081b0f0a02060d09020a0305 67
    0x4500c02e840c00e00036601c40a9100000805400350140020080c1d0005000352a00070f0211001c020192050304203001e024140c41e094544903081a00c2c50a00300d190080b0100701d081d26003030f01c2040d03c8000300b102424000001c0202641c8680c401a500194012000d022594980103000b46544412259565403c071104188603160f846001c450300b42c9050300180e00c6c140071040304d0750940e004120034441b8074032a0401006200d503100100c10040841b00c2100010f02a0402d006042c0045144046903c0c140400a00c1d0090042034055004002418420100c01d040c09840c09240d2020b40107c201ca80b0342010401845101e80418100d000c0040000c6c1c0c4030b00701c00d200c0c0c1c051051400144000d5850a43d00e00c0c58035801440103005034842e040c01c000c014403030100801c4444441c1d94002c0c08603181c1e00010180c03484440c080e920070f0303000180d085855458815650f103c900c00d00103440b4030961800341c151140c0700040040e01507480080d11400c180e006074400c95105500501916081e5180c1c2440b95 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 800568318 1250 800567068 800567087
    0xa0e01090e01060509061507060f1d0d0212030c1b030f09011806051c06030203061008160501050322020d050123060a03060c030b03010e010b010f030e1b030319 70
    0x24415481c20f4404103c60804110941c40780c00c000e08205490303109010118041d0f070045070300740c0e07203103903201844042d414040c01580307460358600c51044180d80b5000c00c01070404d2280d2908100b9580b084869241102650098a0381301a001003100e1f20340030950714100803174159402c10091800000781241130380301d444014150000083e603078010612100606e51541954038007a00c00403c4090002d01481e0340101e100001d05920920003162440c0e0f41d40c0840c0c50100155001908500044401d0081010401c00c81a040e00301051844030180750100182c03540c4005850300300745060a00360b038070010352941e4184d14440e03405480145001080e08002d40280b401501c010302d401807a120601d50002c041e642c4e103024040041484880914640e0350300003c181e501c0300c150525072602c1c1c0344119070f60300f8459550004840c9001003442411000018400781c1481c5140b0145031a08040c0410424005000d555450401e800311201d6005280000c1c41c60040e002c0b00c034000317001010b014021541c000d4884 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 800569568 1250 800568318 800568341
    0x10905250801060f05040f17070b04060837150b0720100e010c06090b1f05101e020a050307060605010201050a06030f030c0c0f03030e0f010c031d0a0e0109 68
    0x741224604c8000300c4c1d40d0302c60791040ca045540072200922078940e500d1084a03905928800702c1e00030641c2d9411055007500a503000070085540b04040201c0d41d03141c22807103e8241903006281c1007010803804000000640c1440d600403440da91020345041c04e29a42a07400540300e1510142d403200021301d0010303c81051001005019102c030380315961542051140d5503c4010030f9254140610ba0303a0004450080c03d058081d507d10784c55401c0b500105040c0503215000c0c41518085032a02506110040010089580240d00640c0d4001048007070941c003c03404d501003105441002844866508102e1801e016428040c04500000070319100304190350303000d0703001c440302a00280601d684964105040b224140310283c21003140403a0380c00028410501d51100d02c1c03040c08a807803000d0711081c0c0b030311480c80503400440115900340421045031410620361071654409280459a1440755500288140095100d00e560701e401c90040c0841907654021950180110b5511086250394030029103000d0030450405 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 800570818 1250 800569568 800569577
    0x420070c050301150e0a020412030f0305150625050303270a030c060b0118140906060712140d090614100f05060a02010605100906140406020601090525080106 69
    0x9000c0c2410f0003030741e00c12010003c03802541850030b07170f208542c880001c0603003504a900300000b00352a80840110f2032607501964803401d020000d444050112003010306a131481641070480e001e5160303180821105003012039a0340d074a0024015030442c09035070000d5070040c5140000f000f0414207076004005101b40742550409440c0304100c4048451301c0700003040002e000100500d440e04046101604034a0344907806140c840050404d400000102e00059040020704141c40301c3d0710300c210b151561555401147c112052468124075581c1d0741210040040e41c041449501d418008054000d41c00707954039807021103000e20110055160901c010125034100c0181196450b0200e401640d0b80300ca40c009582c0000e03c3d10442e05c1c20b01c430410021717030490800d0381c003190340f00d11020416494400501d058180680c641309011424103c000d402002c1b0004240311110040c001000750941c0020f8440c1102c180707400000c0c20b9110098049500300180325100305402801265401c1694000f0307181d41216a290b44 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 800572068 1250 800570818 800570843
    0xc03020c1008160804030c062a0504060f0201050c04060c0503070c08030d06120506060103050c0d0e010b0405091203040206070c030b1e13030c0b06030114090a02130e030a030902042007 81
    0x20f05031030385581904c018000942040c0c0d500002402540300e000c3c3e000095000020540d1821060031916480c040701d20700084010808022190308400c8080e02044680000e00c003507c0c103c0c41e035050a0055201e40420801d80000a82c24008207004072207645402000740386600d611034203810b959178061000d500701c4d2464546c1c00140d0b0fa45071400e504080da44680648200d4a03034000440150402404c000d0021030100140c81038603040c0e102d051810b003403a600100b140700020303081004691000302071031483d803c40e203294900040808122540694104d411545842c004e0820021032081a0402030444a1003410321a851628407480c0c07002078000030301180642c1e104601d0009c4404880801030105c0c0794068002c0014524015856100201600008003010b000ac1a100c0310b80b802e49251049402c000c0103400de60601e480e050700020151102404800307020710340b007a5030b40304241d40b9508241da1040384008640e030b2074001900074154104000c0e00c151411825148030741c030a085c1299109262032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 800573318 1250 800572068 800572111
    0x130b071a010b0723010c020f0c0a06051b100612020906040b0307030209091015060906020619051f090212100605041a0403170d0f060f060c03020c1008 66
    0x31a8035058403102c14520742400f40964480a0049900ca84001d000210b4a030b03408409030240f08400312000c0c154010720b849611101000c0c1041e10680300c6500910340a8000c1c080d05400108031a9069601c1d80d031310410f22089058141003035a400398800d0600e0078281e00103501c07c1e4405495064600844100e20580c40e4001008200c0360f491100c1034258004500c208090b282113140242d01142060960704174040403619001262803030ac1c0c042c100c801c00c2250a000f199031291410003e84014002894203003040c0d0301b85a031862914025041d080d480750005109a440c00c00900b00c0c034550f13580e41c2040144c45d0b0750400c01035001180282d83c00b21018000903002e900026404c401c80d003050b15998030306410038000c1010b04400c11100c041e15a41000000000f4440c1241d130000742c41114082604d074042c00c92951b00341c92082002c0324800d0b04044091124058078009034040766210305050800081ea40b0b410303410300b00c01c0110242d21003620079940304690f80041e14682320f016400500e10680c0d0044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 800574568 1250 800573318 800573363
    0x3110f0a12030c090e0c0a0908062a130303030506040f0218061e16110402070c0b0a02071e15020a1a0604020d0e010e01150b030604020a05130b07 64
    0x110009800d4098001c038581c6514040da001d800303400858940001a25200e41110303c00b107400b40d40c0f002425600090410314150302842d00c1d0040d025480290200c2c0c14503022180b000c046500903045100d880c0d40300341c142c841c10901282c00861450220400130381e0760b420302400420f03003154464011800e0407580e01040919108807400c00c654155001020820602400b40e40d4100c241056036072a44445c410640031000c00150101603221004140340034150302d0551180ca2000d814140554014030500300001c58001c028403d44000d0764000e0340707800c0d030741310220301d8084aa408041403004c68500c10700c40e441c090b21101d00355044400040028070701071000b00c0e503840c6908000b41480c12241501345c48902d0f060300f4071b074003c10300602c00b5041801c01c0c1100001c6609640186585a543e04010561102d01780590f40409008220110582d803800c05550313568440200030a114590000b41484294052415595415924842000b4841d2074881901513540b00c1d0200751040c200c20103d1950882c0300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 800575818 1250 800574568 800574583
    0xf0b09010f0e0c0d06050a0305010203040203120403020f130b28080303010609120f0812150402041505070c0f0f170610051e220b0d0f02010c1e03110f 66
    0xd1a00311003a540b44140b04030f00d608244601024161119000281d03a42ca440405025601400005079a42440c2c41014a40041120710600210050000b000540d5031042c0c0c01c01000c80566003010032000d4112540c0041036541001540700c450041540c5440200b40200d400e001000c980741034900b929480c400d540c0f800b0910070040080c0c0c021000307001400c80c0030100304000d8401c10200d05e44882d1170381d603180c01d40c025684c0003401a000310200300702505440344180300d010707003650210300d402d0501e401002c45c075030062054400c2c0040050345804105441c90b4502c024400c0140445c4540d0b152414851802f00903c901c19180e03102d035800303030300c1c0c03020106030035001e4840d07082c0700101640791201f400106d110f060004880b2003030081003490b45880d202d20216140c541854549800740111030740d27804540c2d6200205010312008800600055030740d0980781034081d02400c280c11040d07818903013000c030100b41c0352a84a554910288006c00c2680101d24042000c9910b420f8500800040c03100340d544000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 800577068 1250 800575818 800575829
    0x2160b0c070b18070902120901150f052116060f02010513020904240209010216030b041112030d050609160807030e0f031810050a09270f0b09010f 64
    0x240890010070158000b402d00f80001000d0381d111958444410049800414003c2d85824250b8100001c280003031081c16210500b60500192050030001e0201009400380a140e002d0114031044080300d40c09160700c000c021001c1c0c030842d0a202c035250b5580003048410f21419010810860091800c1030040c003640e48a0704034504140c08601d801d4080080f10318014000f62190b48120110090301e007440302130290789100c004405030355440c4a5000900e01018800019441203a00e50140300061310580d8445e0481d82200e41c440945001c0e078005038100200140c079100718440062202900e603a01e801540c402d040494150140341c3d02d1030206540d003c1000c40f400000b920401c0022a2180a40d00c075040c00b00d000402c8920224609041034a035501004146441c4d61a014074006a4641151844440980c52138080c0c00d0041180c1d029064007882e0081c11003081c4112503507601408117140b0303020440762100c418012540813016110081100b0400b0500809158001117007105914071408121076 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 800578318 1250 800577068 800577083
    0x3050f010b090d080d0219020d111e16080a06050c0405131a180a0c050924090901030b0a0b010e01021905070e0702060a06052707030f02160b0c07 64
    0xc60400801584403000c03c0110f41034482030298000c03400389031015140d80c250b02d2841c0c48004c110140e01038640540e20080000b007080b0303a1204090081c000c100724807c0d1944180401c80b0380940080b03507050201c0c4560171101000010390005400000148407820703540500f0041103680c4036611426241e1146010341ca421418005122000408581c02200451065580c804030001544d000800109c09010f43e04a070000800074002105041c2c460440102c4c514144185000c4010001c00c100095100140380007010400c0078900840c83e04086030740850b00103021f89120f68403460300f40441c000a6812140191030b025510000d540a031041c0c1281d41016001000d6200224007140141000040704660500441000140c0d00d01000c440030f000355000e8000d841d00d0300c0c06142d000c0403920181d00443c03040c2080012502220088208107044220307940c0c0220060781c40000582c0940042440d0000fa1803001456661901045441c007103086d103c0c00b491a0355856400002103140690b84000e070001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 800579568 1250 800578318 800578327
    0x100b061305010c030306080609030a030510050a0b1b010f05070e0d02130213090203010305011d01050c033108040f090501051305101205010605100215010308090301020c10090303050f010b 82
    0x42d8050081003940034030034a07000c44c6050b10b8030314040c24900195620880d07070740040344555071590140a0240c2c003040050b646e111040c98040090007e1402e0300c5844454040003500300c81a0110440c0a620034281100078000e11264106c09c20040c6022a402000128100c81510039858010b68a8003200d8004000c209800055940c9d10000d50110070030440b11348081e100010309020742d0020314001e6020300000120008021800d40040008011110072640b50804101c402031003002520b8200c03010071100c8803201440e4295402a22083c1c00c05140420340a81b0a81045202e100820541d451851000d030129542c5114a0545070280a40f99018001c10890941541c4540c080d80d40904400485148507592368a6610501e0004c20252040d075103840d402c1c0024113028900f034000040c544024202c0b20040080000c000106000c000e160080001d403981d0340380da003501030715601c0031100c0c150f841381000d890300d850041c03ca94404070040f03400c00000a05101aa088280c1250301145009261 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 800580818 1250 800579568 800579579
    0xc050603150a031b0b130308090109081f11040f033504051e0d02240f0403060b04020a050a0f090e151e1c020a030b09100b0613 56
    0x15400c01003690070341c0c98004141c0720142e5112001c1500850080c68500c81105038030480285036003050700039281c1807a0801148491000206180045a41042c41241c8540d445001201d110810794480c2850b0b100e00e200000b601005880445e4444410b00810407035000c8035010200c06c0d0095204100008020f00410004503000075090305000000c120f0b480c0800005944640f500c4845131210212414081010b10150a15000b1074800c806c100c0b1a480c201600940041da50142c6540c000f4001d4079400c24600108000901d014049a074011005440b104189000100b64005100c180c0c0c0050801c0c076800141d007080e108481c0d80700000d41e1500e01d04140c0c41c000b5a41d8920360b00030101001120000000e00320f840018450040c24410050301d200d00350300f0700300680159924500030032006144601ca149903582079001c14120b0345015000354890031070000444c420010750018011200034010000401000705400d210b0000d410001c000d01d0506106201180c081c0a40154a0305101c542c103005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 800582068 1250 800580818 800580829
    0x20105220501110c071701051006110109080d09051b06030402010f021f0207260d0c03090b070903170a080a0b0d0221010609020309070302010507050f030423010c0c05 73
    0x280c0501510003c0740482440c0c1d201589135100c12240107540d04070318418400c21001c0c00c3d43c000402e00d800001c1c003a500b8140190003420010748035010500c200501c015003080402c1d0072060300150031428075610380301c0c0046141b000d0040754100725914010b094200e01c0703c0e0300740c00d03520240c404007400d10350440c1d40f280c0c010342d120b03140462100194030601c212009903110000c5241c5080b07016120150310b2303402c14945040300e51520300280b070072481c0c80f800400c51604440f0a55071410743c2c1c03950100f00c0400b441c0c001d4004004807800900031508801c1000504c42d04100045c04603071203188030722903104050307280301803500a140c01c41c0e00141450010a17050303100c0c7d170480d007182c00005100403c05c03012a0b0020360721185e45401c03003400c00301c440198004040300f0700c1400001c04075000c0642c9180341c5a2080e9881c1c003000d020081c1072010100c1c012083c00002c00002c002480b00008603680e0716214582058a1004279103070314130720303136146071041950b520424500005a900503040080305080c0410000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 800583318 1250 800582068 800582131
    0xf093816050d05010303020703020a06170a150504051f08070305060f060f1003141303050f030c07020604090605040c030b10081510090503070f0b190309240c020105 72
    0x4200050242e071a04148901c2854000d600c40e03001050514a50300c180040d0b107910764004000d01c10490b94030101e0340403031008140d024051040015a5075074040c0c20405901c40e54008603045440c00b0700300300c0c07481d80c000708108400c90000502800184d44000d808c1e56a000350100404640085001c80c00b5800071200554200300001c042601c080400000701c0c1145100400d50700c0000e4403041d5100050f4000840c1c01d4005091440350030820501e910f018080b4403494803000d6a002e0000300042003840c50720309959115078010401d03a0f8032036403200300f880076010034052180301d10304d45800b1885050081c0310760b20855070b0150841d09854805d24045e40d5100008008010850301c400084115a07105003a0096000607038840d01d08043c14a0241850062507420101008014041c00d00c600050740b81501e0b25480000d0b8585084c48207550201c001d0614003100a091150380700d040301c5414aa403281080220100404000745c0c4081d1b45c04a0076941c040d607290300280c0004603d0451601c42d1403410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 800584568 1250 800583318 800583361
    0xb120d030515090c03040201110601080a0803041110020a1505070e12010b10090e1e010b13030507120312060e0117010207080309060f0c1e0d0f0938 65
    0x16150408207101103503c62100b01c40d54091a94000304110441d030b000800c01c1000d001c000e0040040e5814198026074070603001c02c0141c001400400018200240e07040e0742400c0480203040d42082862070300001c1c0d624403051600302e850800807024410700d0f9580f8480d4501c1501c150b034904814031410030511001e107000c070220810654a411000340d160700ea4031195080c2084a80d20840501d14048081c040706a019002c1141c6000300041d4400410850900c40d0549200208103561071407070716040d00c003102c89030b840201180596900050307040c00044001e0080c40c0251607114140e00d001481804407100c501802d044a5a04e00c01841100350001d540030040012000040c40c01440d41c54000a6070802c555280a60f4000410400302900406410313401c040d5010040e400c10250303020000840d0030361040c810345d034140421203601800300ca41040e4490f1085070010400e04420307040103000c00305001324403680002c0c55600d89600d000f60000001d101c400d06142e0f03000c41c0e144d10790014404559200b00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 800585818 1250 800584568 800584591
    0x150a0c0206090d0f0c21171308060f010303090803070507090507050f1216140a08041a090d03060518040b04030923090f0601020a2a090608010b120d0305 67
    0x11001541d004c2d541c40076540145c40c940c462502c1d0185c401015106550401c0201c400c409000d40041c2c1c400740d900625401814000b91208056071030001565110740c040d00a601c43c19040c8855410b0071415281a02e0203581d500d011252030b0101591740c1e10031904002c04c19400007004025041d4540c1c09550040350a2070f1607480c158600c1c403241c20700c1c0c00002d102c01c100c0080d0340c18445d04241041d130f10401c15150741010003031604081a003c40d80e014028a5205200c822000202001144201d15154026050840c003075400c00d01007559231000d080c14003501080c80c0540205840c500000880442000418101d210384c0d903554400400160180044003031001c1030030081104078030b0154070080e091070341560b90041c00c041d0080100810015200708070b100c40c003d00344407043c1d9020031541d45c2d643d002008207c41c560940110316a1a01022480810307100b20781740441c88141903008541103030800b80090082c01d01e0103080202d07003420700d0514038981d800080b07007407007590090708025032154a105d0b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 800587068 1250 800585818 800585839
    0x10c080703080a0f1a030c0411030f04050316061514150d060305030a1812020904080304031106012c071b06020d020a1214220f0204060311150a0c020609 67
    0x1d00301c040c0c800702e04141c02d400306080c1703400c1c1441c201000f0320306400c407089509208240a4090b50041c5110251108034998004070000b030038020101704a900820700c0c1d5840b0940c0c0a00b41c00c010000b4100b8076041c4080c4402e02d10002a40420f00ca124029081c0081c25142440700c100c001c455554803070000000225150b420001c0407407002d0010707154200c5c007522405070707001c400102c42494a03e81d8002c1402224481402da016071140c50b5090342c881c2d440b0500a5407500c2d18101074a103004184004c101c1881800004501c40058a2510210711300c540050100f0300c0b078224668544c000120340c4980000e0021104483c540c455080744ea10040c0101d200603e046120300c6aa8142d900c41d000c642c0109199050801c88841d1502c600c10200300001c5004405091504c02013600f8003030400c0148000e840c482d006001d119060b10580c05266004101f000300302e03a00d161440075450940718452084640354100c5031a0101d010490300d14035083d580700c00700c00c440d540c20000c06030042048607812220b020b8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 800588318 1250 800587068 800587091
    0x1b0c020102190c030c0e07090302040209040f0f06080d0806030c040519020705160909020112020a030b0d200d03080609040804080105090a110102010c05040b03131a0402030705010c080703080a 84
    0x1204402d1a4001c0b01a40ca655046040c110044d40d13140d84412003000041d03042003601c1341d00c41c0888040c0c0742d04031809030b95601d8440024020f040c00349401c0d0130051802d110b000c100300565000750200d51001003035950114010400713441c1d8610482e00039426030000f00001440745490351005a010441d4860030340620a05498107040360041d403811145030303104202080c0c111a000110000400606409001103d119070000b85000701d01d4204501454020500c0303118140030340c12900e100b04000e40111881e16031030400c21900c0c030360b6609004ca1a2740c0c103401100f903802d0000031804000d41540300c03c12aa100d4400340000454002c0054991080034800030840c50800e005841c02410040300403e403044c2d03a818002900303201c1000742815680350081d1080c080341c20000391000c85091180682e00e0340c0e0f50b481520f000441b403d1000b4100c0c4507408141c2907410f04a0440c038002c40c02a82110001a100c100541c2d0f4801c0c1d0341c201810418040c4040b0002034450313160580e0001070f024000c200c156070344 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 800589568 1250 800588318 800588353
    0xa03060308070503031f0503101a030f030d06050625060f0507031a0915120708030708130905010302130506120f1f06050904030f0504030f03030914011b0c020102 71
    0xa481210f0580000041c0081920a464244d050400501d030703000c90b04d0301c2c1c07100183c2d0710f0400008507a0440d40b103002e414444152191203000042c80501542ca03201092400e0303035120760114101d01c941621340722022405040c00d0040e5643d01c90240514000c00d8044691514801e00f00b0340101d816544516003000b4005403802102c2c00342c03045481c080381141c400c02400c2c15900c1140c6101d0b00400340704c01006800350b01d9030f60441c2d10070070070350710005030030f510a080b51300b0641a50400c117818400003980100300310940d4001c0070361102c1003462070003840e22003e0000c1a82d100b03120295100301070f81012140403025501064200d20014541241000c4100d0500d00b00800884801ca09400c0f0060030580546d200440c18030400500f082004468145400900003050260001d42000b03281c03060708595502501c00c44020790342051190450540e9481d008014211280040700c01c050016070003154488140100b1105044510703030502961000324040340c2443e40200f00b40d04601c1026034003140000b00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 800590818 1250 800589568 800589577
    0x90a0908040b030708091c0f140703110d0c050d0f050d060e091b100f0203040b0d02031801090b2a040b25030540180c12020a03060308 59
    0x41e40c180c0c0c60b1301e080500940356a400500a014641102041401801d100602401d82188078100080543c0a02c0001c807004052032116a172260800916041419001540501c0700900f0030704480f11400c900790211440c42004000601903440b240b204800c29004441a6004418510b41a81030041a1154405480c181c1d409074060b0020349040c880c1a40083c803101a0024070b800c48d02c880030946070003080104200e800311101301301001c5500e0340440e200340f040702c0007050342400311a240d0058891500c000d600a4942c180704071901c140182810b01c0c18006e21a00756003000010f80641c1d90240c201c01c6445281c1c1c19001d580c45642d5094980440c0e00340548054008050056241c14522906038861081c01191a91401e20900c80000103640301e000c813101c084132440f00c5148003685c0601381100c036240c0f04c0311700d180340340c241040781a070341850300503104031000c90317820608101030810103c04513601ca814100c0002c0c180c82e403d07080da01c01a0001d03c8030151518000800f980d981d150038005801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 800592068 1250 800590818 800590829
    0xc030e01050f0d0f110933040303080105130509370c0504051305100c0e040e06091002160602070f05070e0907060311030406090f050601090f050c03011202090a090804 73
    0x40e03562030a02c3c0d025451140740000c40c0301030500391406d15003100103203640081c1c010914280b119a02c0074140544c43c98407198044540f024030a407038646038034024060100c04d028850103080014803030388c1d13110000d01801e4000c8540388050001c881d60b41d030241020085c070070007c00c410301e001541c04190920309c1c0803910516000b82c0349506010305007c00c02040c0c8070301400d4002c0147c980c181a1012900c08990400d0075901d092000030786010307241c0103494226120004a40c044d18000c82c40640640c080754a81c03040e00d00318241c1310038500c01c0240380200d014030020f51401d560307020b55110000303941d54024a8407500070342d002c40300d13000d040d0343d1a40b5002e52030700f00003e81e200b104c050000c80701c030811205002d400d1506040c010445606081001400010700291509468030068810f005a89010f003400580017000ea915940e140c80241c009071031401f00001100b850680000d8003450360302c041e64182c030a00d40c4014500d011940800c100420040c0495044d2541c4088540000d141140108014031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 800593318 1250 800592068 800592071
    0xf3c01081009090c17011d120a0503042d02090703050405060c0a0203040f0821030c0304230d020d090509010312181e090b03010b151c020310030c0b0a0c030e01050f0d 73
    0x409100c541c400387d4070300c000410141d5012101c1400700d4100141582c102050601c1c2180d00c81d0340e641040c40c0e41d0801c0c40f040d0394130050034003003032171400c5507007030580075218000d40b5441e42d1a10303400400c0f000ca406c100c1e0080c0a03a0800004a0144201c000c0107080b80c0441c1e20499091a071245619411040c0e40c0c2c3c07107070103a540100d1007030613160700018a0601d00690001003d0542c98030035001c0100b840000d1000b068541d00e0b81d20750118805039102d10703401030011400c0710b0501528110180d81d0f00c90796941540803417501d41c40040d0074503141030311a040c0c950240342041c4078480c100b41a11902106100c1881030300317006e01c0215800a4509a07400110104507403480380310f20f8142c0890032241d107124018042d0341000400e0b9015145c41c940f00e109034280c3c04c84e00c0d40d144003141204010390050b00d01c031703c40c81c1d00003c103119040940000c1e01c3c05990068411081131a5135a5005003144a803444400100d590060a20046402140840340305801814a1494204ca0031030801c680e134001c418044c0c005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 800594568 1250 800593318 800593331
    0x90a0e04050f070b0901030203060a0e0f0609160c14072112030c0c030f0e150403050106060c050a06200d050703290f3c01081009090c1701 61
    0x34100001c207020301424001e04180b600702054044c50780b28030720340c11307041c19000000b050040d100c12012100400819410001d84d05040e90821801c01085d528640701e4803482004c0f030001001001500e40822080d103c0c440304909a03544c0030b41094114030114810300840d81c0014035084485e10714150f400a00c0100c80549125141c82c001d0410b100340d142d03041500d419000d180c00e84d088030103060392039018104450801d0b5901011140314110340d83c8503030069485070720001c50290000c0a442540d1091009000311901c9800031110800c0b070500c003600e10b602041c6910003040c3c86510581c2e0300d045038121461044024902c80d0040e500c00d010030011244c6d83d000f04120340754036200c0c00310340702880d107404d500d401c3c0310340c07990070409182c40d041034420030520608a000340d4805182000802940400d56550300c020b004050180c400d164030b020301041c004002031499803168078400d116800e078010811215040000d0307170004110709002220725160410303010950020404c50a5114000783c000031a02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 800595818 1250 800594568 800594573
    0x50316031e090b0c0109080d0903020f0a0b0f130606030308090616050405121615020706020703321f0e0c100f0516050c15210705090a0e04 61
    0x600c0d03081e40340800186903001d64aa041c2e600c568000100c070040d0780309940303030b00781404514010010080003c200b130000041441d040405a00103804007806034007a20705038194140199240e09c07018a0082c1311040001c002001c4115207038100c0c4c0c0044001c0b0005124455660380c41080369090f402c20b0703010507900400c000c2c1c2500c0400075107500c0003d0196150301c00d618502c1c040e10038081e42c0a100d20441240c00d0710340e45c0b000c00b0024816a01d030900c050b078441c540d4498604115552071513203040107029941000c10400d00024034201120340c841200081018501400114104010f60b44444a1f82d0081c810306502000c00903404d80c00e00a40c6c0501009000e400d40b03004480352001808620303000b0f03201052680e99a064071b001a82c11608201c9400c06211400315414414241c03801080c04190710500c042c4113001030f03e074010a10a5428000380e801007014510070303001d00e44001d2603100c000790000e4074106803200c5140d040390032030900303600748000c03803000603070800307483c0c10000600511004004c01d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 800597068 1250 800595818 800595827
    0x3040c1d040b0a020901021c03091b030303060807080c06071712090f010e0a06090614010b0409060e1306111c02071511041202061b010203060901051f030b0d05031603 73
    0x80080454004500c0d01440c1d000103501c401d85007041c0c841d003030200235050080b9030090300010304440d800340400d140c500641c1c03481e5004007500e02060300000c1c134000021580d281c000404200b61000700700102115542081000b0156005900480b540a10420440301a60084002c0c00b611003081000500c40e203040fa0703e20f0318002e504100c1040702ea060000c4800e040c10086a10010990400d0300814401c0042c1402c8015050180c00c0e178101e030111000000740221307204047c0c001c0c0c1c2c003091810312500da622407121030328000989030802500d02401da0200091213503131280a0300700610340c8403420030038150502600d0b0314898038800c6113690001185820800c400c0001d1500458031241006141582c0d803406083e405103001d40545034403040c180f03000355500c800c01d50310202400080035188018498540c1c4c0030750402e441041c000c20405001103103915012003602080100c5d240c5600c03e21103900e80483c00b600d100c1300e180b0742000c0d003c84024040740c8244010503251031661440c4082080741d180061 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 800598318 1250 800597068 800597071
    0x10f1413081615021b371e150c051204062d050604090f0b09030f03070306050f0a0303020d140409063b040b041a01090b21060c03040c1d040b 62
    0x15100c1d0006c01421200785a5a10000350140c1c2000980394408010722200c0800100c009010342154000f8105100000c02e007002c000c149441030703a000c00c8050a002c1c0482c1500e0b80000c0c03110120300d00744444081f80000b0902d0540c0306014580102e401248a503100b2281c045135032480301000c100d00002e901c0121940505a0001c1058074201b26811807030701c4080600c650301d10000c015548103404541400810820340d02c0001c40b41c19003a60303d0804090240080c465445003600440044480c0c03501c0c0d01c0c010140108485e015005001000031080302100c1c2c0011858a00041e083c0500c0046600581c0f4801d6002400d0b803220750a0042c01d441000200712a00301d62888140c284001104005a165044241d0400c0e807161a00c00b140d1524902998038000080703042810681a01c000201160b581c5c110401e003c2d025607040d001c1888841c00d45404016132102001540e0121001c12034140066005540c454060701d42d9500c41511010302c0c040802600544951164005060100b44240208000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 800599568 1250 800598318 800598367
    0x4080408120f090402090a08100902131e0f0e1e060f04030f140904051608011401022d160e060607320f010f141308161502 54
    0x5824002c042001ca0014401d8001040c010b42d00402c00e2591511861a050701806d001d80550310a4041c00304d0140060204a90581c0b241da14016403400d503280902c1255564090070941e41d00800b1401c0d10100500741c2c0181c0c60340e0303281d40e604800c00c50075420b20142c0c480360350322410f000000c64001d80c120f16112011b040e105a24034080705000c0041d0b00007003c0d08a076502030800044204211030300c0045c0c1c0c00703000786182c1c016080c4001c00030790402c0c3c1c20b60001054025152050030380d0320b9021300c40c41c1c2c490300504580035a2100008005213144c520b4401e080c600d980c854400f41c0160198001e017818510790243c180050246030a00c251041030801a6008009895883c201441c544901c064007880d04840400024040708131224140ca11507000440d031501021a500c041c1d642c03c13010300808400d04076100891900e041400c402600d6030609001d00c6501b019894640c0882e10b8045059000140001400b0ba295000c90001881146500d0044102090058480c0c142c0c2d401440390f404030710040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 800600818 1250 800599568 800599603
    0x218040507020d1e03060b07050c1008060a03020613050303070c081203070503010b1c0e070303140906091e0307030b07080f0702030414040e010501091d0606100c02031504080408 78
    0x6400c06030758490031002c0405104013110608021040e800d8008000541001140d14000550361041c004002171010a9200a4806141e070740d102c1001110b008405550f02039104642c030308104050710303000d005414a0354005e1700d402d880e81e503200000303440c650281d0401c0f544582c00100400c82504103005030307520080c06072442031642c9450341000b00540300500410840d014082001d25071000d944541070380812007040c1c1046000101c07030495680d00c2041c0700450006002c400a400c1490003c020745255030383c0900040c0c10054140d007048600f00440740e01d0210035450000701c0d16a035a0421990001350300941c0b440031542031544000b0440c41d03000b401442c690403484140035107198004215811218005198499008007200080140020b58030001e03841d82040700100711503186030300c5840851109075034005000c60f8040d0316a00c2c1c0c40101c591b01d6102e20b8003001e6840c103500940440f800c02e44010169051582c0030050700c2062507080d6400d550000c801314080c0081801084000c1086803102c0c00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 800602068 1250 800600818 800600833
    0x18070903020a290a0c020a08030c010c0c05120f070c14040c1e030b06130f0923070f030207060509011d0f07030809010201090b070302071709010c0b1009021804050702 73
    0x1d5a4081c40048440103e0014000740300e2a80710721501d20340b03d8050380105500d0100b5a6603d91541d00d42008403020500d502c2c100303102c4401e9000c0c80e844061240d004020b80144004079080313098070340241d00407040c2d00108202e014006000d0b00c0800000d00b1a80c800008445e40b00c0041c8004c0303075400000300c4240180e0203140065002465441081040b0500c0c000c04c010303224601140480c060350207021030480d01d0200209140d0080510b100590381902d000300000c2c1d0340518540c11001040d00d405500344842804900e01cde078420440140d141c1810b00b03001d850240b03103a0b00e0a040301d078121640203030760b55038180c4000103403402c06c80c201900048400510a89181c807103103035202d01ca103220082c40c60900003210f00340c6034001e410015507150061406022894503d5014029510008003128881030b01d100c40011114080d00340c4003c02810f03950303901c04400320398850011b20006481ca080780b200306440000c1da512030b80020003100241d01c0030803820001d050144826650f024200c0000d6400c05007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 800603318 1250 800602068 800602109
    0x1020c011a18090c03240c090a030b090115120204050106050306060d0b0d05190b070507080f03040c0e010902070c0e0903070f030e03070b04030209090601210218070903020a 76
    0xb1080b6094004800450680e44800d480301d0318100c08070700e060b501800b0340040881606035000e002482e43c4031101d1602c05030b035942e2481d245d0700d00c01d0f02c0d201640444036400620224150b2411181d000f407a480c00007984a9101c044001201c1440d8031140102d450750140004609080c00703158010481802c0080c114280580050105c0c00748241480740580d4072a80300c0c4150340c826002000c1d00342c20600385c844e00070342444c41c4940f5242c01c034402c0e507407a140d200200e1021486081124525034100070014107200c102c020299865101030130035908101d00140c0426181030314621030b8024110980e0060342c507141890582d55541c80703544000c092890b01400c00c00c2455010080b6a0030517403120298424040302d11f4169804020092169090721407190003140240c2408020300542c1e0007140c003071030b5599503a40c070341d0f6581400740900b02c0c0320b45910b0503124511150080c880301c00b52009015103801340c010704d507590081d413040751858005010b041e0100103506100120030090b1220001020788241c00710f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 800604568 1250 800603318 800603329
    0x100e0d0c03090504391103030f150f0a15260c0f0d291f05031e0c03011a0a080408090f04180209010603060602100e160801020c011a 58
    0x502c52603004648915403032013603805c5240d00703118990842c10701400144076182498a003c0c0b2490b441e9012503038103180942e20781400820f4900c01e0380242c00c01c200b16039804610741701c0d480c400280f030740e00310011142c01404e0b0780c1c50301d607102d000d00340b200c008001c01000110700801b6564102d040b4207200a440303404c40c0c0c84030001102d07258030002940381c030360b81c680d2459030f420340a10a801160a01d1072401034050f40c0110003440b83c0d061208082d200b0300c101c0e42c100080028464042d00c511000c4002441d4400b13185000340041c603440000c429003a0032034820b400c1102d4500104480541a1b410008014080d000d008107500c904110b280585074102100c941000d04045c2000e0006000302402107503004556035035545485180708090801d0085890103400c648006070120401c9215140620006c5000c0d88680304007001c440b81c0342d000340700e1068241e94100042c0104200d540e0180500e2044201c1a9083d405031401002c80c003000581e1845555180c0382114021452034030307101010b9195000c2039444 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 800605818 1250 800604568 800604587
    0x111f120b010507050a110f0a030f0516150f030b03030a08010f08030f0d0b0628120b010c0201110c0d05210f0904020a03140c121b030c070f05100e0d0c03 67
    0x110202e621811506d00c000703000c2900200d030703455002e0800f4101108100005081808243c4110111210038500542c81c0c018229a800344000c0c100c00c00d58a558074030310514520341c0031100380c200090005500d0001c00d080d5407026294070042081540100022081c000860004008601c06181020b030b10440c03880513803181a841d40f4a00d0346500701d0000d03d0391a902203c451030140240c44219083c4074514180036004422030502141d201c0300210f071070303508a00400d5020342d0140e48000e91368481d51b0055945090740c81c80412070740309444c1f94209584900c08440711089c0107030f0040000b00c018803110008404444031031560182c00303001403511200010250b80241400725805038030f41e500a82d003280104009407022442011000a206000184500508049a511402d684299a43e00e4201611505a600c00310722000c02c1000549046180d809499000d00ca80415051440c0b01d840b07840c64245289150441540c0d80d808000071418100b100b1007840da201e0070001082441500c01a040540 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 800607068 1250 800605818 800605823
    0x201050714100213061e09060309140a0804052d060a02030c100209031b030d0c1a0a0c030501090b090601030f060902040f050901051507111f120b010507050a 69
    0xa00740c403210280014440400410700d050720840d141c0e000101d0342c10040e400d51082c10003058001074502c0d04c420181c1801c615808042e00c0700c51441d8a010002c900500d0304d103030107a03524000803900c400561030a0103040d00d8540600b4041c0d80f100c3c1003a04204444804418034000d00101403000c0d12191040024045031150031a10a510380b000034000f64214810103049003018002d4003c103008500325503010b031500c401d007902260781c008441040581403104503503002c0d6150340300d0082a00342602c45ca07041140b841c891940c058040c80c14420b010031414080c3c40d1044501d45502031817505071b501d485900d00400e0350043c1844201044404540d481d480549294105030b200d001c0014544016003000340100b010000c115034840d625903800584035100d0240920501c3d51034000911450441d0021090a650b118098900122070b520300120a08041030382d03800c440314028a192112071854840c11111098072800b00103c0c0c2c82c45080101e41001c000541409014040c10020940004e4503654540c2d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 800608318 1250 800607068 800607083
    0xe0d0b01060c021503070c150207080f0d0e030403241116062903060a06081c030902040501030803100b18090a0e0703030507030e0904020105190e1903020f0d02010507 73
    0x1c0030340003040c2c4019203801c00d0b0740420000024811b41d03da20000c02d40403503004800b0103034400744404040c800e80c03251031000303030240c0340510076690b40005040040c92300c410b04441c005035101c2e0000c00b803400d5420640c81550402003500f8910824610f0342c8041e01c40a550345401c120200b040d188000c0c82d80645101c496092003190541c0782081070651081e40c000b00350711000c801c2e2400704030b6003011100450390414002e000c0c860103d02e0054090050303c040c0c40c82030024111015102110704e900603c4046210105512080d96802584917071140d50f018500904815035203146c01b1996080c500a6039201c0803130b61701c0400045444990100713190302c551408072543d45050305c904203000c001c2d00008620031800d0050358400020581c000e001400001d1003034582d800030b01441810880382c1d003802c03200680400c1007000070052a03140750701030044011050074040048a5a0780110b03801114005514103116910542441549014141e200380d44030110703071020740389005600003040382c0a00c000040c03414 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 800609568 1250 800608318 800608337
    0x506012303060f0301050112050c0d0b0f0403021006061d090712021e0a030b01020d080c04060c05100507051b0111040902031b0c0607030e160b030615120402010e0d0b0106 75
    0x580d24203503031001c00740f0f004000307002d256141c005080b180f41c1d00d5041242c40b445144000c0c00641000413015003c241c020840d2291070381d900d614900184c00081c412011401a8000c40f03100150030701c540b50245c5810303070310911030200b40304003d5081082c802030244034901c2c0400700201142e0012100d00c10011314030000d41c03100081c104802200381e1000c0b01c840f42d0754012846a0b44540d060740050403041c0c00340c1c2141c10400c1d8074882550400f205890045a08208000034032109010780d00300c90001d0300c10002c6400816030403010000706d460a8604030005080083c0d03d8445e0700000b2445107250080030020800d1000b850040c2c0c0403481148550201e40360044000f9002c51503950300b914420b6000d801c2075070369410389000c0a460359011178400011074941900036800e41000200b88112513010380b40f540b02103041ca800446a60402031210f46c3c01248115010301c03506074400503042c0e00c8000d10800805040502c0098000841b40080c640299030007901600400e059602c003e0440c0c00a041c2039000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 800610818 1250 800609568 800609581
    0x160614030f1902070f14010e0d0f170a051e0403021009141615090b0405040c03020705030a0e0306072a0c051003061a19110307080c1b031f05130b04150506012303 71
    0x30302034056007410a00be0a0082200d0003c0a030400b52240d00340014036200e0360121411103802503000d403405801a80001c47e21b81031660f160340f000403098010300640e06042c00b01c030f008501e8175000361103401042c0c03880b807401c01440e054501111428115400d107004c645041085611103401181b02d02d5118a1b02c50307403800001800ba41c12141000d400c0000d9903516001d081c40580700c42c100c8a81107000744581e00018192911aa6160000c02019420b0400008403969074030522042c1d900242c0d05410443c400080c29030341c44685460720002034030041807040c030300b00300380c2d8040964400301c010003003013001382180503214840100c051440720300303045c200d04681c144914918061a034009100c4000000d03007035901e81d03001a2918000200d8031141c11003030040d40c181902c5020b00c090359401402602c0c2c1b03850503645582c0102d54000c406d081409000c02060b01c030500c0d00030b0150380a40340058020040300e9000164054507500903400e0802c0704520b080102d0042000b07504c07510f1000c80240c04400b0511 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 800612068 1250 800610818 800610827
    0x12020415081b1801150f0c080403021e04020307022409151504060b040504200414010c151d2406010e0a08160614030f1902070f14010e0d0f 61
    0x40c500d0480030682c1c403585c4030741030400148035100c0e0310000300300e2803000300144a101c1c10344500f5003036025a20034205803a6030309002d4641040300103008c10010b04296a400c40c0c03210b10281d031003103200754000c01514080d410040d90ba144449141443c0504070b104101d07035100e00060790444a0201d190103102a80c0d1001e414044400320b6000991003810000009400d1103181c01400c1581d00440d010030603040f01e040401514500d0009152800030180401c0002001255107001c2c1c1d01010304180b0b10f400d600759503848104003510b984e1841141d0b1808403c000e15610142412a2505800180340700b900031034880380410703410214030348621307003032070018040ea48a6503401d907034140c01401c1100620346400b8480c0e21030021445484030302c04100700005906104811210342c4008c20401d00345580c44403005d808001c803000b03013a50b000300c0e030307201c40c581c54850300384010240d0394052031015215200ca4686042c91501011200c1004d03814404070100d80c400104044000d5200e42c00d11540782d9401110540c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 800613318 1250 800612068 800612089
    0x4080c0a060501030b0703060e4c030b010b04180b01110a0f03020c0d11040207021504090b1309031b02010210140a0c02011e020f0d0612020415081b 65
    0x1c000d241400000400c228148a140d1b00880d05c6071414050301e40c070f52040520f529000c8450b03000c42e80455450910040003100300d005032003e10880d559041c0000c0e0041d1485000e01d0030100c24481c03c43c2020401d00c51181d1280c1e0150103003035002482d091404064040094035602c80f00d5640c1d0380d41d450349085078090503440015039008816519140c51600380031540401c0e01d00150054002d40c0c1e40810076140070200003d92680c80503002e40070840784404c2c0402904036030307001c076085421040103060b48140c200c003a000424506002145441e100000d20288411080039507041604040ba244002a08000001d0420100086202c02100c0300d0004034500046c03020003d03a810700c1e0101500d501507030003400328031498403031324144007420503c4002ca080f18240001061250003820030090a82502d800804505001c00b04440c14546140d21502c01c5590650040080d0311103464a030046050601030010301500600c00d2441c600d1921121640f81e6100d06c2209200407a454460400d59172030241e01c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 800614568 1250 800613318 800613323
    0x10c08042003061816120606050a0518090c060c03041403010614060702040609020c030a090b03070926030f030115030e0c01120212280c0516020418060507091d04080c0a 74
    0x4082e000d549180082c21000004402c0c4c036008d003880008203440c2403584403103045450142015403540d61700700d582120018060003214650160301d038103842c01c0da1242c026140b403400b1040a1580e541c030780515030a00360060080c2501990401008101401c0211248907036180d081d1101a581c68141c4005401400541c004941581c030110b49076450704d000102812459800f0f490f00d024158485982601030300080300d544001500d603031018416500302c411001a120000e422007109840c040500c036003076810101e112505824088010080d003010040c40c2655580503040400c001410540c4240d11403900d120303d1810f0000b0600b000d60301805c140e046130313005101c165110880d0300b4000c4010b03085907000b0840c142413202404202c010803c262082c01995001030712000d02d0100340c1010b0f010706011074007040c0e901030343c0c0300454610b40b10014034072154507108440005652405900151401303080d80c0040c175036164119611904441e00034510394020b60400078203900c031100a14050701d0b290708035400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 800615818 1250 800614568 800614603
    0x14062206090812010b1b0f03070206130308031e070c050706030c0905040f0902090c031e1b0d0b0102060108150606180d050c01030c030b011d12010c080420030618 71
    0x30316a05c4890151100325401c09011510604000007182c4e00d12000684440b42d4008001c3e1100500d402001080500002d40c000004160f903501d940e01c2517001261144c5a1202990340b241200046041c80f65102c406814202da4004140e1075080e0707030710200c2c064001031554503425481c49a00035281c550042400900234000048001c0d01a406450070308801c90280c1e2402c004100c81c4485403003503c0c4100904000e860024440208052032514050710011045804000c01480c90340080028164502540030100c3c944440070002481e00034164480c0344240c100046000507280e600d4007241c2c003c0300445041d601c0703002001016490b42c515a00381503004149070244010804003141d08034000400340c034100580c4074009400c3c2d09840610b0b610a000880851182d0078203200d0b0b400310703420035030041e02c8811103490f449140d80c210751070800b404010468403010071040110303c101d0803800403103030403003450082034071030100e50344220140038210707020000d80d080301070305c0c00401246030202ca00504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 800617068 1250 800615818 800615821
    0x70c06051008160f0b090607110409080a0f020f16030b06060c01091b1d060d0f02090106110f03070804120f08040308040e06030f0705010c1104060314062206090812 72
    0xd00f005494441c0c401ca0001c10000b21000034802c00c15829929410005002c3d0f500d0702d10b0540d41c0ea101060200d01056225a90b01e40d04400302d01104050844a0a90349400140b030003030300c40280c80e014100d800640164010b072110285004140286000c0780d52000300e50526031034440004941e8082c17420000415031070a080403080c04095082100c00d640040c180700c5115071600e0755400d0740310f11408158a0120100082011803c0441658800c2170066416002c0070400391b00251101601780d0080000030f44904100c1c1d0b01543c02c2c0007100307001881d000114a8003940c5c1d030320040d082c0243c0c07141007840c44000d00c00b41e041c030460982c0c00344c030365a21211442d84e541d12454081c0350380d0098003684d44890101b000203441030400054240c034240710080245507540c42d000046800c1001200107d8030028040b050300c0c2c03030b0b840714000c6102540c0f046040c50102e84410000038605000108624005032103c44594202480468a010004d0308040c0c00320f000802e0b810071480314420070000c5800a1074040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 800618318 1250 800617068 800617093
    0x1309080d0f0e0d200109111e0a142b0b04021c06050a06050d0c03110111060a051816050907031b0c11011110050a06030f03050a030b09070c06051008 65
    0x4a00c41c0d4401110514042248080c035000b070308948403003c004040d0300921000c1f009914280c00b0895200460a203141c2e04070030100c011925452190b4070010000611a17072500340340c50003403008a0540c00d4100000308410111240240d114041c5c00080c084901d19400f00d019900c9898000500800c0c041d000036000349646031040c000c040c101c4e0b040c42c078549000400718041ca080500680c240d900440f440996508540ba490b905c1250301103441d06020b2056113500c020042405107a03c03a202103000000c540c50820b51b80c1088010b48100b441c1c540d005540d402c000685d010358014142c40054440600070b80d00c8c10000c5e001411503e4801082001c1d41c0c507080035081c0c1c0548054200d070b200780c41c0c030407101c0c40400042d2007100d41c0206c00741e4075400001044801071840d50105901c0080c0d0000850259507940329418200b8140300180c001078800108183e5298260103400b440c01400d44070a0b6142c508002c008081c0b01041d00000c1106448401040d0700c0b088a58040d00503180440c03c0d9401d0116a1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 800619568 1250 800618318 800618327
    0xc09120a0501051506030a1109040606020307020306060402071a07200a110a0b040e040215070302070e0c040e190902040e16090501060801260304060e1309080d0f0e0d 73
    0xc0c0200e65540c00d103800102c1d84140c00c5844105107034050f007684d041d5240c0613a070300e010702840078181e0004001401780420075030361805020000d1025401440c0d803014503005041c14020010300c1503000754010010007002815520700c0c88045010101401103585412004a0307003003000c0d29101c501303030b08408880e0501d100c001c02d5044c2828456100700401e81c000c00203011505585114030503109030f00380010080d00184070300c2c0710307807091004060b00c84c005e284004071a01500320a01c01d50050344441810b020030078081603611741111804030301c0d40c1020714100b86400c0c1540010040110a107402190603c150f540340c102003a50340c3d0040060002c0241f180300c080d81d40d941c10b201000410075105001a9401d841d10405043c0c400a41d1108216801c0c04600b00c500d408202400e0199076400341d02001d01103041c009440500090703640c0030504442e06003005002d180f0311506203141c500d484031030790016104404440314110080c0380481d641e1202e080801c010306200c40240c1d068040c4820740a05203034030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 800620818 1250 800619568 800619583
    0x1b05040b03010c1d0102031303051c0c1e0f060606030b040f06080d0c0305190801030c0e10091109030307050609070e13031202040816060f0f05030f0c0912 68
    0x166020080d052103030040600b079603003c407030601c0420800720401480d41d94006002d850020b040c0110381c5030400c551150a010b99455205a9654002a8070012001ca0402025030b18030703800d140441a00383c4030744401e15403130020043c0310075a801d0308480700d00f00120942104541c4d604007100700107a9a036684050007500c1224846886140340c071004809100c81c502c91070081c3c40c00c0780010700300380d107048a06440c00ca2039010300740d040c0407084c0800b1042c0c07804460902190046691692000d500d945040d12042425811040480000108000c000d00c88240c90303004482c0c40900c00b241082d203280014210f4440c840d031040d05800300150303550910400245c0c05000b242c0f00000c40b0760f030940e01d07c01030603061740c181c88074800140303c00e0028000c00c1c41024080070741840800018541940c40040524028400307060410540320741d802045203541025490240c1f0b031413405c2900c03a6040c8200b0041a900c4010000a4524290408203412415610507212101d0000d0160442502c008201c80d039161407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 800622068 1250 800620818 800620829
    0x2060d05060a12050606060a031506031e0603050d14040f033804030e0105040e0f070f0e01020a14030d0c091e1203080702010905190308241003091b 65
    0x40c4a20005100703c2800070f12240700e41c001001d405e280d111241040b2803980510044010982c60341c0400e0000c40b52000184001d0690780c03000036800951465034442c0c0b142c00f55800741d420380f80110810204002045012204169140c480840048001c0420644c080c9401c468659256094013000f04102d240015801c00408901c6660001d111080d03070300580400203038404411a941c02003000a40145d10700701c03007014141400c1d41000d450b44150362501c5800c9075820400210502840078054100901806001181c5840e112800040001030f5880081100041100c80c440d86440c0c41c511051050300c00c03440404e00103016684801e603000b00ba4050500959607c154558142400348a041b02110115580c150110490031415202510035000060400096540f51590b181c0041ca0520001c07140013039202d0342070120f11007814018120745006041b141824200910046000140ea4081e0448407048544035600002250b0450160016503001444000c880f140c0c080451400080d92055a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 800623318 1250 800622068 800622079
    0x1a0a030605030a1115040509040c050f0f21010f0e010209100504080d0e040e0d02030a0e0102070515070c0806040309210b0c0d0204030213020309070f08030a0f030902060d0506 77
    0x7901e8030201922410002c000404010380007210420a0810f0703141400e0801e41c0e105124105551036010980311303181203030115888807210304203109518008402e198003100030388205a5081e50742c0d003c903d40401d42664003e41482e105c1001e4115203094000f01303400c45018006018400c0c11400381d40c0030350451241180304d809001c02e11000301d881482550111000f0400410358602d012a0540740b800e040c1103641d07006603c03a0034002c09520100100b40c400d034807aa001b142d071644248402441d408c0c0101055046403c508010801540d54140c2d11138060390360043c681e80d1301500c3c6803400010059a026040038041c41c8c04000c14550400158011982c038641003061031029180e81907640451070800501010860011030b54004850000d44080180b8210043c6455160380010b00001a104608901289c00104201f1441000d0014131300070807a08907041e0415041440e000d480c2d00401800400300b0444401e440022482904611071164000c1c041d242e071107030100c116070040c0600325441c60051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 800624568 1250 800623318 800623331
    0xc050307060c0b0a0506010e060a0f08011a04030602090f0d1203050c0309030a0c030201062711031b07020f06030703151e030b04050307140708060109020901271a0a03 73
    0x168002c0c9459158258020518191943c803039060394010b020140030b16040008007d04921301c0c0d110300c0001c140ba80820380390b04045995607000140701c031805802c170304003141314039280541141c036204c2074906882c1d1003100561500c2850020481c5a00c641e0380ca160710101000c100b5041c0001c02080209510542e40e0074080f69a501c0100e410512050b101b14540340d20800c8104a49807189814509061092002080c95a5107030810754800440e039100d06030b01c40d0071809108043d4020310500c1011003188490500714070f007020312641c03c5502d8600241e04035030300160000c00c66582000101189100406a6449042c41e140050050807c101d21071941700b645030010440d50883c0400c80405a4000440305051b0700b15503036545108400b13071040725030384000e200300d000003910b940030303960b001030503400030700c10b045c1f400b20950300d494810b0303001000f00c502c10010586142d0303200d40d43c1914624400c24035001c5800c0d18160f07022841d10366200e04400c04940641031140c0c05014020410302e0001d80d01070018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 800625818 1250 800624568 800624579
    0x2040617012901120e060106120e070e011e030c09050405010e0c0f04020a0e0411130b0f161104110a142a0a06021201180203151e04090c050307 63
    0x80c0030320b0301c1c0c907000000000368124480d8441c5a82e810700302100c0f440883c808a00d15071852810030280c001c41c0c003152808401d151b800030345200d084d202400d0301c002414117611b0482ca42c0d04a1340c06001c0c010f030720310021a400b0030321403440e41a41c006540c80035010a41541d0303440500020002070703c0455080d401e00720a507402c9000041c141c490301800400fa09140d0b0040c2003040000c2d03101010a80c248054186401c07220350300c511a005015109520f07156031001030f101c480b807401805412051051030180088812010100c081d50326602c1155100301d003880d00c0e414002001c1d8800458150300904020010340460045030140580c1409a250f0715800b0b289418201c440d405254918960100b00c50902203469450010303007429442c02800351440b460082d1a00740c00c1e40e00050500aa1022003c0100b1482003000c0743c640c29200c0e29101141103041009240d440310345a00c24140c42060304200302075415401c81465081200300500030400118649800980e030342d118421948280290400002c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 800627068 1250 800625818 800625851
    0x90703030e09060f060309210408010c080c16080c06070e21060c1318050f131104052805060f09090a031805040207031101110a21090204061701 63
    0x2480d001054554070030000d100344817a942004101180d10f00c11007400f4803c60003041005840404170b4002e0700c1d59281422480f03825141c211801c0c2c8100030300c46080020700c1c7d81010542d40030a0001041402036001424501c0b0350340100080c9a02c10300801050000c015001f14421482030400c1d55031482009503031103140c010a0301c8070304c40c0304141c0044d000a014030b41550000d2400041d5051038503081c94850400907840d1192480c10303009a03958100b407042d035105c4035481ca54090790168111000702c1c041c0d17840d12003040800b04010700840e2994049409036041e00307030540344584610440c0b42124060769107040a000251011401152040355818940c00c0c2040740912410b003400082640c00320356601290420700348014076495269180010400742d60720b000910180d1300903541c0600c0070341031000036030031a0206104803503417010030000350444a402060301182145890100904401d407801c405010b45032442c00203500a251442c0480c6d82c6664003581c90800c20b480c4002c200c01010701c6d80340c82 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 800628318 1250 800627068 800627071
    0xb0102070b04030f05071a070605010f03080a031d0609011a150304080f0403050a030309031b03082a0d050906070905060f09060c062403071401030b01020312090703030e09 75
    0x5a954008000a2000c078900d103e010481070700c1417048645242d03440658a80003600c0f1007158a00d03150014000e01801200d0281c00d01405200d9030362540c55145541d200c103544103504181c024151140090000a08282c201030b128034160001e48100d0710f4688400c034002e040d503d1019040344006150078907103040c485140c401c81c0203042c40d0f0500e19119074888240383d80241186449074181000301000103a010b10440f04064407986010646140b1881d01070802ca200e2452510090345a040c441c002c43e170b110a01540141c1071400241c80340e886400d80240308100b80100c0300c440c2200203043c900c209405d82c44031348112119010f0f05c0407921004c80c101d81444062003166070242c000c1c405990100200340040c81d86440c000d01c49841e00300400003441c181041100e048403600001200481072009d08030380070392040c50032809130000d9800d1021041c0740305000c003451410150382e60440c400990007002200e8110150000444d2246810500d056441d03086000490015054001a0302d86041c041440c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 800629568 1250 800628318 800628329
    0x10c0905130e0726010c09170c220b12100b0603092e0f2705030412050a0b0907080c01050403050a110a09020403061a010e100c02060d1e0b010207 64
    0x8040d0303140741c0481c2441091004000030203126040c041609860006d10030030104404a1301c40051041c5007000b001d808020f0647e81401940220010044580e0b07814801c0707803c800d90b14509180d0001d411008001400380e41c50480d000414000342945496001a100510340d4908400703000c800820400c1c4036803804152207010440d80102c0000e000503542c03101c203146142c94020315411f25401c00400c08107481020340c540c6091682c40030441d00340714034000c503000300c403805484240383e284065507040d681784118490400d40c121810001c1e420000c00340140800f4681100b0300e03500b24188076510684401d65840b50710381c14400e441004455501541c10764044079081009440001010b17202d92414a00302008140d010f0150040403800c40554809000614000c50000441d0341603001e802182ea128401b006051100341c20009075540c0e18140c0e00c4207028880e18005088107040c0c400f0030501c3c003071656404051401c105910031210319041000d50401d038111001d1045008039401a80c81e4000380c05107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 800630818 1250 800629568 800629573
    0x10081014070f09231c020a0503120d020309070324050f0c040306020a0908011505030606090108062802120f1f0512030c0d020105010e240909010e010c0905130e 70
    0xc006500d0402154000da140c0c09102c020380840713180c0094a429034060382c4814541903050710000350300b085201d00000d0001a002494401e40222500003d4010540c000001e01e03000070002d56074441c02d1100130011a800304100201441c1d40512940e9030230b40005000b81c40c1c0c40c203800500450280940c5901410301c018029184c18250744800d4065400192108140001d031100010103c009204107028580c4460a50000504050400d824040090070082c030034070030180144035650002c01d400c1e400c401c0304070200724011401d4142c402e400907492440c0b542d60780b0108054055807107000c5001d21a80c18610755103090340d10842d4100112500d00403002400503c88821701c4a07007450000c141402e44003000f2a0b0030540e90000d840d1829180c030034400c0060b511080100803100480d00c880e80c000c0500509007180d4412030442c041805040c3e4840c1e07100d08203840204625903001e50210761022901002400052030a5402404981c2584241c501806400b41c030710070303a92028890280441c480101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 800632068 1250 800630818 800630837
    0x708030a051b07030c29010b0415110c100c060e030d0501061b1106090a170c1f0302030a090b04062720040e030d0c090906060c0b10081014070f 63
    0x3d8900340c0c40c60050506c408030150501044c1c121b4206011203000317009070345505507914200400300d400e050f0b540c6c0042e418040101105103510002051031201130001b5a1112441007441c04126440003c4c0c00c800342032546029441541d4400110050084001540c1d0620250347e88100c1151550164284640700c240d8014003440050303602035500c081200000c0005040400000020b10079181950014044640c0c6002a5070103141c240329000311041c0c00c0381c80e0310f1403009828808001c1c11410040000f01030f070010004500752000d6102d00c01480e041800400249440d283c8a0010806038121602c41d0b184c0c9001d10240300a01005140348580c0318175044984801faa2040d9070b810748003180b059000b611000704ac61111020130241081c000c00c2c1030042041190540042c0090800350000b869990408405001c1c40c5d070014100c44a455000078050300541e01d20180c1307401505541c0203242c5030300a14110745c00058098024501030a142c51f40c030703009600c41c07902c10342e00c15401c1d4000801090f650103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 800633318 1250 800632068 800632073
    0x62c01060e060714010e0f0606150405010903080a03180b0702070f140105090d050d0206040c1508150a09060902090f1009060516062d051902070203030708030a051b07030c 75
    0xe00130721030f9103080000c40c41c000314841d0305003030091055000c140360f8069402c2100030324041080190b40d000070407020f80b600c1d003090002080700859010292030040c1c0081c0e114201d40c4280c1c07295045020b09030071803083c000d0901d0711030020b075030944110b801441000804a0041c405028110860b54011004180269054010741300c07500700e02c424a91156180d0b4a020204c0c2c0c1c2405174998804469000d41a9840c15250007111940c158000100c0d04820300c3e020410701e41c00c011515044461020305071300103200c6e00d000a6004840f50056030981e400d00d100040c0c10452078000c9c1c080710804480103015581c2c0c00c81030041310100c506a0700c0c000741102c2c2c003c202081c05400104070034014115110980d10454884d517080d039034444010b49000e00d203080b000690481d21007024004030788400702400581007103100050203054805038483d030a5400110740c0215074041089840c0151300c129619203c1c50040c1100000704802c1310000c41001d00c00c55920300c119041c5044400070f56041c2c84403108140e158 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 800634568 1250 800633318 800633333
    0x6050109120813030606050111061306051312120e0c0607020123121801020c0a0206030903041703042d030b0c040504090f0311011104090e01062c01060e0607 69
    0x1e49094960840c10400c80b42240000e0000703c000d14003500000c6400c51920b0001000703900c42001110180d08540c05000000c48150f41594040f0f030403840204068481203120010091f03075110051030700e890a80488c11450300b040700301c110302c1d007141d004101d00300103000c0070307600e0f03009401d41780d980003270100662001507000340e40800c401c03000c80e606036107003081d14480c400c8554401c5480841302d40c080020040390900c50310707a40c4000c41c0004025418920600c1c080da43d10404801c000b4800e0701c0100c00112050410002d0f50014021070603a480341c0c01d003504000b03480754024056001212251044040a010701481c40413103070301c0300c03141121914990744a240281401500c11455414200b00008981d592400741080d0720340500c9810000700541e1a01801c00340b02c5d8071782c42100d641040364074000c160300b00c1c0a0f241220611503001c101c481c0d20042080c0100740d2a00451442180001003840c84840c14800c8012102d15098003080769886081c20788900a06a0b07407260300035170030409100090801c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 800635818 1250 800634568 800634599
    0x3011a010f020a210507050a0807061a060306040c122f070507060e0a0e0702060a050108211c0c180b041a280e040605042711031f0b0406050109 63
    0x9894564148006e5654035410052421003d803043c000104100b424011782d48a82d00484e01090408040c841c41400822018000200020301c10396540c0100103500d03004034511124003144080c10042504110f00844c1d0071101c008442c182c2040c007084d058032524203441211800c68100d0001d1102c00e19162045445110400f615030704602501000a668060401c41900904168001c1c2c950380c036000d4500e104072201644641d401c1c0e80240c100107441640300041c80c8403a13030002c0109658000c0500c5c0c00120810203106802c090f46003100c0e60080c154800080ca5403c41280001c5182c0e680d9000702110a02580c02522020035442c1c150801e8030441000503c4808800384003c0c1c0501103a80c40c00ca0321001c00481c00c40441d00c55a2481501d144c07520941018140481d820040e0f0050307210424103c2c0c98441020002413400c040013010302180d10010713151440020308850703041c1c410032101d82002c1790f144400010103042100c503442c20315003805180705403101070b5a1510a186040f404e8114a0750303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 800637068 1250 800635818 800635883
    0x210150e10091a01120615030f4809050907110708060619080706180e070e090106080702060a0510050a030516080706080a02130503011a010f020a 64
    0xc01d4400003800c1c60207028569809080aa072100c0015a00c0005400240f0004814002c0c034501300c024041a1320702c4250040c0880c29250010f99405a51000700007031084402184450303111110b00c4d04d60301c819004014844944c00c2d028a80307003104110a8200c1c0542c080f00c00c1c0840e0100c10b047c080d41c204100c41d0369105070540b80811412898543d1b072810002a0b0f081060316404c03a404000036420f06203000d2581149900024101b14500180c0c9911203440e40101d0003000120b504810f9000140d0011002900782c0030011442801e1200014005a40513900107018502c81c4000003200c602a4414620076007658000c0e11a0740c8d94402194010900244000d50b101c1d0042c00100b0710391102040100a58800d10003800d43c60544150301854582c0c640c80524907500c446002e020f01e581c403529454120030320507005611129030481c108107900b5990409601903107040c3c1003042c0c0700c0ca05200f0b052035400a80350f8021172040b00d102240c55074462900038043e0300030100a000c1440d40d04801d41011036 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 800638318 1250 800637068 800637091
    0x30f07030b010c080a09050a080d021b0402190503010509010f03050a0312150f291c0612060504021203031b090f0a0e0a0b010e010c0605060a0302060c010c0210150e 72
    0x100035030701c51030981c05c1010090001398440b901440310741032041c4c505020740780384002401c068015403002503807903e01408114041c2c002c64541d80300d58407143c060f142035051a00401041d801c40c0d110007405070b0001d100302481003152000010b83d5000007500f440c10b4a8100016104608030340d24140c4200c006040301c0504580d45e40c0b0004059034042501802a104050101c0c8884d860480316141c200c0c4810900300d8510a851a174260310f441c00b900310344140c07001400e18008131007542003600040929902140448100307100c008100000383c0d101c03d2040b442150306421000406200b10740c2d9000880d1a2180209005003141102c204100038020a0f50018028642c464803100480c5d4504007d45c4a000016100301c00d01c00c0400d83c9000300d000c0000286800d0b601d0000010000b001034001d400007034a01551040400c455032148911071014503009080550707500300365480940200030103603138440140940c1000154013030960003550981800340650101003414908c0b000c0e0640806840d100000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 800639568 1250 800638318 800638337
    0x7150e042309030406020c03030a0f0804050a0b0a05062d01050903010b0a0806040b0114210f0a2004110706050c0d23060609151b030c0709060605030f07030b01 70
    0xc000786030584159150000345443c0d40c502a030184c940305181424501c06d400900207451100e900c0000c49280c104c0c1d903e06184280c42e5410f00c0b03801c18001e42c0700a02041c20300310410941f200c3d01d4006034041d45085d2040c00041507880c00f16060f904480c0070144070000c0d040008205580b00b400681101e003001000051421b00d4140080c1ca800b106a2194925400c40000c020038800c0207690140103010101c00c0d1044015550f00280e100081c030301c4400500c070941102c082d00440d0405c041030704107a4000c00c4400080380c07410112001319084208486525003025400018100741c0125050148041d0000342040c14595806024110051031400044014010351452100c2805070840a800b05400d072140340e0b0483d503400c01a40d5000300668040c0743d0401c001c0686850b850045a400140d280885031207049035801d400340c03412a512840070502c00400c000c0591600425020201d1307403444402c00280303956280035252400116808000e4034101b00c000b425142c0287c1055080280516108240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 800640818 1250 800639568 800639621
    0x20c01030f060f120201230f0f160327050a03080f07050601030b04061a0306070806030c0a08031201171e1906020a080a1a150c060408030907150e04 65
    0x2802100c4e030012009201001d108000e55070000c1503907000c10038886040e2900500c8a400851b07611071b8000c04100e052002a03c3c00c1032900400030360346a546840c0440d160510103003001031020b58080e81c0400202c520502203c29003a0010b0310404075070000e04030a80081c9141c0b1000b005410407242020112000c010210000304140070381c3d0b01039885420348200e142041e041071421074440142d6100182101c85480c05d9954000581550009092600620039521040405d0421084080d070940108550902054445000c00900b041061361812004a0780e80c1e84107a80c10140101c034100e040d5000400a004950008805460b410512000b15004d40e00c500381454019450010150741c402d60201e400c4142c035a01010107504100c102c00240100b0070950040112440c80220300e030700c07803c03080c030301900e480e0929010755606a050794199130300c500d814249042d00da40100e0b0f1244a0740039800001c00c007091507450703d8281d840f0300e580301c01c2101c100c2c00038000100600e4004a19680c0f000c0f02e920300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 800642068 1250 800640818 800640839
    0x70f0b0a2301152d120b01021204030f0609020324100b090603070207120f05060609151c02040e010c110d08010603052802090301140f0406020702011b050a12080403020c01030f06 78
    0x300159200d81c4a1107040d170401d0100c6e0050000e8074119044510b40501509254040d03c041e20740101410310a49201e14100700100700020009406010340e400f109590100c88030360007160134040c2060706c4150340d0b080520103000014020070700d09110511000203142011005994812490b004844610b516002c4441040e524801c3c00c40c0c1d0904e000406104202c41401195042041510542840c2c280080040409034003544001d0041c2640780f00c070f01590081d40340c21a0003d0700904204250080d28045074084c0941142d8540840c00d50a61074151000014402d2441519651590021b13400d00700c0480c050701c00501502c0d6460368281c2d1400d01001c0c3e00003110074140600000680e51810390043c03601b50340400c003865070403a110b03108002c0f0f5a0f002c0301c10f89034810fa10410043e581e01c5907100507204d51405880c01300c00001415018070030000c000414024040c001d0203400c122a8030008200c41d1114200d80041c0140c00003001032126500907085101100301c0781002056a070344030225001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 800643318 1250 800642068 800642147
    0x180f1103010905041a0127021318090813030218011202010302030a060b030a0609050106050a0c1103031c060303120209010c0f0311030708030a20040b070f0b0a230115 73
    0x40c00c81903910060b2001d0014440d0346d9044c08608400b503050021568003200520000d101c2c0c2510300c4900c860f2b85002d0b000c140d00044080c2d902000c0161143c61003c1c075220009141e000482c0548010000c3c82c02e1540c038005118100c680242d1341140581e21a0b0044003c1e401c050000001603440b0940404c007080441c0140d441800300a000044651501d250101552010f901190a104042088085040e07008040811281d00300c003001180c2c085039400b080ca9440b80c42c1000e1030105036030030501503203166074000c0000c40f40241e030780d1200c40080c43c030b00341c0c00c91040005150108840a2284001034010311210b10024043e040403890b66451801c414115440480201c0340e00000008001540a0a205101c0862400c14802113a00c5981c90340d4001442039000b044120768010504104204030000c0d070070f602d96401403030345000d42090042e20700500981641c51494080c085d1000e0401032060400c5d034102c950b1503800100a445002c000c2c1ea031721116000c01d0000d01098540011a0f00342484d030403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 800644568 1250 800643318 800643329
    0x3012c030702040906050f0a05060a090e0c0a06120c0f080406051803300c07170f040f150c050c04020d020c01050f1806150603070e0307180f1103010905041a01 70
    0x852180340c1f044660510780300c01042001d60304c0c80c2c0410301c00c164454500a40c240c1d171640c5030020b884000740c107101e032911486402880e840700f03007400041401d9600109070310354a114030205001240103814107450001e50301c0c21702c9000400e044009404035480d90001500011485882144510702a01309415680402710b11540d070001d195120079044003d000c41e202200201d428010142003003490b44400d841001d4025007810b5110724895064880141103420062918041c0c48e0b0f2107550f40070075040c0c0e00c01071054020381d04007900344102060040400c0426164020054030746564580d003000020340002d428103407095824030903058490024480c580c05046034210108007450001e40300600808110003d070082d40080b400d018a4242c4000c0f11a0b8405040700c0c419200e50356682c049400342c044400041c0d044c816807000041301d88800c0c0140c10854940c0c1014072000d0207141500060301c2d440c05044010f00350400040040605540c48544c0251203001b642130581400b00380006192401e0b0484c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 800645818 1250 800644568 800644571
    0x182d0d030605180108030f1b06040f151e020f300603030a02031801120207110a050a08060c07030c0503030c090f0d021806060d0e071403012c030702040906 68
    0x20b1140b850100c2565400d0703040440c2001c141d42c10041703d06e449000b10604000c0d241c0010030107200303024984241c40c0f8580c500b41c04079100d038075141c240030032110010034003960024a0200c01d840120890b000380e46603410280d88070044010803000003002035200d040e10440c04007043c020091807045074079000302da06540d22032600e80c10000b00c9414020480280555103e640104044185540c010050343e204071102d017a01c04600b01c071500180c54840e0507510030b5051501c009100401c101c0e54454001242006698440941780c035841804000d484a010787c03501580080d00027000d8001801c02454220701c24a0000f961038071940e51f15140d0341007603400d4010340f0700100f001002070525603207410301102c007110700e242d24419a402160a600300c1c0841c43c410507524500080c2c564a80404544680b42410300400c40b0050500103561184100c0c06074800024007040b80220324075050041c1c0c596040415021000c2d4203460a0f006d00000c141c00600c2c1d043d000a200c0b0b480560346c0e910600303a156005500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 800647068 1250 800645818 800645831
    0x21c050f010207050a020f0f1c0c0509070f3e10060e1b030115120902061603080c0301080d0c03090e0705180d050303060d0206121e182d0d03 62
    0x104203202041d0203070a40998244019040f4566071012088403510705414001600127080c10030a004000e10380106030000325100138480110fa00000a86041c42140d807040e00810103c44014003190700521400040c1e807140605240c02e00311b1a8070f10400b61030b500f04a0b00042040114181900c4440c1d0280c86002056010000700349800900c1d541c03000d0380000085e25660400709080c0c00c51440100320010000000509401500c0c00d6000d001071503001061161240c82c1c1d22024012000800800c13000200c0d0785010500300000310065a040c2c40c0c0c610054000100a09021070ba5003008400c2a010850307c04030001c0e580002284003401045642d541c00c2d6206d4a001d40d080d044016421040e018090078a00100425804070035240c20182c11550000d400843c0d00026801e030090301c18400ea01c44005041c484035045580b65203401d0b40004c802d183c82130346d13520114240e00409460748000c54000c03c0300101281022044504050701100501070300012158000b850101c5480d100c0011955a45 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 800648318 1250 800647068 800647073
    0xc0510090c0602060c040b03040201020c090c030a1808042d090204141c03050307090f0b0712020a030804030f0903050f0106140a0819020a0e0411011704021c050f010207050a 76
    0x200410050b000500040865007001c445900c80c5102c0c610855804160200c041000c681c800e11000e102c0c0f041c010901c001c142402c4804842c2c81d071042d20403c02d21440d10100303411402080072281542908420254109450314013483c04002209810241c00d184024021000c0b00681c1e0101c006003145801c0141c0b51070a004038500442d1410944a115400c0b040d200100c010012000405541d41850010380765214a402911090305e60307004803586081d0703844041640640320001e00081d134010710105003502d202180590702d52105450281c006075280c80000d001c00c1c0a01001c5650901d5850b040c510160343e51140c0e800c0c0000407400d6849a5102c0108000e604041c03000459402c0c4101d4511003c10700d0030b110356a0b155010024440b403100442c0c0500155a0b94180754002441311380c0d4000402c5c5011324001114217600c501280c046284280900050024000800c0c491603018069080842580e0b40380190f00d0b41c016000c4520303100f0302c400c045060000380064003034540701d4402813400761500d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 800649568 1250 800648318 800648333
    0x14090a0b0f01030b04110a050d031e080f07030b06090a080c0a0801020f09010305040203010b03010c05210c04120c080708214b040e060d030e010509010c051009 70
    0x1824542408800200600120751407402c13054005074091041d524003001c040c0851111b03802039005d6035000c0401040741d0245500701c01164001c60080607540c00080084a080d1403040007030f13900c00200302d42c05c000201120b0180c1d21107030850400811203070a010302d460008000051070f8111403040d8108031080383c02400d1441000c800303003180707034000e5042c90ba440446403101c0c0030322004c4604058407400441d00b9074900790b2005050001c060001c5c02803a1401c1000340459000d00c0c519503040c1c410a03001113041c034000c081c0e9400744280c051401c0ca8180b608105c0d140905101c036050b00ea160f04c10100003620b200030090440140051800342c12040e0001545000c00f00c0210203460481c01c0c100030402c0715020280c60b09600e1f20400380445a500c64140c00100e4608800944110b0b100d086207000e00756443c504082c0c01200c2c600402a0410b507245003e001581d00385000003408911004007129466024a01074141140185841407540306161100c44c85d044140d041d500d80580d85440a400348a40c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 800650818 1250 800649568 800649571
    0x30f061121091c0e0f0a0801051603020a02100c05220501030b0a0302150a140a0c020a061b030e190b03041101020d0c20130e0105011208071514090a0b 66
    0x96030080c24043c03030006408001e00414581a41c1040905070442c4400c0c1e960180300303880c015001d0302001d2115112a45a80289005d0b945080b005e042c9001160347e07180f02c1d0085402c02e00d0140d02030140c0c5c4942e04e09042c0540b000700300030b00603c4030510114460204229009000d0300000300940c404624060001d022501c03c07a1905005030341c041400d001585444480c00c40300062083c1aa5440c001c074442111442c42072580015680000551048103903030101604040900803500c1d9180c00e6551101a500c440c0000c903111294542c2d6180c0350301190042542001d0014050b1808401c03003000e4411400e000616001290b4105000c0180000d00035a180c001043d58001c1c002004000c00c1c5040181004c0310704030005010f00d0804405420750803140c030b180c104064019015454041c114441e11015000c064105c032029882c003000058410b03c4141640c0b001904a0206407922107a6143c8914250541200d552190b48841640e80001c1c86402210300c9100c03603102074800d020082c500714650131030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 800652068 1250 800650818 800650831
    0x6011b050d14091207061407020901140316030f05060f070206131b0605040911030f0a0908120103080d0f290604150513081b1c050d0203130f0b04030f061121 69
    0xa0508c4a14016290044030a0558807001c0000c1150400180040e183c4540048200c42c50303440080c0020402c80d800c00c114074154401c0080d18481c3c1c0c2d8410241c003070701004440c0800140d01a501142c224060030300c18040082c01220b249414211003182c0c69144002544124006200010104907000741482201d20202108191f10320718100710303d01e880410800f42c16004502daa60304000304214400c1d00316040030039441c0b0318030000d6a4a040403442d0340c11a441c0c2d00045030501c0840c00d481e041701d01c503003101d82810380e85d2040707055030701022642921000d0b00e0064010f04200030104103c507044410151008403581d0b01c540e501180c1602c962100c03c90b80c06800c0701d9021150152042c080038001c511003001c140d4840088545c01480c0051041c1035003006130150041105281d94139074048028101c030982c40c0b0700d40340300c0e59a400002d035580d2610321807071a49800c28041400081c20814034054807600640c000300d1200c04200c1c007003519a2004001c545106c42c8480c031241c003041100107a6a0007035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 800653318 1250 800652068 800652107
    0xf0209011509150e100c020d21080631150612020301050a0303052115010f1b060507230a030b0103021633020306011b050d1409120706 59
    0x5840070015000d44c00d40705060b07100c0c0c213101e04140300c00c500c65580d90b11240c1c0c00a10800e409915800d040c021611031005681c0d00682810b03250b00154001d60405020b0700020304208007004240b000b040a04120621100c814001c0700c66801c0510316500032146038016140d8420005480c108002d021564a21100302c034050041c801003103a42ea8000400e03017201d03014103255950f00b4000069100180500100001c48584030090202401c254072041002c01c1080c1c0742e0a030341d400b1301d1006a50003104884010713100c2d41d44045007000120607422240c0c1001c698103010300c43c00c5018001c0315401c5101c00105104007800300ea41d03a402581400740c003840c0d407002e00b02107103010092510413100d040e451002511443d03090145030300c1c00d000c250841c0094245400340349045280798846901940c016900795000071460441200f09a071819404082d40c1d03808402846282c038070b203070107440c1c80b04660303988105004188205100307603d07081c0440c00c44c50032030f40c0034021460906101a19a8200c00c8500140e81c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 800654568 1250 800653318 800653349
    0x813060603052508120304170c07051c0f112407051005070e221e0b090f160207050907110d080601050d18060920060306010909090f0209011509 63
    0x140d011a80c41c0e0007407a580c07803c0303546c0c0d030743c90030301d140d4048400503807900100340020491085032000ca08403060b21022120000c545c8945003419418090105014103450103030900c2d140002d207500740040101c032029119041c4051051200d8030720000c0c844120580700c0d00050340c942005402e00c0f42d50600300d44000100001d08100e50020034203c1d1103043ca5010b941301d00342007000d0250060300e0395045503c0314000d00c0002902d5403d000718a44440c40d01b0301c4541000345501c5c452030700d821124458803501580700c180344d5500501d495030002d80a261802e50140c140042107540701c00c42200d104031a2a140d280c1040e107010229403501548001c15803c0080000510402e6039010040300c000980008001ca01198030802007140c0b46902140200038610380360b00e000c100096a14003031400b0f9031101c51410764080d90010300003244022201d050015001c00070a108030b0340c440c1d001028042c000c003803000e503030b040c240d0104081e80003e0300b05041c504444112144c803a40d001004001030030080d0801c0004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 800655818 1250 800654568 800654579
    0x6121811010e1201020c21190c0606050402210a1505010f02070f38030a1a130203090f0a051e160b070c0e090a0308130606030525 57
    0x500103009031803410051031289608040c2d0380c2900c00769810003040021540c404a40d50f00c1a5912580707600091041c007240a9a00c94407443c4003510100f44c1d1400d080380700d45144020440e00800040821107100780e035050b001c00c40b80c42cbc510103010000b94403203170b002c1c040007402c06000f070b0403900411030006030342040c10000454610b500041c0c100c807401c6c2030105400075072010903400c02c10349400102482c110140c0000d20416117aa0418000d044050f00101148030300b03407107001888003056074420f0080204041041e0008c503503c815100b10f60001031205c070710039450000340d080c00c41d81c0315416010303004002d00481f55418030403210544c140c1401801000e816a403a01d440d0510483c0156410320007106000302c0c03c5040c41248196081800480c198580310303010a61203421011080e1070612039050302140395409520543c1c0204d41f104000c201030001940c0495401c2402021861800707050318004d00029030724061003001d18800c001900b000b8002014151949410340314040c1c122203174800c200171 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 800657068 1250 800655818 800655833
    0x40b041502090f06130306050c2802300a0e0307050102031804090609050307050f061005011d010e270c0a0903060c3615021222061218 59
    0x100d40b601660398507144c810380b000d248171904050380042c000c54107050801c200004002e0081c0604040c2d00112148100307400112a0041a081c82e43e60142c1d100790014495070807000c03803240d41c43c4043c2415000903003401415086035004185680301051000305441e040e45800c0c0100409000c003840103500340180716100380ba03400314019517a0b000c0c0b940c44d01c0203800d01c142c0b50030100e00590440100c3e0380e20780a6180c46590f0311500b540c5c0c440280901c801286552150f802c03e141101c00503540c6503601e018040d01c8031540301c140c41e50a0305103c011050040c0c4c13034841d00d15100d110000c611500e680030124103103590700110000c00104900c4c0341007001308135864001202e40c041d69045640010214080881600c0519031f523034404000d1035085404501803c00492815540300300700c00da5070401903950603480145443c0c0e803459400740c2c03c509501c6552a111502410b00102820a000d070000030050301c0300c03240c0e0916005200001c442e070a200400b0f4015020300840c000394644400d40c0140192100728 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 800658318 1250 800657068 800657089
    0xa0507150b1507020a0302180907060e010e0402031e07030b130204241115041a240d0210111203010f0521010e070f290306060c06040b04150209 63
    0x103802c0700c40842c500042d5162802c3c100301540e4080e1107401031440a000f820031420b812141e104003446260000f00b0b0140c0316204228902006849000c444c1100404200c00707500003d10b0306030401c41405c0c0310f011004920b000c15000300c01e19100040d8420f03461085c000710710414507154024070f00400003000000100300400c1014503c4002550301c3c07441a0300c00700ca00400341d14000b04244500496881d16848501501e40124840d18808060588000c00c040c20384404850801d0b50100606801d00e480c40c0301040310310400d00090160b41c00a0403980081c50342007030852240d000441810070b03a0596601080a80750915498400e2402e40d03140c030010f081200c0b138030b006260150000d9500c0e04600c64030030f51000d05407904040240012009000d06a0f612100c501c01c00b2034412070441e0000d62090100c000e5403070000035054111030344000c2d50112405a001904c1030703410010030401442038440511a1a00441c070641e9480b405003800d0821540e850011101c4041c218810440c1d5032040d03590702082d2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 800659568 1250 800658318 800658349
    0x190216030e122d0f0102030a0219170a0b030c1302071419020d0618060b0a05010516020d081306020c01020d0306141e0a0608041e0302060c0313080a0507150b 69
    0x2005404085015103080105401c00f1321141d600201c117100110415402400a4030a4800d042d50307403c0d11660101c507400f45a01d02c40f00f0000c03a0341c0108940254641040051420181c100c0da054030002c000304514801c2210316601865000c40c0c04020480c12141541c006012035008200c1c021190141c082185a41d15009101c0c911030043c15041102e41e8000700e05424800e54012490100703824904043d180c1240028811020341402007000d41c081c05c191140c60f0030050315421110803a40c203110700b0740400c001c01c0e10f10900600400301c0c1c1040581c1004050400e07903002d0145400201c002925000c4100e51003400e05081c034009110501d00400d018001420071900d21030b195000e4150617030b000308039001c05500510380d500042680b6400c03684182c0298400c070342c0030012a000d010450f8219400303220041c01600f1207004903c0300b10b4980d004d141c00452003d10300140c0300c11655404641d42c00400c1c9900400d401003201e406001404107401941403003000240621701c03540c1c001030914082041c0c41d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 800660818 1250 800659568 800659633
    0x30c0a11011b0513060c020330070809010f02030a0504330216052218021306050f04060503031b030d020d090b060405010e130c0f0602010b1201090506190216030e12 72
    0x408854114441c048501e6032540707822709548600d2804d000180342c0c0070044590116002526007034203944000112201818255101401d143c100a03864424000c0e100b01c08800103100752401d612581000b10700711500318260001c000381040c0d50012203102c0003680c442c0d84100d101c6942180001d1040d50a14000034005c1030014142070303051145c02485400c440c01940040c0e441c031054180c1c0b074880e8002001d0712411135411824121010400040c1e03107607806500d400d0f41051090540b61145580c00507054100f440a6a042c01c110b1203c110032078110310300394118951202414418480855400d40e0849800da409115135810240080c00071a40034119807038036003180c0b5802c0f0522032100c00c0200944030003440d02184035641c00c002406400340c0250b031407184110030f071a211484014031640b001030350312501130641643c4000100d070002c500707030064040740c0e40c003002101c1c55400d414100b000b290b40309496114200356080c06001100c0400e80d0461a80c0d400400d0901800310f145085001c0f1000e54030703d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 800662068 1250 800660818 800660863
    0xe1803030403050919030506150904380405011401090b0307050f0a030803040c0501080c04030b011202040906090b07080c270105040f080606040b0402030c0a11011b0513060c0203 78
    0x22400e17864003048a98500031000002000f00040491924001d00e214031103210816218400c00000280c03d0780c006140011600f00ea80001078801e504812540404400184500e04098000c2c0800700854003200c0d107035950410120316120910031280903140c2d003241004070700c80910210344c2d101d880d030003440d100b10b860b0b40c204c050640c1c500890f203000d164000c070805d4403824140b62a4104072641c2c000c482c0419071000003d000c803901c107000d40301200d40140b811401a4684224a50500300b9140166001515815036801203005405000080c40c411140d01c0035a1618842c001c1c0800009004a60b6694007044046d4000d40910b0000903000081c50090b003481a2500059510f8480c50b441003583c008a080001031154002c12842c0c0304040640e070510400d10254200002c80c40112513a00c20010144a0444d00521401080a00c940c20800000b0781c2011448074440046038418060000350f03001a00c00c001c61641d152841c020300c80e50800c80009011903001a80710f0441d4107128820300420003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 800663318 1250 800662068 800662087
    0xc0709291201062705010e060a14040f090b040308101401050f0c01060618050306040308010636060e0913080a17010608040308070905030d03090f06050703060e180303040305 76
    0x14840f4000b48403a03400300700f00f0b080501e00d002203100c040742910f05003490302c0e000040c01104020b04a209010003400d4089807400c00b030003035000180b0008865081552025402c0600c0058452440d45601407505113100d0714091800401082c03009000f290000b010110402503001420340c0005518400d00380320792109041a0f440a143c000d508800d1859820400001140364012620700959400b030211f400c0c031203032107001341070f80c490040e2002400100c40a004122031407241d441c44016140b0320b42c0d0711242c10102c079540c1d07290180d4fc0d0602c003041c0c1d404680402861741c1290403034150403410380d9190003501e00740b0703051b107040009490081c101c500002150035458bc0b00e0034042810450820783c0c030146584892004213610011281140407940d42804904c8160140702050125031000780241072803044000304902416482c4000c03a0328041000d0214001607181c05102e00c40c00c00c0d5600020b51500d000600082030714042e1100007050084012840c5000001c8210396000390541003455a454240 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 800664568 1250 800663318 800663321
    0xb0d05030904020c032a07241b0f0b0a0f09020901120c0e010b030403030b040b0d140f0f0303090c0913020103020906040b0703030e06070f0203190e03030c0709291201 73
    0x15480e10483c0700794603400783c1c510806c50065099008000c04840303400b44c540c40e905002d00807400200081c3c980c0403910000040c03003188906510303a6010204090a0f84a07a102000394010010884050302c1d1901040100005840f50301507403004c0728018429540349401240b22080180500110042c0121041080c4180c2c03544802c001c100b141c41406040d03075610b1aa907aa50810b560880c0042d00341000f240752490310740138070810712400074404010f243e15a642e0544a407140030500b02d141c011180c0290580805101c0205850000b40c0a156649485000342d0b00341551007200728072a4031070005219101ca00145001d001d00ea080c01e006944211800014046021780d61041c03603101c0c1c0000e2404101076040c0c009212030b003180d41c11681c080d03c800c04103a0310680c0014045005a00c10f0080d4007201d048010840c5a500560030000809032200c000300c2d085a0180500d604517620050b0304100c3e0480314403503045295506090480001c800b841d0450680a08208651082082112801071588203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 800665818 1250 800664568 800664577
    0x904020910020105010306110705100c120207110f09090712050709050420060c03091507020a0e0118140c0901030b041a03010b060f12071404030f060b0d05030904020c03 74
    0x80001e240d4400112009002c0d10742400304950640c100000c41100340030b02e0058804099101000c1d01c0d00c048942500e40040c0041045042040b00700c00704001240010302c0280001800b40314907482d1002100103102c00e81d10078060b84d0b4014440c4400300100d001004c40d0110980b00d500300300280000d0541400da140490350b4000d01e102514000500c020000849200d0b056084940c107500400c0c16079504001150047d45590748103904100043e0301c59240001c0700001003004403c00501b440740c580c000c604d0015168000205003040c840050001400070409041c4a01403100c1c20b110100c070a00e004110102c000c0c1101c0300321100460814140e80c000d8001410080300a0010085184142c41b0001481045a041c600a510380410b40c01305050a0b0115480003100e503040a1900d10040c4c00740a00303500003055007003000100c065940340e02d001c8000420066000d00341540022440c0d00740241144e2000d800d40780b20303c0114000c000020808015241e81c2c2504a17801030725252000980e5007184503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 800667068 1250 800665818 800665837
    0xc06070f031e03050601080a0b06030705130803032a0721110d02010605040c020609300409050406051f0513023108070b03060f0f04050a0501060201050702030f0f090402 74
    0x40030895480700c5900d0b52104d803089070240e842000360f071036200003201101d0b84d2441d4a44c024004000186029020380010004400141440100103a0302d108141c150b403c1592482c100c0e4442d111302a58222541b81d00c1c04030b085030822814a407007055a1841500f0042c0c2001d07201c4201c1071000008028000c0c1c50400b4440c0c895419a280c0180780040207000340418003a00c1d10891504002c80e10103440020860f1007190b91100500380150b002d504903039562a0b0554076071103d440c140414001260350000341005004000001c200c50506140030819140000d003600404d03004040100400003a0041800c00c03247c041d1070380741d020340300038000304060b10644016120100410191009072008041d01c00e408110160b0030008171074560500035140c8041c1d104460200c60f060001c0b6a051610586054a01000070301030304110802d1004102034500c120750000040f0f0b40c4ea00100081e82e020700806603c00c140d0f1025518004c007400c042405809943d40080c9000b0010422a0042d150390b03040f01c40190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 800668318 1250 800667068 800667107
    0x212010207060e070602011e020c1c0507061404050607030b120111030402090a0528020913020c0d081e060a0e28020405131e180302010501080c06070f03 67
    0x2429424103401503c0420202c042921031a03000148403403061007211040340c4e540504101c0c44041f403005030044c1d004842c824559010f150305424844004200d0144144c1c015121640ca60741c8600307000c821190100401c4002d000148200300001e03501040c015840402c504002032002d210030080307030a00c80203801508266103000f06140d081504040030790f2040c1d2007214640d0441d9561031180c01541c80c15140402d070450381340400f881007540803601400b078000700c400050a2208144c00141d410000166028090f80e002030140301c500000d12440b013181c0703120300701110203007000300101200030740d07010b0144020600300c03001c02da4590740c0305003000003842c0079014450036050480f1082d42d02c00e107651800c08038840102107a02d080c000da0080c0c070708071003006148030221042844860090000303021840f241041e11810800080c000e8814517030032040040102c0ca00c9405441c0c01380c216101a0065583c40d8482d42080105a5601003211f842d10382c08031805121b2403007441c00385d07101914445103c0050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 800669568 1250 800668318 800668327
    0x6070f0e012f07080c040606020604030507050114191d030f1b010e0f07080d120e012c07230607051002030702030a030507050a080c0a0c080f090307060504080c040902120102 76
    0x145000109002036841c04130544120310403071400c02089880520a940140e0040d20000380401d0090014124284c091000441c803500302c0e940e9204007000407540100e000175882030000300541c5e07034401c00b207034140c4601c10144194204d4400650b41d000d807850300c5414600020b007030b5800a005500068020041d213009001101c140510141c980401c0d4083e040c031403040f0540003410369000034030100c1804050f11080080318903200d000014142e40c010405c0a5926400c4c82050515041521000110000056a54401401c400c50b0030400540e00c014040d42109406412145060b600740c90003500440d02c140d030340c2480b403070b0881c20264020510070000e8404800c000036103030007100501d0030f4180c0d980c0404c0b00b5500c0000c11381d0280164141d80c0009129180011400114200102010207050405032020070030307a9a01c08159001c20804182130f000801c00084900b41040008043c0c031240c1440360926040220b1565200381c1c4140c031901c22900d801d0303c6801d5481e803042c00e5892034110300083d9501d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 800670818 1250 800669568 800669657
    0x100302060c0309090c030712050601051204030206041202010b0f060c01090b01030f0605060103110a08090f0d05070b070c0f11150301080115050301020a0c140c06130806070f0e01 78
    0x180d0b0089240513024540443c0040d0a9401d603000301d078810402038541640708480341d03007524004d110040080e4180441000103203202c500d40c002091080303100380d0040640d840c09203840390000312118045419a810402c0c0089540e80b0b001000c4110007040c2c1360a5100c0c940c00381d070300e405003a28070320140401c01007400110034031103150200540c26000702424825922844011001c40300313002035880300d8030410310884200c144a40d5071503401500c2c00d400c40303440d446045280d9040c2044a00100d01203100080e0310410000c03030104482d4041e42b241400840c443c030503140d1001e80342d0031140052000d410442003a01c01d40e0303940140c401d101c150300c0d03016840350784030740c0038038000e00001c1060940e407107111100050510b014000c80740d045204d5070300d40115408540d038180613021034142d44441c900880042c80c1d115140c10010b0862742c100001c41003051072138404002d0070076501800c203902300501040703a2040c00384c01c0305480026880c2880c1040c0340701004c0760701000c64500d041c403469108842ca005d6404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 800672068 1250 800670818 800670823
    0x30060b0a0306050306040f023d020705091b03041a04030e01080f01051f0e09040602131a030711031315091d0103020d03020307060f05180a0b0f100302060c 68
    0x38098000c0d2000c00145482e10209540c442d000c6400605088940c2d0b2682c0041c181146c85a010080e86030300c10408520800800b0407414803200705101918600c00304104203a41084114010181621a0401c0e810622849107004c00340e000200c0744904000045410070040c50303103004403215034191402503030410380f50083c510882c101c10180000d88444c0851030300032040e510390741240e20050403a40d501072280e1001c0402400960740e64140302d0a4000004240c948e0094144294440d01e00140d0b01c1510010354900c4002c650000e00b40c0c00080e417402d507620381e40041101d400c05a2411f01d089078150a1401d41e203580f003008118852829021000200040844140c080145031030700c50920761511031081d80704110301400d0031428110b43d03000400150406010f00303100300c0c0c02132060f64a481c00585075081030310300c201480c600032a92103080055004902c1e84910a44110318041c140700402503d4002c0301c2d010160041d074904940704081804000380004502c001c0d50f0107800c9a880b007214030360954 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 800673318 1250 800672068 800672077
    0x6060d1401030c170604031409030703080702040c0807020c091b0a02070e13030e04020c12030c03040c1a0d1d0d080912040f12061e0209040c02060730060b 68
    0x141c0c880c0790f1410108445100780036445024100070000c218503a101c0d01c00f114100710b08086001001c07001c0141548070f844c24481000035600504c400e584d2603c0c24410310003141c40c1007003840c041110b07440511002540c0400d655124140850f80a4940d4440341d10b009041d07a01c100440716080d0000607410720042d0003050080444d200c5850306003041d9100e0780440c58009080c40d00500046021607600810303d010b03405012074012074401c4440709102030540b45074a92090712030000c00d6102200300400c000f09540d071107016004ca07825651516420854160b1540600f51080c3c1c00103440321802559101071090038005490703035038121040e07146036940142c0621b2064408900c80d01502e1050b1010001c42c81c120b5040391144a5070062091030310325490021301c4051401c0758110f889264070311050542d00c2450b00b10048003000160380f40b41c0034040008640d0740024010079074222800f00035810b038000c2c0c2c0b810071805201d010304602e01e122814100c40c164031400d40620310ba14000000c501d00080c07038082c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 800674568 1250 800673318 800673323
    0x60d110418030e0f010e03030708070501020c060408300c1e18040b030604030807050d060f0f05040507030e030a0e031002070c0305060c04140f06070204050a0f140105060901050306060d140103 84
    0x1440d0740c40b081300116030f04000c000b0b0031038060380200003503c00070308848010070125000d08001800d100600070110b0400302d0030307101680c1c41080400e288101e4100c0d14414020803440008080d1940b140382c0c0d55204000d030040c110109408003184007410f0780700c644024140303545080340e01590351407900c900d80b009041000429000e5460010a010a420000388040c02160152038841103692529400c0f51241c1c80150500001a12841c0c0001c4601c0420441d04c06031188402e02c800490400081c00200c60b002405002054281080c1040360203020045412014403444c103543c0610f9103201003440c2880034600600490301c000780d1081170100d90903511050341e100b6401c1e1120380d2a00003a080302c034062402001100c05540301262198a0a41070044444a028189074240350654001400300c0c4d20481e160142a9160030f01c3c011240f001c1e20032090b0f039010035a100e00303540d41004081003042c011000c009050240000c080b034070035554041925a0350322000340501041c20007640606c92041d080c8402c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 800675818 1250 800674568 800674579
    0x30c1e0606092f1b030409020a30050604090f0b04060c0203071a0414060403020d09090c1d060702060315090a29060c010c020102190503060d110418030e 67
    0x20000d43c05209005942c080380e001c4000b203007490401e4868a035074401003200080400c510340004a81400303001500080c481c0c13110040e1142512003015104aa0140102e040000e0000c12030f1420305026400e0154503e40c800d00041d2682c54078041001840c41400151091a0321900481000b00007001284030b07600c07510382840070040c80c00040e656809042c600a00b00c107451801f00e060204100c03015507000717000d0705040365102e0f500b207215802c0100c141d03002c0c1c00513002031414045032500210840020305095034200007802040b64000c006500600d2014121030180780140e04642d102415a8010b039001800c950b40d03801d140c500711010704201c852160280e03401d500001c80010042c4510048062010101c00d03070411096400c03010030300300b442d0807640580300f8407900710351020074480c046510343c8580005954000c20501d6400c00180124110100302040040000c00d8550181c120708985c0e1004000c80440d543c5800600600f0009803c420800d0451000ca014954460840320301102c00366003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 800677068 1250 800675818 800675831
    0xf1306021c0e10020322050109021c03030b0a0f03060b0303040914070206071704020d15020a090e0604020c0c060c0f160519030b0c07030c0606030c030516080703030c1e060609 77
    0x1101c205174041180c0182038550340005903201000c4440f03941c0c1c00d0130b118900000b0508916130000740d60401007407201213007240b00c1c1400010141c051003541071400e030813900248101d1818180421071a0700c0d000c01400f150702ca03040f6503166141007064801a001d10081070208114800740e50b014004122480d00051140b40003241109000f00c020706040401c5521040c06a61507400340200305071003040c116207100740ba1511b946172201500c040c0030010304585e40c2e070101c5071810030744004c010005086d0f1803060344100800c070600500007990141040c0300340c1d44588c07074041610302c190503c401610022498001d21242e51103042c0340c40310036400d40e5022115504000348408224045866a005c010071508984010603440d04890b009040103520904d001050201c0700d5075903000361340f240e9204440300c40303140c2021f0040000900095011001d00d41080d00100d26081800e1381d00d07161840003170107010b0700140c0e080500c4602183c4608101000100c00c9201d4454a4100001c000e50312a80300d01760719104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 800678318 1250 800677068 800677093
    0x80f070b0f07020907020a020405150406061707030b0d06090804330e0a05030f0c1f0f0e0607080a0809250504051005030a0302100b090f1306021c0e 65
    0x25907041d407446200c101c0c1010215402e100d628480940500103602c074075003800b0011382d2640a068494204000f00c840540c50340302c248400e8a440350401c07820700c040d00181c0c0c06090320701070010340d00940900d8081036102003003005c9000745940403405003c10f41010400c0702413081d0140180111280c6020190f0391040d210b015a600d240301e0480c1000c82604039246110f514441c140b108400074005045001090f03807000080d01d00340f05c00100c0340300b903001815903040d603152030815840c03418402c03102c85445040c5440010504e01c0c3d0300e4040020701940704440b10032a00c0b481300303a55040798007002e44d6554140d0003501500c0100101c0d2040901d11a0030700c80e4002c0c4580e00c40351222901546182101d19060030100005040c0052a610054403600310001d415074042010080140c002c0d00582316464032a0b0501c400c1c2d42d210b1003a14024219001070021107080031104d0b5a11044010304034224144034588140030340f04d055602c00b00801c81c8490303000e1848040c1d001c00310035000d1000715001005100c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 800679568 1250 800678318 800678339
    0xd0507030b010b0903100b06210609010f050306160315031b080d050f070f05121305030304050a05220509030d050115050304141f050604050f04110105071b080f07 71
    0x9040954250300600c01c48949a0750700d80040245c201d00511460801444204685050404403034003420000c10300309100c8541422f2481c1801350a501840181240c20407010a60b600d5020f84040f101600f4a9039401d0f245101e5841038000300360b111b141a03405030b0b890600007130b1044401e1150443c2c0c0c8140400013045900000c0e0f203410b003056501c81c0303824508601804d400d1900402429141c1c820b00c440c05ca0f000910910100c0e041d00000340c6a1612060410503000c1c017a07500360002406548100300078841c580d43d0400c1101124021207170b02074001d090f29a13403400d0121427500ca800f501d0514060010841001c400b4040315070b00c81034104020703aa9a0641543e03447d80d081d0305004103a0800200700412a040a0b401108010f2001c80b80030109242c00b0a8001d1203182c0c40964480c1c0d24014884540303410300800d074001c106100518000c3c10301761204032140c103039254054188440010b085042004903041c1c1004605111040b2250b25940c9081c0703901e403108071071045c0d6030f0f00460300d000c59405103c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 800680818 1250 800679568 800679577
    0x3051c0206070c08070b0c13140901150e120d0311072d05060a05150603071d03190807050106080a0f03030f0212090c0a0603110304080304030507020d0507030b010b 72
    0x180d008000c0381d10303000c1c03094615119500c0306907003280c401c02081021401440b130090142403246102650740021050440301c3c4032243d0000c50b00c3c8000d0038102011590b411007400c0c10b40e110310600070141038901c5820749507142c051503099002000000c15a50b0000c0104188902c494030340c6003800031140b444200c203035511400d0f03002032107030800c1c0b81c1c00c070100b94031141100b0782410f440210a44403090358690a00d42071040300c0810246844908006600d0030000703903128240401d59100d421402c0c600f2010f0841824000800040700890065444aa4040141c90f800c040b5042c00035010b03440324244130741030364490442600d0715824903e00040c0d10100040540706e194112112144520035a941200580302040012103265020300605880c80d081900c564041d03d03040c002000941030f0300080c00000b49440d808071090600e00320016611411400407a64031a52080c50140c0c1c0340d0300e915059940b8000d480c0040d4020490450b03840802c880002c1407000d49003e139260140e980c0e0b80700200003c9114 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 800682068 1250 800680818 800680873
    0x50106030507030b0618041137020d0e0f0d0b06040b030c1302030606071e0b071e03020c010207080406170c0702060901030905070b0a090f0e06031e071d010305 70
    0xb4100310450224542c1d061074070401b1401040070601e102411645807454101840c100c807442d10964034411074140032076552900308506142e00b9009180590040d498071224410081030203019421014a41c0e100303201c1083c40f1200a2100750000503e040c80d1010000c11216180140d1419200c04100e10f4002001d0080d110024818680000c3c03006200f4065040a0704035500280144940f00000d030070510000d00c0e0b048403049074290f101450901c0489608081e011500788016403140c040b1703c030801c06481d4100000c6081c0542d468a24644403030080c441c00c8400390022201041c041845039000c400803402403081400e403080342c2c40d0040c1c9040d0601c20300fa030081d03200d441001411150350203500046a118005c1c0190341c91941d0b139994050b000c1d40000072000008148410501c02c80c003101c060385000e4400039818a0f0245400e00c0403a03501e01800c01c00e0840c94049010511001c042041000701038541c0c2000e2944566511100030000364084c04102d445000d6012a88000401010600340c20798 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 800683318 1250 800682068 800682079
    0x1508010902030727050c3018070b040e0711010e19020f1020011104050d080c070303031e0203041713030206270307030825060e01050106030507030b 65
    0x5142000130607541d80510003c441d040010000044000d0051044520481040000b15a11070003113440d88404111013804c404042108419098162200d0444540c055040c0e410100c42e034414a400f10300d000720fa903024500c1c00800007804108110f81205c070300c0c000c11140d105c5098580700108814240c3d01052941110b9611014260048140b0701c102151001d0000d059040190780100104014071000c803c0031300420820030f070305450f101d1609032407038030002c68000811030044082ca80146520661003206e110702e000b1081d07241440282012290101400340c21126810303600d02c1c1c0a40a840401c04c0440880c80d1028035070640c100c9030003201e110f2035001d2098025001503440103081a0800e0395025160314400d540480140c40b4600281201d1400203180c000001d02d82707541c1189042080700c0e0070b00a410007101040010311440540c5c044545608820440e40284003000300d4010340035030041d1115082944038144d0000c1984000c0c1610500c0e58148030b80d6645140607402d0700e48941e84140c008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 800684568 1250 800683318 800683333
    0x40305030f0711060d060e0c070201090902071109040b010f3c09061e090c0c0609021816020c120304050d17070c1502010b0a030204050612030d150801090203 69
    0x41c1400108800c511403d0384814070010072000c18410741190340403400700e6583c0d00301031040c440040c00320340c0d020040450651410071641d000803c181c420f403150310b84035500480e42408010700164212090540904000214506420041c48104c02881804030307151100801150703000130344c18612290100c1d03414103103868840e9280d240d01540c003a02001c141c00c0341141d0109220b0b01a010b854020004a800c0342012181061404042601544041c22440ca000e021000c0aa000849031004039004900010304052034004142039040e0741c2d03002c0e0714499540082240b0040740f0101c0e2170310100268210b8240f040240107014200c0c3e070800c0c003910f00354018001007266240c640c0325002d449200d031031480080d10071400f08003c1c54001c1401182c4054191100340641c180c0b2803410600c10080d40b000340700d1901c100f800325170310101d540400781c0036541b00d900098050710789100005801100c030044030341c2c0d001c8000040008000c0d0002500c01c14560ad40f002a041c0d10500401b080c00d13030000c0250980 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 800685818 1250 800684568 800684587
    0x6042c0a0b100f0b070201210e0607080a202d0d0207141501030b071b05010c0207050634050312010f05190509070302071b08060c04030503 61
    0x211040001050892040c2051000019840310400c0d01880c030345401000c410b428451000780030300c400c1d000345144210900000c40940c2c0c0c040d83c29410a2500441d030f000f00c1071110422405003a80041c082018032486040c000c040781d000703480ca8410f00e404803080020602c0401d99100d0341500550b01c201c90041402442030b441c45411080c0e1840015072000444401c1a90304450035400c001110b07605264081481030070f001e030820191441d0b40803500a0643c1ea2524210112640ba041c04050700c501d000c180050314090240501403540b062140126104081c0c0740340090203040001c0005c0e005000d0b800001074281044025101c84110700884c1c4440c031070400e402007144542d480d4850000d2421040364401084051009003544210b01170f41100c2036041000c05000c044899110038062481d0748141c50001040382c1c045020360303a048480342d03c90f841c1e07240100c0190040d080c024104011900003030f40c3e03c0281c0b000f0002140d066038241c950f10740c0c2d02e180c07100703ca0045120290294004101e04e290 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 800687068 1250 800685818 800685881
    0xc01080703150f0f0602070806070206010911040915030203010c03060b0304060504050c0a061e0c030509091513020309070b0f1e0d0c0f032a2303070807080604 70
    0x40c440b0300030024640e994080303400daa0107035038820300301c41000b40700900c410741c1d06008002c0681050f200400aa0403c070400940c0c8030310501c5010301c070a544510201d20500310038201d600501200d60144200f02640b401118481d025100480c4250719141d90000e68074041e000d66021915000110360555503039888882c090100203000f15a070303000703640f004030b02070707944a9049002d82902d40d40c1161b00c8001c68804582092244001c01c2400f50500307078680040d5000c003c49007030035001d865104682d00c072000d540c0d26802c1041c6900b68002140c40d450f814041c5640d002d1441506000111940c1d99901c544d40700c0e140c03160510320b05805908000200300b020842000c02c00400c00b4203070f41d0b45495148403000c01124048031040d400141c03410240088030364107000c1c880440408489401d0340c101ca80b500241a0041e840000701400740700c0c5d80c002c00b051210f00302c4411120703850740d042d5035900d0100c00c020402c1304200d4088003c50b4614000c82c20a08042c4280d000041940711859035900c00d50300c2d940b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 800688318 1250 800687068 800687081
    0x20d020703021903050a12080109110f130b03071211030402151e0f12060f2223010e0c040312140c0f010e0c0301090b01140d060903080403110c01080703 67
    0x1400c03d00c00500100050080007030400050003075a2450364060025401850b00c04181d01180c4580e00306031074040c6180c0460200e90f5241c01c83c442c0c5079520380300718885401d9051254011102018084200000c058101c0d001e01409015000d0402c03040a22aa0b40c0943e03010944020303405c003080c1c40d5141000720a040003401229079100010298806040041c819940304000758860041c01240311200c600500380d45c142c204400b2140e05041602580c0480c0da24440341c45400301c1034035201c0340f40020780800d42c4655026200c8900b000101c0d00e03183c1c2c01e99010b4000384500341407102201c0004249580c524140c4050742d03440780c404804402500030440f942070202003400c030b62001c100610241c007041044600a50403103800085071409440883c141007019081c40503009904000180f80024150454141542e440480000184d002c070800b2505c1552005802006a807410090380c0506030003502c02d5200782c0c46a501d03002b541c582d01d0640340d01c416540039514046844800812070280c0644c0020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 800689568 1250 800688318 800688349
    0x90e030412030c0209070c12050a0c0c0f060801050303040b04050d080904020d0608100c0203090907090506030901150b16061d0304170c03010e0a26121501020d02070302 74
    0xaa05007a220303200c0c0d03070484450000441c0824040982d442c1103082019106600c0070103400c1c0318554240c10b072219160400c18240b400304112000030095400760285180f1a410340e00204603844d880d0f2500c40d04081e05980c1c3c0a08004524020000100c0b464008111030503242c1c0d02040c5402c0928000510003240c500c408103d8540c2c80600c203d03c02c3d48c40b1440a020705a00c04080802e0301840c00c0200313401c142042300c2e002d0499003007d0039001440c2d000002c0f02d803810400da0700c0380d00c10358400d00c08584500c190f4004942c000f81c0007042c4400100150408040004008525a1035554030909490705100f6140074403460702c6980e80401c003145055120780c00c00300203020b200c000b00700e8901d501130840d417181c1c001e11a00962943c042d042c1304400c200340e80701c0c28400e600030040301c0b00078400c1c0d980d80e03045110010401c80c16025510000b143c2451042211b400340c40d1401e440d9100e0a2a0b400030001c201d4021042502900240c0115880001c42c0520301450340c01900351107095409010503802d070b030b0240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 800690818 1250 800689568 800689573
    0x60302030408091f0f02032d0d050702070e09060f0c030a061e0e06040902030316150f050601020f0105010b19030b0603010b09010809030708030c0306040b1e04060e10090e 75
    0x100801e40ca0346010400819600890f10113012940e1501034045d10004001034111360040c072174202c000000030304a02c1031401c062001814518640c0c88000c0604c03481151015060502090010b40c030740000301a015200415042e1806a9840c660307290786a40c2105d80c00700341811000411400103007a4015904442d40a5000c202f0907159194204405011401018003d0028804012443e070a507001c0790070582c00c5505108000c03294000035500c1c0030b901c03070400c0340b0103034540300604001402c4580b801410036500e0034840d07000b207040743e01c2c000c00e0308403a00d40c00f6005040070b030040c07c075040c452a816240404142810034102411022044c00c600d000c0400381541c4251200342135070307000c01035400ac0c185400c0c45030f1f4505944000500802d0084e0420585504c1030240c5800140d0314020740394010310101c040c54903541c030a00050094803480319400e410000d40307160b464503205551074007001080151030034000140d581d8001c05180f00c1c101d03182111660410021b01480031503070815903011215008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 800692068 1250 800690818 800690827
    0xc1005090a0b04050a0c080d090e1003120215040b0a0c02010b01020a030f090509090105011a070c03020f210604031b022206080706080703140c0909041b0b21070504060302030408 78
    0x49000350b1000ca47c01450303503a8428441b1051080e400803994014001481c044a4181011082c0203004101e0b408001d00e01803c520503402aa8030801c80b505140da150800c802c134900b418201415801c0081da80e0b00b0905003070502c3d000c580c40c014002c0e050100c0c010707402040552651b441c07c40711ba00030000103008104440100081940c3c8512145006280002c00040c4552401e48240c8011000300564a0088418090100400c401880007412aa0184c3d040d03581103889000003404160707458800190003000d0240300d00e6581d80051a54402d520070303111a8681b55866560507803021403104001c1d030110820720342079080c004031003c090f0b100d4003141c40880d00c1a165003c0a041c0882030b0400c00008d03842d02e041092841e41401190300c1620940f0b003000940c242801000b080d4482e000b00d05002e488214041000c225056000101080c08440e841d182591545042581540841001c1c54601c01709035150125003202c20780c01f801000d20b03449481c034040c074007101039003e50002070064031050010300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 800693318 1250 800692068 800692073
    0x13081c0b030f030409140c0a031503060c0c060b04051501030f0e03031303120917160519110406060801030b180a030e12010b10030f021e0c1005090a0b04050a 69
    0x100e52070b11004203601a5882c0c1d410038040c4d5049480c001c42020800300c080c0240f0400004a4045030510140c0385000304444401d85500c9141e00c0081c0d00040c0080e00c1c1090606040d5400798a03460298880c102c10720500f05d055081105941c0207542222f8450404090160250b019502c0449400801440170031080008461941180c000302c440006600800b07601c80c0405d0f42c0441603940c51210381c0c400b00603501c03458461002c001109960381d907003030750009010840c050102282c03068080c0d01c002198001e450b03841d08400604100141212a21600794807100781c1d1925024900035110b01d603070303484000d0b807858030f583c0f03050302c400740c103503004d40701c41544030452941c00b40710b40c500d128000e85850110313041000c14005440c1041050000513450300164030320359501c5080004510031549804288e01051142641c005e208002100312082d02c5800e220101000641c00b07801c540e10804150303201d9505010600084c1e600c200c0c0d450103542c00c45801c540c0000d10440c1c2254000740503c0444a0000895 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 800694568 1250 800693318 800693323
    0x18030f1110110a08070c0c05121504060608010e010614010f091505040e060906010f050a05120108060603151006080a0b030a0302060a15050a0315110a110613081c0b03 73
    0x7003000c465006800203d442c2d50a0300706401513000b00079450110004034950b25504502c00301c038000c25100c6d030848000b440c8900010400030000000082c507211361801c0500d0180000c2100d44038014895003004040401c801041c07180348102c03815100d54580c00011400110342c100d01010070041072100512011441d0b150013480740040c2c501035282c0782c0d03486041039404c402543c40102181c1c070540c0210200300560b644051020024070344c40c2065038403440c00740c1c0c044e03505d8007418042815100400d030001469000000780e8a00a24094041c1e030711a5151101201d180402103070303810b0b03035410b03508400c010b481d10524101d54410f0114400148800c1000700203418180d040c0001d90060340244e05010f080b8034284603c510b4501c140314109541490400459001442c1d440003900104002c5440c00c40d010440d0445450454201c1c1605d175034003991300c4043e0020401700382e44426440f8000000d2120101031036120250743d040740940d820f11080c81a94040d819040307142c03c60240d161062198561401c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 800695818 1250 800694568 800694581
    0x80307170412050109170f070b06040219080414030a0801180f02030a021201090605180408090901030f0b07020d081602011e0920100c1103070b0a0318030f1110 70
    0x1d800082520030340e074101180402c9601c440221b00c91400c01c094415800188112144a40c1c0a10b0b00100c5940e0800090000e00400d92800c900d4050059110071650b13010022074403980c85240e600350101c2d14450703034035600d0052380e0a0201003039288005001a500543e00c000103030b003113180701003a03c0e1900c00600003683c0003560031a040a070040f45805000b0560710300c4502510009404200d40c5280000144402c0b0704100143c0f0407106580c0131409110440080700c0300c08030b0241c0301d14100c1d40d5902d000c0026050038401070f5501030045003c124528408502e8810304040c075904c05480c1d499542c0c690410b04407041d4940d0039507580c0c500c0280c041c550084d0503a1162000301001031501c02604080942110b4065641c4199000d0700c6200707519604da8980040806981c548402c5020091030710b01606080c89284503414440e00100044000c1c1990040c4013a410315681132108803070443e1012258035010300300070b001ca80d018480c05841441809103c111303d96480845c1c0702410b002e10068203d400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 800697068 1250 800695818 800695823
    0xc03060402010c0f15020c0c030d120216120203071203060302240c1c02011401050d0609330e010c080714041a04030c0b07080301030b18060727080307170412 69
    0x130041a510094241441505800300043d270290030400c0e904c0c00005c150081d03031602100c8803a07010818020101e1a40c008038481a07000e4810b691071845600c01940c2d07a004480100e42c0720300d60200b0200c1c90351180c01484101c0342d01500585400c0380e1140707500d0340d0014021200341d06000c00d00c141e070301d2810100140b112070f901d81d8071364681c0d0541c02d200007030030340b100024600d142c00c102d000104500c1d03c40c06408110940c07c22000201c1215915110811144c180d215090019130141448848807003440c05914000029004001c1c48002c030f07150300c0c02c0e56a03d6000700c3c0458000000a52000e0080064140484502d4103d80c0f81c5501d0384004041c1404207400200d4007003002c103043c41040000e41c10107024118003c082070800b801640c0d5440340d880140401007050750068041040308851248a880c00320100c0180c4503030b0707d04028010851070310320400c18001d40c40320004401c0000342001c03400c2035460041c061442c00078241c40310076407410f500d0050110190108000260302e00d02c0e8000042c500d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 800698318 1250 800697068 800697071
    0x30a08010503060105061213080c0d02010203010e0f1e0405101103060a06030e03191403040602030412090501020d0318080c0a111905010e0a0b030115110c03060402010c0f15 76
    0x50408082c540b501030141c010034051601080500160350215a200d680185260880381c00b42440e8907040c035907401450b04105c0705116240c1110301154041d00a50b0507038500d01500103480c0d0312101da00c0c2110405a41c925035001d41c1810505140c0c007440c0d803ca078400d004000301c0300c0c9090380b00509030454440e41e45945043c0804000d001d0549020394180c00140340c646418420700740913116042e241e100f00d40c603007400c5280d61130041d905036003d41e668012a41c502903200b0740341e1600303092041c080d40c401c40e4100c442d14080761051050324014100042135681c181d005112a08550005400820003030106584d1011030468000002d00c118006000d455012805824103600314902080d01644030816144915901d0320707694901500b141c0d030300040f520f00340f80266406070b104004c109410b1480c0c000b4035030325200000110718060002c0d15900b0001a075a1000b00c50200001c0c50341c0c80b00c800f00c80c80340d03041d04090046000740d0b2042440d07410450189030000c01a11a555980c0b082d400402d6641201d107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 800699568 1250 800698318 800698321
    0x8030a02042310050714031926070e04021c230f0403050703050d1b23040e04080f03040317060105030709030b07020a020303160b1b0702040903030905030a08 69
    0x70300d501d5400000318008500400070b10300c031050004442010192031041000404075070b810500c805c8401e0410601d00120540baa681c3c41148501d0f02d2002d01503144011a004201c2c5020300000c400c2e01c205002401c81f00c0ca00151507040c011034104080f40d070f015520075024003c40b0403d44a03503040c9101f41205800014000101c03441c10301e6101500345861003841c41c7c50080040a03d10580b40540c490740c50f1030000d50780c0740c071840c06840701e015880341d0464940c40d004a015111458404020250550740c8404100c034091590440b030060f0000e110f6540c80c2c0703060001308900300400300d249030424811186071b0f040200f44008814190004c650540005a00c8a000222541c00301103903500b10b08286821440d503c4c2c03201019041a41600c40117100d0490a0001041f81e442400303a000c0d07443d40103060381d5a501442c0244250003c00b5a81070328454246400304420b0003e4040c803900349686c0010090078400f8540801000b000344403070a505140c2c40f012000d000841c24002828640e840e9160004076 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 800700818 1250 800699568 800699579
    0x5190e150d0f060e011406071a07080604060b0c03161e0303050604060e0601020613031b080d0f0b0102100915050c120f060120160e0f090102090105070b060a0308030a0204 75
    0x94030629844a07441384412001400854001955101a003400740c48140d038800152070100c0c003106810040c1c14910b03017a0f409010505501080c803501461040f5010700c62940c98180e401d0b0705201d4010360b24110380c0204406604510b5120381b640c045030042c1c2c254035100300d41c041d03e41e4070102000d10407030029940301c0400c40140b8151080384050880071051201600d4050000707903560030060074500d40d00b1010f1000408040c49107402c520041610307800c54410009614166865803c084215000c441c1801144064038016201d07804440070164010505040c205503220020108020241c6d202c0b44544002141c41c11140103607070056402507009551b403182c08440a80046000d003249441165020502410b41e0384911195059846948100c9510b060813102034a0040407150b0b221480d0001d00d800a00c4809584480d88181100e180790101035498107030b40d900303c1c8200214030340490028003084c0e000c80c00390303ca080d80c0000040d0015111549a4454101603002100c070303c2501074001409226 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 800702068 1250 800700818 800700821
    0x80c04260f032a0c13050a0603080a1101060e090c0105070c0918050d0201090305041e050904050106150e03060106050a0c15021909030506060909190501091205190e150d0f 75
    0x80443c0c209016180b907040980008524070030104440c1c0c80c0a07110383c04511100b8203540420019039114103116604c40840102926200c507101c0c030041c495180c043e000400c4200b041501348501441c00103040300c0c4084c1c0c40150740c02d404ca15415106245000804181d00c0103074030a5043c5990403104044110280e440e00b5490428281c202e0340440e4180048500040c0c0c016054074207560a5140c5000e0313040c00b28262503010421a440190b014110209101c2440030640c0000166064280300b000b029020050035203800143c50350454159102d07200421416102e000a0200c03500d10f460560407004113500c448600a20702402010005d07400074182c4011800d100300c009000905043c1102d58510799101d25443307120080045014055280026445141c188050380001c180c07058501e022005a0130502d00900041c1c030308581c000300b20350000d800c1078010000d55120313088002e155000c050703014404032541d600203a0b44c1d40d040244421040080301c803c20241c1603c02d1016000160300654008010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 800703318 1250 800702068 800702137
    0x1030b010b0a020601051201020d0906090b090601031505041112151f090203060303120a140c0304021c0203030c01060e0604050c0c2a061603080c04260f03 68
    0x1034851200300b1403982e04075008510141110380448030702c2000c0e9001e0284502a00c81c9840d079489251071700b03644108203e107070303407118046500030a91168103035240c804881d96a4020301001e040d45100080e5001801c0050700f2443c0d015100d08441200c40c0c00e06400306111041c01a1200400d8020498044200740e00700700b400da0102e1010207141c002128031f440c0c0403001200340a034289880d0004002400ba031010411622107144540e080d00e914a0f00244d484000c01c12100a20902d146100c04104010b00d21426a80990b030018425107010403030003500c40c0481e004003002c0340c040c00b0a020704c02d00f00c2003c0c45000b0081c503480303030b2090092400408100840c3c13001050241c00c410203028640c00c00c40e0004040c0003050300d02d1010302245440f250346a10113031034407045aa002100082145004001c420001700c10361013615815181e40320f90248207190700aa000c0c0c0840c14244036801c904421090131940b500e41d0b14017041e5491054980f07510b6041d98041d9181150b00b00b03443c0c42f009009400580e800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 800704568 1250 800703318 800703329
    0xa020f130605280c0b0406020f131e0e190608010c0c02030705030625090513020703120b0f01050f0c0105090601031202030304080d0c031d1f050f01050d0309030c080601030b01 77
    0x39070a06201c0c95010349100640b41d8042c10031458000086c040114560441e64030488005120762503000750503200da0010454050b4540a401c002e08492600403078100c00d03000d40c1c410905240301d99581000702d0301384400d8950050010f030f854210025014030301b1322522000001c4c0c1e46d00c9440415050042c94a80201588003601070340c0510f0820100501c41510000c1052244c0c1905682010319a011203404c0090f401c03065100484c130031501c1c60429542e004120681c031036215249440d100e01001710440340c11050340f03078010940084003940f81d88240300414820030588901410000c1e02d20b856402c5540803a41c10f047c1e6407103800103000f400201c0304200c0ce480e4082c4000c61075440d0603501c101c500d01034000b00b403400a880e0005041424001c2e0061a079210500c0c030440030050403108419035540c10b40d000000381d1b59181d0b01d12007208a1750b01890b88601000d50703440748981d10f09000d000312292000406e40800c0382d9030101000043c0342080071782c010f14400000340303200d5040d406c10701c01c5d0240c1030303021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 800705818 1250 800704568 800704627
    0x18150b060412020f030a05030409050a0f05190e0106030807050f0f03070302030a030c09030b07091e03030804020618100905030c01050a0804030e030718020403150506090a020f130605 80
    0x42281400b4501440340c119416a524035169402da00031a02d0700c00c3d40600107009002c042400304185105511a920421140c482805840f9580c000e02c4100e50f42507401c109221245403a03040741c91525040400e900c00c84400010300309642c0d454201681d08080401c42c0d6903045030b0361440303401c9410000340a0400f4910059031410115a8000e940c80c0709900c0780f501419100c00914038014090150030004503041140d94000380382001d00104070b41d5180c01142904002100c0c0d01c08081140b0080b20266a031684445415032196001c01a003034108101100d4642c40d41d085c41c4095448010300150342d0181c9480720a0442c3c1004205400e00c62044011070411102780003901d1001c5c3d01180d21038205406040803003114440c0d1000c40c0c10042160444190582454021178020303a00358000d0044900804c0d050b05070300c48070008074068500c15074003180d01c0349030900451901d555540c01003500f0108142074a15102c1d2411041400400c10340c06640441c40201c2c0800c401180e22440b0700401120824 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 800707068 1250 800705818 800705827
    0xc2406100c11010c0b09060f0f010807030605090c04090f0302061506040302090405100c0e0f15030f0a0b0901030b0411041122030516060f080903090409030318150b06 73
    0x4020440d0000c140c0c0a000801c00b6041000640d02507000003050980110303005086103482010701e5078901090b214031103845c81e02000148280220058181030b40c0500010300405d52642c0c40303280c00b80402030909074a5001e0107169036a599110700c64000c0003445562200c070b00703140170b090103403c100008001100011403000103101690f54501210152a8120348072442a10380d414503031314208590245100952078070300c80b116a960000300501007500d044480002090f02582031003a41c1501d581509002d60050000c03d00d525980982550f00c07041c910300c0041e00c01e1810001995000d820790054135140c21000070701052001500020450000955042c041018a40308140880c032800807003400340e03100c0c48400c0d411000752a003210000d6400034111244100c0c8003100404c0019584500c0f404a0700c0d0400d0b40f2a1b1a02500c1014400c42d8044080d41c20038800c40180000b03800c48400840c10566540d8906c4207030801c60411041c42c50142010840c18548255881c00700c501241e07201d48122030a03c07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 800708318 1250 800707068 800707099
    0x1008060106120c020a02130203061c0209130212030304080d0f02070308070f0306120605061f090513020715051f03050601090f0905030c030a030506011103090d03050c2406 75
    0x101500b100c290356800090405861004905145007101c000390b0142c00c2440103050b240d002c1e005540112800c8404a06030050001043c10051046074020740085c010000a4011034040003081801d0780040c12030003446104003078242c150351040b58226806500491903186180891080e030724500c041c603104500d8030005490103840341e10010000402c02c0010b01882c10071510a0300f00b00010003c5080d41c0c9404600c3d89001c9024060841c2c00b80d01606060103601c00c40b000341c007907004140046460700c2e01d0030360a00040c00f95040f11610b61000140e001c005600c0000e071010303582049032040318000146400d021149500318500b80e40c242d800d8603504001030000c154081b031040e045400b40c1d000003403100c5903039000801901404201924502000c98003000c6940c011000340702140c81a501082a60b40b910700642d0101410f02a40445034002e02c03000019003000640030000078040e01b402404c110017003101c02e10b00341080e514400800802c2c28820b080025010001d508400110f51194030000001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 800709568 1250 800708318 800708327
    0x1150801061e120c02061e100303120b0603010603090c0f0b090f0f10050d0f15350a02130507020303041b03120806030f0a03120c091d1008060106 64
    0x2002203108200c1c142c2c1c0045581d0254402e0b108440b0342d01e20902602c810490701a40703c3c402203407035403001359101090004410035001c0586c03040080d180901c00e11411602c00b1541510080c0d60048090f568a07801c004039502c0c200554000c201035540030505680c07038545051642045d602015000701820401d0140000c14170aa0f00b6640e010384a2070f451a01c01d100044088070f1082c07240d40c002070a8060707190030680c01001840348008031368003801043d00f0041e4800031194100d22200207440c58000910425021042d05050192044450b60f1300400d801c018083c8600300d003400010035807000407101c0071030038040c080c002c1c030100d8030101304032515085034040e403640f1000784024900e600d2001a5544c080181018034051030300711f61604205401e8401c017500014054440d0b40c8203201d01c01c0700c66400c08000400c1e1b03140c20303450f070340d850801d0022070441c40141c400d060b0a04248a40c9440204880c1c100803030100040f003400760300b0081c0b424821517441031480b10342c05c1000ba98100c0d100500ca440d411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 800710818 1250 800709568 800709587
    0x111806010e210c0a060203040321030b0306250503040c05010c050f060c0a14090d0b06060708030a0902090106080108150a0605120d081609050f0123030115080106 71
    0xa08018680c0210030740020060380c050007106480da0340108000c0ba6074000025410306030740c015501d80c000aa220361081c1c0e540c2c06144801080c804683d041c0148175200070070516841030060402041861070b100000b4144007045403101301490041101c2e0241c102c0c100c4603014040c41030b0618910303505094803003141628590103050705000c1001103980800c0410050b00340e040036244255506800c203040d0343d00c1c0a6000c8103620000070004c000901d043c014100454034000350003000da40b41300b243d80e598a80200030040006502c1b0704140b1091001c40c9100c0d004510540d0500340000d0f840503244100034506a068218804010b03150005000401c40091020120901810f6120150307440b03d401078080e02140d0003007504a03510406444000d003002444100e0364a082c1c03100c50f03d640e283c008005d6a890105504000181c5140e030402c00c9003401d0218a540351018505481d010560078440300303009002d012814025540080104100301000300a40da404550345000100c65150510081c1011803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 800712068 1250 800710818 800710831
    0x40c0c0303230a020927060109150203161106040801020909160807050310170c0306010816060e0f0411030f0a0207021f09051203180409080a0c0f1e1118 67
    0x40c00142e0785560346d1000010006682c1c800322151070142c0780f64000c1c90000050781d8941c007140021002007501e1003080a4039200c42c82c0c41c2d0055090500e040b6485c900c0f0354500702c1c10b0b03ca0395145000481e868450200800207801d9030710026a9869481080c0100007000400c14404440001c0d03105000d40d500902a503085082d5141181e01c03601d98110107058243c003548042c6200c070143c00b2101c0d544102090348880028110180c414981c0d840b01c00700d454018ad984811040b40b2003a0080c42424000e80000c5074001c4050101351001c80d510012401700c56600100304c01c0e450000c4204002040c2c03552401e1392204541e0310642c05c16000d80e0106d0420b00e00700001400c070301d006d84200f00301184510828002860010310841040d07201c0c40c407550b202c1d4041e201006400344000c0401c2881e040c1806201e91540c0d0194240c3d00d04654828111905440b08000f00e9035604100c550030b011038150010030710a411500200d1050101c82c2c580703e2018114000241c0c0140e001811f14161008502d088070380c80f08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 800713318 1250 800712068 800712071
    0x3030f040515090307180c020c150d021b1606020706080c0c0a02031509150f01151206060909050702160b0a0c051203090c121b0a0302040c0c0303230a 66
    0x4035660550a00340c0a08901650148113038600042c0d00c0c5900c448051a000152004108051f110340d0100d84070030032500c1940d04101c040c01303281070720390fa000014008808070100060a00c1c044010940500c1600040001560701074400c0b00300c4100c00b41d9041004000c01d000400d40f81c3d15020015042c00b50041c0f0010085402064500305114103002c900081c607401003e40d25040b185c071020b04400c640c06d44540f00c0d5407058100310009030390250310448c0186100000d2805682c600308140d04450002e5008100700508240e20481c482000d0241710301030105131b240e0311000c1c1d0414071000308444004141004550080151540040f090300c80e0300d040d24040c0b03030a00e0341d4190040060f91401041f0308010b2051080310200e9503e141000c02540c050040e81058410f6020f40700708111242c800c590348c01085c1d0f0000240d86081e190580c50a800ae224003510404240d90381e40c0014049480d102030300c40c007090034184850304240d4144128007890b8450b640d00104a1103a8002800e0108001c00030500030b0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 800714568 1250 800713318 800713339
    0x31c08060931060f0e10020c01091b0519140409020103060b12100603060b03130201091d042604030803101e150503060d0303180210110c03030f0405 65
    0x2400c0c5455000116690b00d4507030080c00345294101400801e060806855141c50544582d0603420b483c003034004940d4809008101c4280c030355100d0b200070340c0240002c6407507650310307010600000e00c201140300c01c0380103003e0300003040b510300401e0000c1c81f07400710a50840003450319810301103260a450228500f03982a28001130000301440103800030a601c1e00315004c07135000810300702408000e03850300c01d00c9900034180c0382103e9a075444040c0c051b641a07015000c01c085060001402151105800180e043c1c0140740c0980d2042c1d07280204140502c0484100c1441205c00c410007050112200e07640140c0c6659174241010354071100404121400340d40002007000c1c10001c0030a013690812003e490103403902c1c181e03908101516101007a00c100a070721462555102206000c0e20440c000c00a4902c034820251076850181c0040d0f030b044004290364240340c842c034501016084056152507061005450b942d031a20707485105003042c41882c19400081070351195004000001c03840c0700101c107550441e0415181c1d403610 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 800715818 1250 800714568 800714581
    0x2010903081309020d06180e072c040b061c02060a030903020c1207150c0b011214010f020306040e070308071e080f0901090b030907030b150a14031c080609 68
    0x7103142c0e510520ba81800400e0001c080d03611030b401402112000d180c11941d4400c011200c00a45115030f8143c070554019040c20040300e40e80459107039500200800c61404c1c90f01c440b462030340d965020f90b000d40f044100a401c106503410840c40c8440911000140090000e52960014419216102c0396600305500c5100e00000c02d4002c1000d0780e0101401041001e0300c415903080c89559060b184a226501d440008801c1003413402028040c00d00c94000350b144005a080c01c15810900b20070700401c450280caa0f907000b1040c05428400d40c10b0010030254056aa414107808200075a010200482a15004110204000b4280d4821541815403090680c00c404c09404c0319140150b0011002600c60440000d134508601d011500409a08800b40c807068255a01c68820502e00e0004032180c18442d440090184045500030505d01c0e406105900503002c0200c502c1c01040c4d11000039484940c10000b034881204103460b051041030700c81c072000c04d10802010040c60000344402c07405008240280054404107aa = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 800717068 1250 800715818 800715847
    0x8011e0605160b0103142a040c120207060509010b040b0f0420030c0d1107050a060908270307050d020d0f0203030d092a1508181507080907030201090308 67
    0x2440c2d00804410f000d5a56802c090340c402c0710701e2010b02d000703005aa4003040d07282010f20b48108414180f010a030801c04940050000806100032000c0a00000d442104151041e034002031101c984111008521410704042850941c1c1e000d2524520a40c1024144240c60701d42d41c01c0000f050004482c00300c1e90025940f104618003003d001001e003031490001c100905540c0540080090000c10441000f44a0350000d42c141c0c5801582c2000b03006401404004000c0b40460300011a41e0b405901294608400c8500340c101d13454880a001c00c1a607030000c401000740c07070b06028120050005680070801c2244a80c0082d1041004c0d500040105002c0c2c40c00205545041007980c1030751080c0c078402c2044600a0400341d030310300d08569403095500c544101c17010000300603000a0040351451607031040b0076010320005580600340102018140f8440b5500c40701c2d645400c0001c02200034140e800c400c02030800d0345008000c06001452440b40740d0080c6000c00050364040785200840e900300034101d0f150703c0b15074103140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 800718318 1250 800717068 800717107
    0x4060b0603010e040516050616051204060909180b130503040504050411190b03010611010b06040b0301030b0117030d0e010b0409030806100801150513080303070f08011e0605 76
    0x2038000c08044004100908401001c900583c003e50071a00c0385402c08118120f00c0340749004040d04802c0c00e2000e01d80304801c000b06c03083d9183c4110b0540c2e0304400c45400c0710045420a910880024000345001c2201e1440b62241c0803d96a5205589a411150382c451560700c3e20090a2022003250b45804a000c0c4071061095078080c100081081c406400c19007441c80b080b801e24900588104007441c902c082c4014000d140c402101c01c6405014150b030304c6e0410a9410b0300d001032500c0400d540307409440a607941c6920040000d4032080700d04948950460500d41400c03003058028107402480f281400507880c82c000140c030100380c0b0210780810403510700c001c0280034140d140c0c00e1a4000d420010041e0030103802512141c840d01c0e081d550001444050b01c0c0884045400307104101545400700311460070340e0f10070f40c0100725440d110085004280e65843c034240c5954002c03258400050314210012113205d40c841d082030b004140f0180d01d071480c942e5641a40d030f441802445604240100007451a6403400e035030702101c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 800719424 1106 800718318 800718341
    0x7020604060e010908041205010605010906141c1812031517070b040f0f0b0f18120709020408160815091005010b0a110718050406 57
    0x7400400921881d04815501c03440a10040703486240140300a02440d00700d84141031090910508546568200798100951041c1c10448168131001d4002001c010032003081d580d00c290809a0344013070401c0e41c464842c50034980101c000c6101c1340c18003000180100500011b80b1211401242250615060f0102e50311600400b40b01078015103802d000d0001c9130608480f041600c540382c407680d07500240d000c0020b100700000148101c04100184d03100414062100a0a0050035850a0340c1800b494816111240a101204105d03a40d00b014440d450310b000019a0406a150490280a903229018189403482445910682040d00c640601c003110716100203011402184003901c1d4580780c010742036030218032070511803d000c840c00d171207a11300800c003248410750346013000e681c06414515400c0c2005941d030003030304081042005084449180400c080300000c0c141e035503440d01000820003207401 = true := by decide +kernel

theorem cover : BRFrame.Cov 800539568 800719424 := by
  have h0 := BRFrame.cov_init 800539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 800539568 ≤ n) (h2 : n < 800719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
