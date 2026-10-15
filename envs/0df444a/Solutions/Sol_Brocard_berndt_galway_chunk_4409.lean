-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4409
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:31:44.177165+00:00
-- url     : https://prove2.me/submissions/f274eb37-299e-4809-8f97-50edfe53cec4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 792805755 ≤ n < 792985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 792807005 1250 792805755 792805759
    0x70c082b06060219062903011505090a0f020f031303120c0207180f020a0c11060306131a100c0606050f0604030b07020307080d0c080a0b03100209040920100824 70
    0x3400d40041d515036501d1b406a40d240880c90b0301c1c540c48252081c2000c0c0150070f004129822403d8800f440c010100c0e0500300001c104003900e40d40d5040c41d81c2007180540c1a1040c218031403446076100e2810504240b00d81c403059a054010441c1c0044002c02c0040c0c0d8012203002d5801903019013141c034946403414070143c02c40d03411100513640f1100c1c034083c03403007040c03000d01602c80300340d0b40700c00607a036840c00c019120f8618501c0d102d01450080081009581710981c0070311100744034800c00690000d0b120341291220141c4c41225a0107078000e0204a81d942c0d0103600618094041c00c020040c0e150303103004201301108190b044581044050108001050440781c40d41d50090450041e00e240c20650758a08419610210803001d59540d11641104100e9100b0301041c0e000c00d0844003081560036020000340e680340348180c00c11619400180510058031903400158986a00003040c000c001c0c09007001c80028500348000500501d080000c9800322031040101c50b00584025258031800300c070028000320700c2114990000d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 792808255 1250 792807005 792807011
    0x815220c120204061505040512010e0d0f050d090606150801120b04051f050f2214032206020d08071e0e1e040c1d0603070c082b0606021906 61
    0x21742e81d4011843d543d0810180c1e9a004d40c0e540c144001c0003a840359501c4c015544d607150201b00301c1503010000f10404038800b1130030034968120744110304a03a40d01c40d00e42c1c0080441d0501c2c44100070004c0540050701a0b9032414915581c140d03950f10100c4200c90700f4031440c0300c8e42e815050900085400140801d070000c0c02142135800c040e4206441c04418005540d110b03a0f15a0759004201d2485082030403143c01805200329080c81c2a55420003401d03035550b188018100404041c0b0441d1121402c000704c694807102c002c035500f05001a00d5284020b2100d07449a8405400750a40761200b90f8032902d09184145d080f606e59002e0b202600f2450b90081c200205408184240c1e1b00c0b5a0780301e5074030440105030052540c1468090340c0034103428482500e480c594040240602c0940d00740840c10b000d20300760120f843c283d481c00e2301c0f81c0e50103108440c0503292801c0548031100004402001484d00b0107440c51000c103102c3c0c10050020400c00c0e15040310864030803040145c00c04a40407a02c0c00e07000408149140c02a2008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 792809505 1250 792808255 792808259
    0x812070f0809120c1003050402030a03080703020405030d030e100c1d0a0e09011b0e0a03240204151403010b0a05070302101b090e010e070c03090815220c12020406 71
    0xf0500042c83e5248a81d001d9100000b030f4a2140382c1004141c1d14400e01d485c05110500f0141d0100c1c0e0380315111b01c4000d0130301800100003034209101c0d505440003404010100c034110440c441c4090010400e1680d046402c5c0240d103489a03c52640703015464184040d50b4400c07014146d0f580300da80620003503607091940013905602c000340034100d01150078028800c04000186001e150340c0032000480607404040f00340210710060580c50b690350745900b0201d03a00008080500b0f13410340c4110200e03410062003480705900c0414081072000501110034000d00240c1c98455180040c4031046230180402d21039160744000401ca01c00c0035500c44c1001d000402e100740120b0750641d15203003091040d07540851069a0150501110724481d6a02086180080c0016603242c00c4650401210407900040100040e0a01c07640d503280c981003500ca0b0040d01c00900060040e142c200b04000304294074a0400d0321089040c403801f8282202c0303c282107070070407031480d40312001010082c604900048502c0e42140c040e60b20075a14040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 792810755 1250 792809505 792809509
    0xc140a030902030105010e1e01031127070c0512030112120e041e0c03020f041715010816060e0a030b070c0b130b07020a0f0f080f0d0b01090812070f0809 67
    0x2405c0d003e4031500001100c0ba02c0d10390703d04964680f203075000d620303952140001040400e4508842000341202901d01001e00c5001c44c11907480c9000d60600703040085d85034403c000d440b544c0318001440052144050760815402e0f003101407480d0000380244180c041c041449000019840798400c503011003d0b062564401c1d040400240484041c2000c001001c1e0252411484400981c4542c4d000b03807103203060031400d10480d04821036183c0aa8003c0e0700b46520008120b918a13142003007050780607410005140b071070790b13110382466440346884091040e8424201c0404550f16005503540d0700f042002070324883c2020300e9030300e90192030800903052030180588014404080746120710403a01c40c40b8030820041040c0d15034034064218a800806520840d0002044000010315550181c0c002d60f4000e40404400d0125050003891403103045404440070b1000100c01c070040d481a001801640003d0701d038614900c1c0d581b0302c695154030144d450071048900400c43c040000d0030200120f054a4003c009950401ea20040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 792812005 1250 792810755 792810761
    0xb0a0515040c03060602010b0a060503040803151f140a0503070f05040f030507031a0c0f0307051b1c0504180f020f0f031008010b0a0b090301090c060c02130c140a0309020301 76
    0x102d4140007a0701d4070011302c10160240501540c40350184c03040b164041c6080e42c010041e0202030001891202e000011138160740c0d80d510300700300d80100248101141038607161080e452104d807000c1c1d14040340c01c10300204082c01c1c20303c0c10380e1004056500d510b850b50f46c9180e4116590740a0360041814008103203c003040d030702408141d8030701440c440c000500701d0790b0450420703410340341c0107000003e6064104020020a101544245c40d15440d2410740c442c0c40340c6a864055845004003a010320342d844000f50356090300b010018110201d003500a0710f80741813400340c20007200d0620a034007540d603c40b4103200c40d05400c0d0b000e6a0106c034150540c3c280c018103090181181c5010342d40449030701294203601105104102005104e07504c024000341000700154050302022440500b0b107413207803040d0706001041c01c190381c0c2c400307400c2900704c140e101140484044d124880500903051050b42a809001f003000c80100170072181c0300d4000059a03075140c500804501041d4110703258000f075584c50415864034182001600c00b40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 792813255 1250 792812005 792812021
    0x1081312020d031413140c061c0b0102121b12070303020301170c0a060f120f051617011a07050d020607120902090f06060705030d050f06010207030b0a051504 69
    0xc1e02906116460740d0004042d5603524202e80f055050a07000c1c0001142e031103c3c0190b050f0f900002d034015070301d490012641003c10f802c40d80364100c0c10000b00c40c004041c0056440b820051894010403a162040c8012a40e03080054000202060304021a0b6581000784442c1d8081008800890790f580c0350300c5010301e160740c010301800c40103c0d40200060110021000b0a0002e081400e4000e011a8801c1d40024080d15640c0c450380043c0401d03c40c002c200b603845503039210029140ea203000d000311904040034500a0404560030880000107001b0350301050b125400052190080f0708010405034280350100400f094201000d8020000412400e4005101131041d22542842c44d005002949840880580a000c00841c0940894684280a801603490300030341c0c0d4000d00400c452030503558885012410034490b00c00054000d100100e00151000640d401182c8101c02102100301d0b5600c03554016a600c01e00c500005042240c0c500c00500c3c0400340303502c0383e5800a42c00c180301100e145020302260441d043c1c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 792814505 1250 792813255 792813257
    0x13020c0d0e01022a0609060703020c010f03090b0115020c030706090305060a050108031204020103060f12020406080f03030412050d0c02030d1116350301030605061e01081312 76
    0x803808034680c1e0041011002001c003800039064011040d15040c81c00361805030b080c28101c0780041d41d4500c0e500e07110161540f510700505010340e1610b0178240a5a5048218009400510103000203410301d4401d002c2c50200580c0b0192001c2940d080c0000e6603c051070103c1d05030110f2055001b44070880d0380c104096801016039880e49d80c0410f0a40c2859420640010b00103110213052a004119174140082160501303014020108039035140ca2004130041c00c0e03940d025081003182110081910000ca80501582c03901c00c4030100900ca80d10f85000307444890341c0c02549901c1c0c206000190205040f04042201d588042c9440c521340039120b05280211000002c000d03005a06c081034030301c0c40001a11401c640d5109603c01c580c24520040d6a403131003200d80290007000c1d0940ca5241180f0706002c4140e4041e1385684000040c00d060844000c5440fa4100344002d840307007410300c0c1c046266818000304c140403001122044100501d80240107407098180504074a141c07115461003140843d400000b103891030011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 792815755 1250 792814505 792814513
    0x2090d17040602010e12071b081002040e150108040803041a100501120b030705060a0507060f0507090f0e0c1606060314012d0c0203040b030709230a05060913020c 71
    0x10200002e0841d05025405d88980d4481c001c41468890780c43e058407111540600f070f40040300d0301c08201040041c4283d001c01000e10440d00070700e105458903005171052314030500c03061074280c0e500180c949e48040042000d40c042102403003c03030003040c620002154002d0140003254401c211000c5132034105201250800000c4031840c005000799030b403000c14681d49d800030b2841403122806201c00252034014074401c0c0c42c460000010640724150003a01911116600b1502c1048510700c200701d07d902508088680f1f5000070700c103c3c4c0119401302c0c4080f0746001d82e02a11107410030307070381c4024800200e64045030020110701500c0c1c020000241280c0110b07005944108210243d54401c4a1140d003902c00301c904000c0d901414940442e2320f40801c0141620f03507030503104017140c500c141c46e0090381144110f13003020710080000420003c1181e0449003d030203d1349080029110f8003519220001f1508107101910b03440311440320308100b03520f40301020b4800c1d504002c0c8916480700592404100326440314400d1500c90f00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 792817005 1250 792815755 792815759
    0xc1908040605010506070510020a1b0507050f01090e40021f02030f090402040312090302010917031806090d1a010803030105130c0219080c2e02090d1704 67
    0x68203010b4140142400c0d144a401c0c00c2035a9a81e60300c5440061f0112110399000c210703400d030341742305050420b1240c000c0c01d1040c40000550900359100c3d034880c01800d00865410f160300b8072552040ea02002110462141003215880e010b1080727504600000c0d1a203c1c000c08002d01a0303880c00c0d01c041c0d40c620803040c43c50070003010781c00e03105101040d030002c9808100c100510511041158000c0102c803510b110000c01c4640d2400142e00290081c082d0380c00140010022078503c84001c0c0c2c000402034141c138006d80700c40c040da5030384440a00040c8046103000e4110381060141052600c21254040d60f0303450b00030001801d00014101045810489200179180007120003010680c4800c049e00160141c5000000380d880c41d8145004142940d0341020012070555540c902c155640d0f02c00d22200c95071401040080039180d4550070500c0e0341c0c0d0000c4402c3c085a0280c6d6040501da1160b240007180200405030340161141e184070b50b000025001010f180b03404c0200c049000340005c030032030040d45200322075181050b203580c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 792818255 1250 792817005 792817013
    0xb130206040810061505072a0e18062e0b0a03020703110607081305010213030822030b13060f180c0e04080f091807020f010b06030f040303050c190804 66
    0x113031564070074200c00f510503440d01c0710981e100084444043d04090041085180380c0c00c10b0441c0000001d02d1a1503607581400402c02ea1080f58070140210f100c1200c02c40103200844c0c0803515031109a0f202d410b01120300d219102d48008150090032003035404005222191b983e000125041e0703001c0c0d1f41e100000399001840204060304400311000c07001c4e03110010042c41c5081a4080c3c0020b40142c80c840ca03090030040d40703008024094040320b9032401c40d4110606034a0342c0c5d10b064a0240c0119a00c0300907000810490380c00040ca00300c850003260f8101d510340b2095102c20400310503030f010035001070314242e403a580c0700b42c0c440c1518042c4640210103811424a00341c81c43c2403501804040390401c0c129060702c0c909000102c0d800d842644d00740740050503c02c5d540c5180000140c440305c9101000310300e40e2010404c0013550f903004a05002c1c40225040280300c00201c410030044e061008450342d0029038030341000b082c00b0900c60303030129078081c00c1d01040724a045082000c2c280382c0b03041c0c050b48200003840304041100f08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 792819505 1250 792818255 792818261
    0xd050405010e100504120509120a060507030e1902040b0f030106080a06110a0e0f0414040605190c1d0103091506030c050f13050a060b0c0c03060f10030b130206040810 73
    0x542030301181002103080540d541c201c1c14206118000400c200482c523560541d0328015140c2c2d0f01c0c00f16104454004400d403902c032002d00b604403884400720b8a006110245610081161600c8a0107400d0240041c100c13a400c0000031b29030301030010b8100c01176480c0204c3d0f5813003d1207200d01030044000201414082803030728900766040c004c610803a0769024460f50f07030819040420050702803000c8400c004408407030400328008245031074200b10f0380762024050006121032640064050000c03c489446030150802c005816284088404400501d038a0034941c1100c0260170b402607003c105260101c1c07000c00b2511140c0d4221000d01a022155030380c0d07402081000452a004070003801c007500d400002000c004001500e09120381c2c0035000c1641c5900014440f18040c0c0d00003005171840315030b265101c8140c20324123a83d0305020b800d0710380244281c201188200480c40490b52180b00c0c104010780989045560f880c01c20700c805811400c100300081860801a9680c8000c0c00203041008010a0b0302c00c00e07481180d060b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 792820755 1250 792819505 792819523
    0x609022704020405010f0e012303240a050d06090b0c0d0b01030c0950030a0f12050418020306040b01090510030c0909020c071a03060307060e060d050405010e 69
    0x4110b10410040001d640c0181c0010300242c01402c00b01204e418940050724140d100c4444c1c50111088801241a64000c11000d18043c604200700c20403d824407030340102c0001138079580e86e640045c0e42c40c001c0045141c807a1142c20418490f84010503408016a075400b200101030316410310120001c02e03043c0c3c0110007480b40c543c0d985000d103070a2001700000640a0320b80191802030000c41d0108048405000c0354405102c2102c074400c02100081410300d40c645411411207452003929609031003004002840c0005040b4070781900700f62a054112581d1f514440c40402c0ea0003084244002404001031007a40700034058444240214017598900d000000c000c104c0e10601180c0b8140004c1c0b40050043c0e40300c02800e24904c0c1103900380003d241c0040581924403000d82c3e80180a407600008004020761400305044044a262946c0d1003039807840d6140c44142d038001142c0041d01070b80181c0341000360600c100900c0e11288000f91016251403205103018041d1601214182c94980d118101181c40150802c440b0340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 792822005 1250 792820755 792820759
    0xe030f070501091e17091507031e09050315060303030705160f0b060f0108070e13060b0c03130b0307050d0c1209120807030b0108060d1a09070f050d05030706090606090227 75
    0x86800803130300000f0046007d0b4030891080c80b1011500008140c060b201a0080350315040454951004a000c02050481d4a014207800383c080c5448400140c60704000041c003034040140a1811176440c030404880716048983c0b40c0760070021045146000c2504401c0342420310b07000301e01010803864010309100c80e800c40c511a0728104442c50341040380b1b02d98080016035900800705d0300312400101860b82200644150342105201e02d40c00259400c88480000081c095000c11102070080180e070b400e854001800111039807408164200000e0151800b16030041a00180c076050040780301d01160003003004c5601c28803080740e000074034000d04814160401e9004e035128425203000d004d07004044000070a82c200c0980454003401300d00304020b0400c11058400074404248001003051441d00d001442d544074010700c9056110401040003159509141040c40701e200d401800452420201da0785100c000d2058100c19580c0710790f03c01e40450624610b00092000260b83c80d61116503042085298500703e6500c01454 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 792823255 1250 792822005 792822007
    0x203030103060c05071e06020f0c0a0209010f060801060c030306090e010c020105010803031b0c15101a2a0705040f02040503060124080a180c0311040e030f070501091e17 74
    0x40002e01240c88140e9042c00b0184615036564452800307c020740039003038086500440110307081089500c00560000360900843c0c14412590b62601050a427140d035024203000a91000010f012071405100c641004d14881d1a0015001d44d594500f4003c0b00e00e0b4540f8048a03035100c2c0482c0c240c1c02e82c24014140035004600c00f9500d0341c00c0000710350602c403c001403800034244004c54034224040090290000380a44900c450790300d440c0001184000b00d40e41d000d2110b20502070aa1a00600111001d84000090868801400d403004040700000409004240100d5104050001c221034680d806041d0b0781c50300c2000302584ad141000201030034544140c1100035405030045048140048152480b007500125042002c0952240302c4903c010b03011140b60103000c0720301004800100880c2004940460b030049940c881c04030b034960100000c0d5132030038107200000d034424820308080f041403600400d006885600001a01d203007980c0c4a42007001560205482a03801d21514400c0c02542002c0440007681d0940003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 792824505 1250 792823255 792823267
    0x180109140f130204060b040b040305160806040b0a1b05031605091503060102070306090c0311010e0a0e06030304081014090a0f06020a0e03031603021207020a181b0203030103060c05 79
    0x18101c460750041002c1c0d61010060780080541d2600e074441c102801a01018956654607001c6d4801e9039800343c48221030390300c1182445481030341800c0c2d8090a4a40d41d9010b0119502c45860b0404402c2001d4031f141e60300ca5440a80300307180702c0c0d140c280c2200254035440e01d548a01c0c8ca0b0030000c00001c1e0308541710044c8901084590126680d41c841810300b044a042030742c2e180c1c3c852a0040303103002c140b900020721040c074142c018400d005602060382d007180e21035003218800d004044011108503100800381600940710010034801d04240d4520b0780cad4024406400c0b01e0500b5035480c1c005240803003100b43c1d0040d003641e950102d002c3d00e07070840c50240c1c800c0a00300107222400241d40c0790196652071002c09020544d000c6203680404d4030032440d5034034491006048903294155000404104903d0342000c4015200d0614008070404082d000d5805003034000b45042d5442e4030b03080d000011803540141c000c1061b90743c0c103048080c030304012200346d0f201501c2e5402103460750f066107841c1c022222181d0b00b1806106060100d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 792825755 1250 792824505 792824521
    0x308070f050d0203070e060315030d031811042405040e0601380a020c0102010f050903090618030a140c180105010c0303060302030601060e131407081518010914 70
    0x715100046210302c0166031780c4c1c92200440d4110200d22006910030000424050b00041200203000c0b441012001c1d940c400090010584c1200c0b82040380c9000a40c8600b400e0021a180303400140e030b12030340903001046115084524a0070a581401040d9200c03181582c103204a0916108a44034585114020600d039410400c010304608038680309452504280c1c80707040b2460405040c0d90700c042d092006107a0f11f90100354030203901c841c4092511401503282814071154041d4a000741405a02d100c006146814007800c1400020760101d844860503002010030a1901e071001c221016469001e000c6840c01032002030130190803c1c4c002000ca61050810445140c14080281c0c103080c1103c03000d082c1288695018581580980074a5002130f525000360301c00001c0741600201d51008105048076889400d4403e100d000d8110b903201030204a15a0741e40300002c0e00c0340c0c0511a0030f03400a1b640c00005107032400d0000007072901d0540c2d1140c1810002c03031000401004945000d00c0304e04038241e21940000307141a282c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 792827005 1250 792825755 792825757
    0x4110906032809140607140d1401080607120b0a091e0c1107051e0411070b01030c0302090903091810030803240a141521040308070f05 59
    0x1000a1165200002194254220241ca2492450708031030540d005105209010002e0603c030070240c84454001c1420503040d1808581d0350302c101030030f8903070307a1707184082188a241540100c080c14980035a030b50f00c02d040040d06401c8150080040702c00920040c81d00150041038460000c69103201740d400c2c401300910603070b00c8034101415204006400104c010700c0f460040300d1902142680000c5901d04580440040d41c007803030403902103440301c1c1100e076600d41d0360702401549221016036440311030402350108030381c1c581608040300d646074010100381491800d07220040c076000c080c0d004840da000128020000c5051141c00d02e0340c002c02500c051030074120b101d004144081141c0d040100741100102c00141207041900c541030155401540c200e850749002d030200d070b00c2c0200c4060110010699005102040d24100030b491055400c1d000c0c1d440c804801e0a400c0c0980c00484400310020280180950750304944280a4840340744081d14209d821802c0608014140503800740c0030404000c501d00c0341d0b040c8150020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 792828255 1250 792827005 792827017
    0x50306010b0304020f040618051f0807140f0a120605010b3c1b1005090d050d0b0405150f041803080a06120b19021204030c060b0604090f0501050411 65
    0x18a000d01c0c0c8061120001d8010103440c7c002c2e001c500d0f184988d1900000f07aa82c4081d01c100c40c21502c0da4141604a1140d0000d0829845601d000380d012140c140604211180918850310004d400041e10301c410800140034591140c000781300a13504815110b045c06420300690b8018148040f516207405000319090740b130417000c0500c07a80258403050b2603081e00c41100071038809140c00c1180043c1c580c00d803c0d030001611501011a05601d1082031030300c13031000142c0d00c0303800d0080d92000020030b0700300414075054500313800a20702c440d207141c1d42d80c1ca50b0300b00d51200e000740c40c030800c0c00508800940b080702040206a00e403032008540902d192000380443c007541e1041d126034164050a042c10030750754018100000e403440350001c558406124071030004000c02403441900a0070344402003268800900c200b00124050402d5000e180e14170100420003081c0290005190140070316004a441415900410f146600651100c0441903403104440f0440361184140d50151500319810b11000aa01546950a010380 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 792829505 1250 792828255 792828259
    0x1b030509010e010215010f0f090b011e0c1203051909080301050402070f05120406110d08071b052b020105091b0d060507020d17060108011a0c030c07050a050306010b030402 75
    0x104401d40507503130081000020009030740503100420340c0c46044002890000b8460172050f50030305c40010071070300114000d1240c00d01042c1c1d20040000080600d00c2c4e160920310712500140982c202d03094022422440b41151048182d03100440d01d410322922034034110000c560318610303851400309140002201a02202d04503101150702580ba024a420301c0c041480680340d00501a201b401c0c1e05103907940a800292046a410b500d03008034083c070003981b6545403c0c07081caa1200103120301d00060b040d14062040f484449a00c11403a407444800c5654092520400940c440800200440e420311040f50524042c4407000c464030090000d4180140d00d030f5a01c018180340392a8010b83d03010722040c0d9448801d507151400e50015018080fa0620150103520342c96a1502400061400c0e0345140d2200c1d510801c040c040e85040e9643d2f40940e103000c01503d50001c080d902c00042c800100030035071080d50704101400020307110801400500d07107010304010300c88000d540441d000e500308000410040c4008015a5842501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 792830755 1250 792829505 792829517
    0x19020903100204030b160504080705062809030c171c0513060503010e100b07021912030504050901170303070c020607290a050610050d27031b03050901 66
    0x5400006070400da561800851040c0c4046800402e01c440914010300903450500940c0049944110071a054480c60080a1081d03010117010080f5050040040240b212030f0751505001070381401d2101e12140381c8581c0180000c500c00014814402c4060742d04005054180c5014181500c40003e01e482d01068082035460717850034502c031544280980100c4540320089945501901d0300e418014001e80c0003030245105620001c00025902a40e400c0c01000392407800c01001d081130500c0c1d003000308000501c034110420300d08403c8000380e030070218010ba000700c038030903101c2c940c4842c100303404d004210005a0050304818005884000006000320851350042d10703525240c04003481c03c0c0089a001e00c83d040e801840d211019034900a4522000b0207041417480c000002d1442d0340741c802c1c664040c1c40c0d055071090380c405134441e00300d03915601550080201100c10100480c848000344242d0450f40d0b0721241030812051094000400c25038016600700c6105004500c8d28041c0107103850040060160050007418070803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 792832005 1250 792830755 792830767
    0x1609050915040f05061e070302160f02010903050601151d0d080c01110a0c1112030a03090c1a0a020f01060311120c040f020a020106050102011103220510090b0702061902 74
    0x10b1100e5482450f107811108807407240c00e0400c90400403c034040c2041031407900140200708000d00c87e00880342c14941076601c40c140d820707054036403607000c8081030800c905101030182d0000c006141480107034020f200c807103881c0d01c1004041d02c0203804038066103121460700340c07810b10461155540f4400c4900041c1c12500054982c41030154040c0102413034266010010804108a900581c1c40403002805920403038044d00d411541c03400f40071401c0354086180c20160418007001466510980c03100c01e03000d0264103554807881e52001503028114241440089101d00018083ea9060f0100300c041c100703c0ca402d000704821803454640003c2420010107981c483c0408072a02c0041000401c0400d11034031004008100e803125003040c0000a5205403a420007550a110002070251f006101c1c010a49482c1620907145a42d0458010014452542c1412507003202e48440004102c04006008402d50307000b100143c1440740c0c0c28400d1420384002c00b00021980b06004000c1199040743c00385030140040900561500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 792833255 1250 792832005 792832013
    0x3011409210d020315100203070b01090e030d02040905010e0612030301180b12061605040b0d0902010318060f060909050318120d0c0b0703020702031c090b0c160905091504 75
    0x31065268920b0054004403d1200706070802865800c1031808841d52007841944c44002d980301c1c003c2800140c07882c0001e10040000c81100d4011842c150340d4a425039281c054000e1158080740c10540092110b40c2d40d440061101000d86117507250080f50840d50036040800790520280e03248014058100d20741500b0519801040160b00704100303070740000f010408440d4000940907980c40049802401e2010158501d0321082d00030703000c88041e0703010702084d60302c1e0010348a04000907254a107012410959184824070754001042c40201001744030b100c0208401d850080d040080e50255007240e0f041f40e10300b040d0a000280000120b40c1c0044070f418810140c0c940150009448404407126080e03140611350072403840580c040c0d100e40400b807103101414015100d40204901b00e024102009405502000c00803170200250301c10b2440413011031030704d054066181c01142105401100340841c0b95406007086030b07020b045c2211241c010b40402842003209103440c030300840d6144001031000e91951220030204080c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 792834505 1250 792833255 792833257
    0x140a090f0804120501050f0919020607120503070f0206190f140a0c0813120809030c030d0204081b1c021c05070302150c120306030a200301140921 64
    0x107034019440360340356a030f81c04011003480322148040340d0951800c070010f5154a4680c61080c010810280204040700c074100302c8103018401c034035083e68001000d0080e030700011041034517600b8a280ca13a4910b0b85078100300401030b041e115510410015500500b0400545040340714103200700300da00303a0010074800d08402851000b00f0344906030740705a1182c101001100f05441e041041c1c541c859965203c0307170340d43c0c5e03002c0c0c4401403048d40030003040c1c01808a16141c0c943e00c2411119008462102560310340140d82480929581c80341d40740f0041c264010504000855040c41000314030a2441001d4100040c0030000528101c041c40d58074035270740c041d031384c0400c25510390304100344052802060030100001c80b800c1195903690380b440200d100b000c101108403c040540c20030303200c4011849000f0700d880e8440c25828044d40d0402016280c16104d81006c02c0d020644400cc0c0003144000d4461104841c41d0080505094420804400e0984000750043c00b0000388005903040c07080030011081c0710001c240d0b4000242c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 792835755 1250 792834505 792834533
    0x31b03050c01060b041e0f0605071416050a2112050d0f050406060b18060a0e130c020f0705061b0114040503090406270c18080c030d03140a09 62
    0x900d43c07800c0b501050030300c001030080054a24204000b2000030351282800c038190b0160080090b1300f030541c4802c109031400b40028004007440381e500318180701d100f0b900383c0b0b10304241a07a01c2821b000454a081225007049d059030000351049840f42c04168007a201017a030b035520b401d500100a04070051729406281e01c10810f50f000e8041d0002e0a01c510600c0781c1c07407d0060301c03040e90103030f8030b0901c2c0c85000524814003400306d940c134222141c1c1c880405040441085003a402400340c103030600c684148441c2c015569002880f00c50001c05000140f44003c0081c024a40074205c000d07400709174030058040c42144c2c0d440342500e0681400908003403000310200090350150640c5105c0701d90301c1c00750307030288000c0040c04400b0f00301c4440f041e2070400c8059034814018808601d0326111646440455001c654000f80503040410b403401541007185151002a42c2d54104c90703016400141d07260814052500c0d00d1030103000350307030680712980303002d000e003450b984d469040300c4501400d01005549c3e18020b4000b003040640403080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 792837005 1250 792835755 792835777
    0xe010f02031e0c010c05070510021305040912030b0103111c06120c150e0d020909012009041802091602010e01020d0c0206100f0512150106170901050103031b0305 71
    0x10290b0410800c1200e5044000700340310765400d04101401c5075108000b91600c00c1d80000c02030491420070b40500000f540402003515040840440124a94445008003c220342c0305600c0c03000344901c1c800d40182212120802c2074101420040e520501c0c0990b42e065840c2101601900901140700c0840c650060099900480d402d88082c070720070b800c4c8049030201c00102c4403600c01d030420002049104030b850941c00c000d402c0d032000b00c0c03c03110009403c0c00d00c5543e45c0300c0710310000018100030301000009094014840744058410003d038004590509000c0d240442040e0040e001101029600142211100a01880720020222000907070316200f50070800858140b44002c45d51001c2011194024021a401c004051700c06d01e000700701480d04404065049408250b082c031840350401007003041850300d606c0035001c3c07440340020050750928007070310440c0241500e0f01c521010410811940b0701d1201c0c01000d1000591400f401000401d030003070301c1c410b03901c11021528071420015103002c1c1c88601036100045 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 792838255 1250 792837005 792837037
    0x50a17041112030d05010807030209010b040807060f0201020705071410020a02060928090606110d0f03020d1d1b0d03080112021c050106080715120203060a0803120601031b0e010f0203 80
    0x1f451340340810b415054030300a807000e103644da07240d5007465001e00c168861102e01d0381c05024200440b42c032812501a0080b8148000341c07038800541c658503d0841e054020030020451035003c0f01040c6004000941520040c1c005401da00203a030b00060300c2d030700682070801d00400d21109411651601c1c007800d8002048400000d00c813040e26902d003903000f4071044c0034060104e441d440c144040d03130600144100c049841d60b0f4412085a0744440100c1c080d410040c44071010719200c014000d1745411803d03c10480d01c0302c50008018a0b010036042004918094611034001c5001e40c070203801080c1d101001e603054582d00e0041600761a131610200303243c0d501020044801603c0c00c85e00c08100a010b42101d0110b0300103404542c0740315101c0f081c0d40c01c0315449201c4040428027241e141c2d1010045900a594418001009405501d41d1840c106003154492004270380140b1682041201960b094840ca41c501150303031030206291700c0c0202016009a01d1451418140030071010380440c210300c20012904c58003880c0c0300744 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 792839505 1250 792838255 792838259
    0x906071a13061a06091003181b060315090504031b050a0507140315130611031902040f0b1b010f0e060903070302070e100504020307050a17041112030d0501 68
    0x41400d0340368401c4200c071103a080c020802a0ba0014940c040610303c0d00529440c038001004003000700f5010116000c80605888034080d030244010b020460300d11902900e00b07501c03803984801c1201c1c000d6800750005001e1500c1c3c0144d500c0d0b500d20641c840c4003900c0702d40f680000c140c1c80da07040683c0c8040e43c036160080ba040f00e04170342008126000c15940d00e0306104608550056450f81c2032520381441c1242c0e000d4140e44200041107410750075000594102400421906060655444400684880000070f1850701d01c0017092215070480c0b68034002051400c00030031800c042c00c001c143c013614070740b601c141c0e44120720125a00740650720360106010035081d6200204064203444207518050121740000181900599000404ae50f10100032030b100180e040c0d003e02001c5081014002c02035801400e2140072030703150740010506440e0741c0300650243d032241c0c07a030a44811034110018803c3c040800f03140c918900c110b0500c00003d40121080e460140102c82c80403081d01850340c201c0ca18000e102c401e6500a00308000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 792840755 1250 792839505 792839521
    0xf04021e101d0312090d021c030c030807091d1f0e1b07050c0918010c2d020a290c0405030c0d050d0c08041706060a0f0501050906071a 59
    0x9480e03803442e4081140341c80745080100340d1945081500440b00c10b104000304607061429041d91960148003c2c00c483d041d100361715280c1c2410b10001d00440118135001e04080c18940c002020540c411120301d40083d0240c2040309160142c1c1c44103801701006400030f0003084040c1000a100b10f841488205a00aa180e607041080e07424102550010300001c02c2030503401102c032042d402c0302d80c2c80784c01c08001c1031000d684100380304020000610b02c0c0031641d0044080c0b01c0700350082c000c58603119400e544c1c42800111021b07031340c4000e14003a05015001e044076130340d02d0130300e80c1c021801b403051a1300030038184903248403445280d2045400080c0c80c40840c14a034100022003013040d02a01c15100c0a80444409519400a01c000810386250152480c4d100d45c44109842d03202d020b158000d08d00c03801845007401d941d299400740d940c05039000710a8641280b01003001c603007800101030740142071045203040b04914202c00a8520703c6031280d000c0c0a040001b44007420300c00c2914100c102c10b20550f034000c10314940703150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 792842005 1250 792840755 792840767
    0x1e2c180a030f0f0e150d112206080708340207090b0103021201030b070219061d120a030b0414010608040b06060a1e020114070c1a0f04021e10 62
    0x1400020a41650031201070724403e504e0206092805441c041d9179000c4c510890481c0e800c1901c25001050f10390b18200a8400031a015000c90b007021190740c04001031400e21040b41072000d03001401001520800c20070b15a074400001c5400901e00c0840441c41400400c1000002d806134066495025006c017000030404d42c0025400225508040b0401c09131007040011010707807280d0300c250380c04040d0410051021441aa500e00e0b0450840d00450310085904030100c24040c001c10001e5403610350321030301a03030341098120700048100882000ba00d0500c180400d20300844c0a15017086040542d85c0c0f0b5503800035123032580029290340c82450b1000c0d6a42e920312000701580000c48048420300d846202144046c1401d03c156810461140c580c0c1180b04907603079080700400103036080e11046648440800e01d501140010700c5000d400c00d03550b840e11004041c00c01d40211080000c90400d4010000308200100409044030358010358100c3c0e030b03100d1400002c800007130384410304150790754403e4409a0b940d1005810103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 792843255 1250 792842005 792842027
    0x18090702100e0303042a050d0f05010b1813030e090103050f2512060b121b01020601030209070e061b1e0d120f151e2c180a03 55
    0x11410320481880321040781d03c902044e01c00500301c1400303000034092410810044203212400e0207039140c41c03a41e030b0f100080301545541e80603101084850707040300500a0030300030084201c0c81511071000d40c1040d00d03c1802c1e180c0c00240a200d002141800000070144a080c212200c020001e240c08103950316804c040b520348408840d00c0109101c0c6038038120341ca03404041d186040500003034010044514280110103041143c5038121456a50762103c001c842c2d0701d0748004008408420010000c800c00308580c6040208904049415548841d0040005948035420a94442d0300b524208405103810340116031180030790040300c3e20784085894441c4009000003403408440404454075104039131081852503d505540041c0030000b100410b040e2000c040c1c0c2c0d00304103044801000005400d89400e280e1040311601c64000d04542d00c4031040703044041e800f07070b042500034290500b51514101e00580c14840d60b21390440c89003c40a40000000b210513a00c11914004038010724260303000b8a100d031800500380038000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 792844505 1250 792843255 792843283
    0x121110050717101e0306092a0e0606220e060f060304110f03070f03060b090105100801030605060616032f030406050d0209190e01091103060618090702 66
    0x588505110240106040d60003201444140c0c44118204a0010800c0c0c03501440e84d000c0644950300000060030911804103594056004400c591400c6808030550307010035440c500380042c0342c1c0d0007804000205151240c200404699442e9070382102c89003104020144510314580c1c511031000059181d80c0c080404e8032802c01100c02ca0300c94000c840c1001603a00007a078016002012612107505e040c05c20780c000c8007d016004040f03411042d03a5560400b80c4e42842e42040314455120003401210741440c0300c5440c00f50004a8082f0117029040500a00c1c010701440050040e175200c0022668649134141202c140c00581c08281d0f180030117504015000d25040b020030001d010700c0540c00c00fa0086400702c2803401c00003070301c0a10b161a161400840d5990040322040700a00e50030030400119a0745c0d0305120072080000c64007062014540303a00b940c11014140e02a089450600700311650f1307107038420100da9003c4401c0360103648910014000c80c0c2d1a5120600c4180c024032041e0a0000580e00001c0c44a0b8070500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 792845755 1250 792844505 792844517
    0x81902131404030e1512041a090f010501080307111507060c0306080c011806120617060612030304020904020d0812040615060c05120c0f03031303030608060708041211100507 76
    0x104509102c001441c1d001d2070000d0400070b11a1b0151500007841050300706014181c4a0628000ca682880d40031900360f40c50115507101c40ea09010304c2d9400c5c060180100308d910051b40c02c1034441d071154580b01c50708000c0c861107081305909040111841209503080a0340041081100c0200440c01400600490091356114442c44a01c01e000d988604842000d00b022255082142032030042c0540d1404c0303c40040024480d110040804c3d001124444913031010031050060800e41002000e02140e820704507070180702c6820800800c000f68440040e09504103505070b0b54140340c81140d040c0903d4074000c0103000100f03a202c200030700080c0a00798000d400c04055003104486040d80d2140107503044420301100404ca40c001c0014810b06201d003401074a00c144c008010b8605010307001c14400d003140e100301d407800d500d100071800c0101455030601c111005010044010001d904020001a000220040c00200052804a40242c0c140c1c81241155140c0420104803101d20700c80c40d82600141100300d45150010711 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 792847005 1250 792845755 792845777
    0x3080f0d060e1012050c01120e010e0d0f17070503180a03031406040e10050c07021903031e022d2d01141f0e010b1801030608190213140403 61
    0xa94959030120a40c17260040820811120054078940c100e00f030403d0301c0994030703440410451020301921036480d82c02e00c00f403e56581400006042c0d002e003a5610310401440d0b0500410300c10b803500c030343c9030081403a00341603440750b88070486440f41c00c280c0c501c01a03580c00f0f6100d01c0020150103400000040b0056000c0f18140d50700d4000744801c40d40c4240d801c4140d5445104038840412195001c039412851056184e0f04c0c00342e107600405c0390480d46040245180d01894010400c3c1503119400650910502c01c401c02c0310f641c400c03030080d80d40d940446008a020342090030740881082c04568030708040d01d0301055558103528405840b00000c041810780d55404c12800d000b01c8581418890140c5448150b82e4201e450349490f200302140c000c181c1c40c500c010710260040491b08143e980d2050f8003e2560280c0b041d52221041c808040c2e00c0d52150341c0c85d06050514105004001e0003140320849803403002d00d400c16013091400028a0712200780041c001052415440c521100640344909204501940714040040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 792848255 1250 792847005 792847019
    0xd0207030e041a0d02210715081e0403080a062d08060c031f0905040f1a010303050d0905011d030408121e2b02090a1a0403080f0d060e10 60
    0x100c120300c01d59400503285801d0001860010103440c8000e10350f50382200c06c080580200b0b407515049400030311001082d01c5040c500340b40d01103032003070740071294919084800406030610b0040100180000f400c1c09504400500d40640541c0014010102c41c4883c4880b0103100c2e8a4010900b40c1c0f070030520346000800d2011031a1840050054010400e01c2c1b48149540e5510300b175060001034102e00401c9044500e200060351004500030746000da80a2416110140c4251901d40c502d0030920503510f400325020001000800c5c0c00c03506a40c4000d9400b01d02107062685840c00c00c0c0189004013844c0d4a26198441d2071400c2c40d00000580700761507400d4100c510340225050042c926014002744181003200381c04400060b129500090224280031a81e03516201802d80000543c01d15803420000c01586c0c0820b1500943c900310b4008402484110411080401812149441d51013140405400380400040007016655504100c860406820500f00140c0b82c0710081d4001c1c0803016031302a2141405c2c2140404c0c80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 792849505 1250 792848255 792848291
    0x6010f080c030c0c1608070f140d021507021206092a0103020714010c0c0c0609051e1203040305011a10050a030c0e0414162c060d0207030e04 62
    0x1e244031003100742160f441080b009015401241284a20700071200c003403d081840d03c40010180c80361501030b0006134100108182e900f00300e580f0198170311139038041142c0540c5407a444610015010786075001d0704407107009980d00c28802c11070000d4101040012030103500700045650780c09140b6800039100c12107804032a6941014043c2245408019140c80d110901e40c001c0d40100a4a813050f000e40c0c0c0e0402c1d100305442c4c01c50f204082d041b408900400c681108014100b154100034042d0b40c14200412402c01011032581c0d04900c030221005081d04030041355a549028030f605016081d9803c8a07951501d901d01507000c0c0104e44480c8400c102c040040c0c0c00b031440c000b4080160040140d403064102007800c0f1040b070180a0061044c824082c60055102c2c032511240141d414000003003505c01811300703111500c075180e505000700000c104201510281c980d03106420102c1c01a0500840000403803459030700107001d511600e600c0c1607aa9200154480405800000c42c03001a24115400c0040ea03140216103001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 792850755 1250 792849505 792849511
    0x418051501020d20120f0c100c020c090406020c03040308120a060e060d0317091b040b1807111b210d030c0201060f0b040e0a060e0402040509010209090f06010f08 71
    0x844c40341400f80400304074800c0114414814241142e18040f40f00510345210790102d0200340520744001094600c40c4c104106182e500014a0001c02600031a008025106c106110055214411180100e42800304540640300d0084041080d02c1d511a543d02e40300040303500458000c0d26042100d400a1898866449402c044981608100350340c2c0e5190f004004203007805403001c80601c2482e200c190181c0b09a15a56485105450001c0c1a18840c4000807075040949413a4144528188803a52a143d202c2880c001030003429041c0c00031f15521400303400d0b10400c2603607007251040c0c405c00c21107451142c2007030074039689408143c0c0e5486943c959070f585105046540030940c03a02c1e40c480000c282c1614841c2c0e00c03900007040144000145142c0310420701c1e807013200c59440b0750300c407030800b01e0144600b4070f40c2c41c15140c1081c10844100006407500320b00e10448035008001921582e81d541c0040e055200a4044410207007005001103150700d8800c0d07190b100c0b0075040c0c41c075600040342e003481e4460040c022071100b40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 792852005 1250 792850755 792850757
    0x5130b0301080c2101091412042313020a0e090f040b0420060d0603030e0d050a0b040c2402010e0c010206060f030c060417010c0e0919020418051501020d 67
    0xc2403003064030a019216140c50b004140901105603105a9460b081c41ba144040f0b209403686910300341d080d5269842c08005011340c003481901003004001c0b03580d03c0111109684080c1e00644902c0080000080d09940102204011280001035039240c996108080d041200d90444951001d603c03641c00e400c81904c01124020201014000805d0119a800350042d00c40d01002c0340080403000e000c0c0200350385411899040c46540d440380418020140c01c2640000380d00010342d1705401106660711003550306ca4107502c1c09040b08410700c0c003003000d000040d51101d025104d400302d001c2c8880c40d030359200070050311403100f201c00551038008002180c079004190003c90000c1603008100ca503d440f810081034182c0c0141c1e450f41449800f50715602911a080644014411191280c1040c03081101c00c9096401492803001000002129143c05c6d0741c9a001480e00700c2031400b1408003c1b0002a072142c0244150f42100e440c454841c14200444020340c1c02141c0310b01400742c1c400901c0f407a50f03401681c0c0c90303ca40320110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 792853255 1250 792852005 792852013
    0xf070e131707020406230922210219060c031b0507050606030606062a060403020708070b040e041101020f101a06030606032a160320060a1808040605130b030108 70
    0x706524115440d1a0050100c0c5408c09880c01e0b02d10800c0300340541d00408480d19070220300c030040760f0f0f401d100c0340380441d00d8036001821000c01101c0344100d03d4003400100400b01561203c2d41c00e040391195001c4411010000ca201c403000002c40001f8085402c003040407200781c450840010402c7c200421254041d50f00076001600302860b4505032540000d2041a03620065642004816401020801c3e0b9004a009402400659041038a081d0920015800c1428400020001040b004486280003540245c00240910350740e21600c0040341806c0c03a00100d407400b4821841c008802c801e0750307809504c04e5030907940341508252110092000500080300e15a03801103007070001440151088104248d40303031318511002c3c003103001c481600005400010440708802d21401d4150304040e004100c126100c0415000d4011303002182244540d1840c0041040840d5501e07402000c501c450050860b45a06a100b46015103071525030000810035004242e0030703d11043c811078009407100c134200032681a101118064 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 792854505 1250 792853255 792853319
    0xa270203240a0e030d0f060806011a03040204050a090c060201240b0406230c0304060311030907061d06030a0c020118050303150a090e0c010e030f070e131707020406 72
    0x10010b10040c0b07442c5200c0e0108124405c0180e690f40309020300f102e00007100044481c24081c5041c80c041058001443c0e0b2100b00c0c07620501d010b5641c033500e5100d07034101d81c007055941d501d90a0300090090035000500b0b02c00105400708a01d1380642101301d55a00da40300942c2401d4509240b4080c80b51148110000f0b61810041030261520461607221241d01941c0301c04d0320300122075210304407a0b01c400700c9080a42c1012034144801503250090444128005402a045080a00401d901c48e4078511500c01404407a079008200f15280241e000b0f140c3c0401004076489240655880001e08181e45134240154079040503510a000c025100000054201c8010760443d5203840207003000d2100103109179070244401d40001902c483c2070180400186841014140403040500003518140c64081014440c5c0c101401074100248001901c00444040103000c1d0000e458002c00b07121a15031706400608981c401c92420301c1c40182e004004d04005109403020424181c1e200c0188400c0c071600e10b02d80090250b20612 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 792855755 1250 792854505 792854521
    0x130c080f041a0712050c09010e0d02150a0804020a080a03090b0904020702041803030f020415030b060c03070c14150909060109470a080a27020324 64
    0xc4680c441c0c46001da001814080e40a00403115030125000700000e4138582850704041400c1c01880d41210429409038107040090740042c0110421100c07041c0a08040300403801590341741c0310031550900c41d029055030390f4038104038014082c01048409a02643c000f1000140c4c00400003400d02116400d580c0314000c15040c58501c3c4600c3d40b14180988d4070640034041030025030f440740301e05c21030584804d100804042d1941340c040c00340e07181200082010b51042c8030801c030184182e0400045248a4940040e00803030860000d81c960140c226603503554400414201c3c1044000702d0510240c842d0484a52020080d035810400e41d4404030003030103000d0f0300900009400f070801c10f035540c0c2c200c401410320021040c0c807010b03145d804c440710004c4d01910070900719040c1c180d42200340848043c0d001e40c4003510540c1c22518001c4e803903485945d202c2020880e00c040001d007405101d50004c0301c10020f09600c2070003a0581c030f8010115290b1000241e12034010f000008840380400304540c072240c7c001003802422950f070200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 792857005 1250 792855755 792855781
    0x1623010b032b110316030e0f011d0303040e161413090b0d14031804060819031403070203030103061d0c130908040f08010608060709230904060b130c08 66
    0x8442c0e01071200c542e46111540d002030024042040b054031041c0890105802c004140c0711803d410f03035008440c030200d03030a1140da00c441d89410104c61940300d1201d0200210129281d4030032613105444041200d028000c119101f05860f00c1158110b64440d40c000003d004403402d984500c500c0080c2c000c100c880204659441c94002410300700e001004540310245d6915010511024011806415080040d020300d148018035a1011811001e0700e04010310340c202086c1c2076907803101d4021030b4141345560b610307070081500c21071030103603404c2070404d0b00b50b00c0b1b08100002a40d2038000b808211440e070305044035105140f00f410680300540c110748006120045490007030000c0b04401c41040c060003520f0302c201c100421240307001040204404ca2642c00611300d03101d1001d007125103a4000c0301c2140c222000307001e001c3d0780c00303c8507109941503c1d55280b102542c60704180174000146d61899080361180c010001444655401280040c40a0b50300761410b01011150404403039210240001088609010901d074110200c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 792858255 1250 792857005 792857083
    0x5041b05030a051302040510090c020f03070803101505071101140702041d0102120f1803030c0a03150305030306011101360b09030310090b0f04021623010b03 69
    0xc41d90004e500c0d008541a0f03103084544100a08180303a041003000418403420307540010a1001e05142200200030039200d209822010700041808000310301c003a008408000000e0501148a0003909000700015103980c004850a6801254500340341c001c0754040d0b905c484030940d028000700d161501c9a07003080001e0840c814400b4451900c141220340185d0240700501c03941c070302990412218a8000060120004003c04014100d511000004161030002040e43e41120360200c0040d01c1e601c00402c1100206824102002c04031020322000040c00703c080001e40c014042a0b071341314070f0944d940c0400d07400d8540514645101030310700300224540140110f010740d920041251180b6080680e61540b104084003070301d401c00349030400010300001c907915414020060960800502c138802c4200c0c00070307001d48040510180102d4000480c44006425400220011588418106554030301320000b881c41c50b0000018181541c80d14900c0e20301860001801c240300300c9180b00c460075400c007082150400000d15 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 792859505 1250 792858255 792858271
    0xd1404050604090f1508010603021c030e0d17070c0503010c03090503090607080d06090509060916122f01020111030606030402010e0616031d190521011505041b05030a05 74
    0x717500905012040c0540e140c01009074200201d05281503004000c0c0c41c01070040303203403054460b0741d01540c002500a010840040c800f03c45e00d48076030f01741c0d05021607150f00303c1809290201c8001142c40030000340c0502e00d019035100b40e008124021031000241d040340c1c030100b0040c19991050207491610b00d8298010032802e03110740481401d01060581c66004d0f200d5036006620001d0319803082000e40c040820400350700094140080c1001580701e1000c040120140c00360240d503d0703480e8515000d11202000d00966840140b010020807411030a90b20f0004950320001401542400801d40340103140300300756402100003c203903501d103484650055a0324462460003642001c1d052009180c4481d00304006a036483c025110100040002d082e4102c02462605010b40300354454884840c140c0d1b030000c160b03c10b0303440580b00101e1003000c0070040509148541c0d20001250709010300426607408190092040b26802d6070144188002040c2d2400c811100644080000700203000150741d4081d140c03c825000080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 792860755 1250 792859505 792859511
    0xa05040504060f060f081501031d0d02060103120c08031909050a0c062c0d08041e15020105220c0b180906012a0519050d1404050604090f 60
    0x2540c03001c036055032010b42c03012091103d02c010030402c1c907400007940000a502e5260a0b2118504600b40c0103001c219200a20304140c0d595007006926000860034154034580703a0120f51303020a68810095844001b400101d03500b510507440113003900d02644010704e43d0365001102d07500f9661410300e403008001e400e40c400404541c544422030b000c290140500b910040c0900c0010700340c02d0528901508070340b0b9a01601006000d2070003c00d80311030480503680a00c500844118130740f080a81455151030180346c2240700340d40001c1c500350505140d1181e02d10110703000c8134059141d411034150281d08a0304215031121a8600c100b0305024a92051018000c40034443c54683d00d085032074028074101e640029420603402d0000d41000c0341c1d030b80340512074a42e00c200c09203400e20300994407500c1e080c000d46070343d1114201e4a80208648041207024131200003030400d84802006030218a0615643d1038051401440100343c9138400c00c2403030b0300b070b0104907010348101500061400d880d1505040c003c04505e05107006042e5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 792862005 1250 792860755 792860759
    0xf0c010c0813150e01020a08030127020301150806030a0201200a0c0f0303170705090f0a03050a0f02210d140903012d021216090801090614010506070c09020a0504 71
    0x1503160181010700903180e03c10302c049107410000390002100440d20b50640d40099440c1000440701c82c02c85e4103641041a800d08515000344140401030300c2100c6803d1030742d002000124644168400c81c038030010107a03487c010181c550509140c0c4981c101c030380190000303c0a0f0140e140644541e12243d01842c111412280c3c14101515801000d0016404c5000202a032031410014943d0150304001000401a070725005814649000340c80c40c13003027501141c02090810883c0d0b48503550000300500a40e0017400f540c00141c80c0307240081c400c00c12020200c2c441ea2015510709428015201c2440d40c00601100400b482c0e00740044c15507040441e40061040340c0c004000340c0c000d5813021702601c031554480c0c04610a0a4500f04d24003045400c01702c000304011403040c400e2074440c44076101401e030803a901c0440c40080d82e1485070200d0720305429410100d441d60920309008101722040e0312450200c28815040e011503622803003081058410448060b140c4d01c40d0b400144816410342e03004044589507401c00f20320341a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 792863255 1250 792862005 792862027
    0x3040807140a020901080f060f070215100306110a050306010804080c010c110706021b061e040609080706050306030a030e2b060e0703080403030c050115090504140f0c010c08 76
    0x200500980711071900000d01c2c881c214113000324468050007080001e4a0320f820000c40c00c03966480003c01100519659601040d6124028000d48288111003062504940340861a4400140140c401100c5a901d00142c1d1441429500181c80328400b0320b660b4503286448440046600c0c0f0350241083c0d4130603008002c41c9403441024415820f00781d960780c1728840321100b6880c01c1030809400c1c2d03110710203641180410461181026201001c105800c443d0b89071282440e071146200d9503000e24801d02a1140010003051039500010f003142122442d100711121540c584008440502090303540d0b0b42c00d54003030b00f103100000e4040c40d58003e00010243c2209100703456180d004012041c003032040c4244c01c0c09800742c00140403180c0541c1c00c040b060701000300342091455032025801d114602c00501000b002c03040100c10402d00f0742000c44860355030004a0300d001d407202c10100081c002910700301da158284800c000c0010350041869440404044054582001c0f03480042d00c0d452040ca41c1100e8009040001c00124 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 792864505 1250 792863255 792863273
    0x20f0904030e01080a0204060c152d11091813121101140103020319080909040c05130b060f0f07020411031008070323011b02160603180803040807 64
    0x441c042e81e242d031000811500050407400c0b0144c071024900e8010001400150340050469040a0340700d1071660705191000305000c010007502d04410070100c040842241c05044201801d0000100881e0800075504113007907905092281c100c1c1650000344a10005440003002100c1c075501503850041c040320904555500600419102404000300365141403001e1000800d01c60340743d44d842c0c015078000f00c03075042d5000a0740c0ca0700124100030380300342404015400c11a120040e600402c8000d02440c0c140e040500d07088c40c80483c0c0d4051140102d4900d042c0422603000c5004503c01e401001d0b05041c50040804002c28507940150100410404108400c02c01602d980c407d942501003402d94041c0c80e41855030100c503012455500c10300d10790b40024018070118010030509281c448a40600712040540c002d00c20307002d4003850002c60200c105110b050b582c041d80100d005003120381d03400c0c07418611a4440c0700c294100c5001480b08031056519003200000658558021600a40544016801c007c0243d0310078800c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 792865755 1250 792864505 792864511
    0x40b030d020d0908070e0a180605070507170a0906180b0720010207080d0813140703231504020303070f0f0b010509060105070303052502010b031225020f09 68
    0x603030000d682c1540450b48114010050200309000e01070092421030880003107030f0302400144070346546010041804000144014480c0d502217010322092418410160180e0808101a0340d22401007644201c2022110203c072a0005e031502e0b106200d1381045001c80d141048400102c0601501e200040b0b1480081d60242c0b160350f109801e01149040700b5413a01240103064541c1034155881243c050000130360101e80840e081c050703450b0101a03640d9445c05201400c2d00004080c1580d00810540f101380c4102159203015240150340030f855106000201866a2010780f90340c25640d000841d10b510307150f120001880d0894002401ca81c20014243c45e07407401015904001c031000c00c1c0f01c10300e4000b0041c40312560b80c0140000c6400c60000d1400d1b20006c0c0581c407070f1b000300808041c0da800001d000a00c03031b501820303d031210360301200f1800100c0d1200640200701203141a03101e440380c1d4052400008a402c105c0da1841200c7e6850880da500f41400000c1a002d6030ba0100d034414040513a030400382e1205084584 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 792867005 1250 792865755 792865757
    0xe0d1809021303050f03040b0d020d06150c020102010b0306130311070506030112030f030203040f02130f0c090e060906210f150402190e130314030103050a030909022502040b030d 78
    0x1540c6443d5180c09442c1c40d5019944a00c141c00621007003126418100c2a12034060320320303001603030340c4081c1d00c42800201000d81080188400040050420326801110010341d41e200382c00070860502640308056880070102c0d90500b5100100200c080042d22680d203204000320b0001c211356106449800041c01504260810500342410b000301009065003c0c10320f240401c1581011890760515480390b20798135201d1030000c3e0081304c00d00481c9040300c2c0d0039408040c41900d40041048100c02580c001060741400744200e840024400020500d42e10b801041d960003400014010903490007400541c40000a062103401018040d40303007041602070007442080c0c02e400ea08034100e0510329082c4104000c80c080c0441100c003840e150308092084040c641007284e000300200084070032410f018a0304075114200030083c0710600c0030120001040002c0050840c01d5684241c03112000c054a0300043d0040b0300500c40c1e60b8001352440d00c15010f00444814070014000e00191000c200d045040300824640111101948 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 792868255 1250 792867005 792867037
    0x50307080f0f130519111809330109020a030e0609121c060b03070e09070c200402031501140c0c0f24040e0a0e0d180902 53
    0x5841680828400d5101403014001025070a00b0111000d02d440c0043c10305070358003142d42c019400d204c0e0030040304038101002040400d5507074151900154201207040e210340034100c1f8000c6c2c0825240308640c1244038041034030003016540001d07007000201800740ca2500540c6101c0302e10300d60444481c028810302a0490f480e0141c0e40b00f00c40c1c81c0c01800c580807070003030902035008203050119000e404240c00b01a0071001c034246859841c1443c00741048000b9141182c4100d00c2d2620014101c5140005148249515104c1e205036042d139801b03102d452030341280c1010000388940e911070000340344000c1d0b1440290b0190001e070f110340350100108040382d0050351a94500052659103031103641e0b0040d40c0d6074041c0e8000006a00b8503540013181d60b91880e2001585100704ea4004603000e00307450f08510708000d42d288000002c00c00d0030811142802d64841d0140a4148141c000020516542c9015800442d80c414008001c11498903104a400e6000c0269008085006280000c0d481090303002500360806144441 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 792869505 1250 792868255 792868261
    0x403020d020705150306090a0e01092001051608030c0729060109060203040e060f0a030c0f051504030b06030a080a110c03010507021203090c1801090f06150c0816030503 74
    0x3a190900a81c0f1080c892543c41c030141030401e440c101500c2c0c0025003910600e4054a80b4505000030380156011280658605192441841070798a00e501202e403030741a1801c81c1c5000324004413540e03c61401003004800c64001400006041c040c02507034407488800100e41086071035a280c440308204180107024214150320314880207000303000c0c500d030440004d00b00365246501e4060069140e020301d2085042000710400011044d84600c016444055001000c0c9201c2503180c0c170b0322030320280860040d80c8640702e219030040313468140b00100c0700e0015180706500341414074661350820700c400010885501030103025200b80000312200040d0054043c580c03204803049030074801040c07400c02c40d5071341c80f84030303a04200c103018440e50045000c180b84100d0503000765580d501c040340c040c03905020208040d0400342182802d018131454100c000c1c184c0d45c1070f000034043c01c20070f030700a0130596456001d140d100300300c009507039101c2502412301d4442907482402424100a100a1440c0d8036560018098010030000820 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 792870755 1250 792869505 792869507
    0x1507030905010c03050103151d030c070e0903030105060f031f03060e3a05070503190e0609030706030f060b03010e0703151d07032414030a1a130b0403020d 68
    0x3102c118408074a130421141d0b156448103aa03038140308206004071036a4079681414840c001e501c1c180601c45840442e581c0d03080c0c500c460766481241e8401c3e0703d0080b4001c2d000c43e00c445808005c481c12100014451824611a5884000180d001401c440d0022840e0800020341d000d840e1281801107020b440700050706440c4a0030107051003c5800440340b040400702c0c3c0c0265034024a40c10021500001c0c2c8181ca5507030700d1504c113070754500c40d424014160b8440402d181400090600b615404168075a569040c040c542030140701d0b26000344a40c0c55031640003c03c0500c0228402e034491803907001810340200e40b0543c0c2c1d0f507044146d40d10a030050383c031410703a1200308050302d600340c060300700015410074400355624a80704502801c081c0c814000083d07a46648003141c0210701c250041c840c91074580d40941550300c0380303200102c00c00c8030b644100860146001038002c018540801c0404100c0e4000c940c1e0383c940c1e0390700040c0341e0320b91000801404e02807400c0c4980c200400e50061b44584150b03c00d40041120b03c0c120b0304 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 792872005 1250 792870755 792870761
    0x7210608060a02040e0411040b03120301081b0d031d06070305271f0509040204080c150c030405041e0c08040c0e01030305070f0327090608070608010501050c150703090501 75
    0x8071902c0c49900412040101c211134201255005401a4502c142240c1400015001e843c215110503454403d82d4019643c000058004504940c8074404032140103840c80c0c1d50021161810203a540c1c02000b0610120100c0c0c02001200f032105548007800303510120401c00184260440581030380050804143e515000720000c4265180f840420058030f0b4441c0701c0c00000b034030230aa129a02900019080b4010b5060f4050400da40780b24400031b20a5480d0350325140100c2e61024442c0e103d030310464003100f451584226a204880301800c0ca6400b0b145400d003010103000280c80584410078901041407142e40c00900e4503c21800801c800381d03913040040c1420b0503e4400320013550801c110800d889001000001e81003c1100e00e075a501c50000341d48500c1e00d0400355500261401540c891030000b01007081d00c19560f9070490300f17a0341444020040c05031200b1710b06940701c80364050132001c5007140b001800950b01902c007410360317400d2010844002c5070000d0080c08100c901903c5c2c003008262141c41850802c4803c2c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 792873255 1250 792872005 792872011
    0x40e0f04020f10050d1803170c0901030b030a06090602040e0c0f0901080408071b05040e060609010e0402030a060c0903210c0602220b090a061b0b0721060806 69
    0x4002009800d103900080c8078400000380c81031044880ea40c42c02c4995004030160340c440004800e00b00030321004880ca8401654644d0012030015100340761281e51506100c10041c041c05101d102d40782000702813401500140345003c00e00f5032621a41c18044000b074403d0041c2d00710284561000b40c0c0700c81c5003c644c005d1050002e0404030441c1000c0c412000e03900360b500152405d1040c2443c00e074400c3c2d101c60902451500c148500581001da0f80130100c142c0d62084514030b000c5400c00e9504001c0140039805441e00c2d4401075604640c0016040c0040005603000f90701641c00074001429580d4614803070b07868104896000241002050048204000b80107000b103c0c401c5c1d40c010f0328000120502c03c0a402040714104800c002c11050380840d441c0356251080c1c50400e040011280640d68040e11040e5119668010314a814403a4561071008114a441908100383c000c0c9500d01c801c01c030101541d60280c801000810101c108403410b900d04032071101c40c80b034040f0442e005403000a586170411850f070382440c0000b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 792874505 1250 792873255 792873271
    0x130c08060307080d05130302120a03090f0b0306040b0f09040f022d1e06070c0e010812030c070317072c010c03030b04090b1008010605040507141b0f03040e 68
    0x2040b04000034080402d005104440d40e18285640700c0f941c00c0010030311609900301a4015003549014110040c002444c2d80c030040c029203030b00b0f031420717074800030a1b50a0f40700c0d01075000300342c43c05c0c00401d0650416070409400b0728401442d002d9002c02080100300b100c0ba04513820b4076202141003941c0c0641c100020119540c0c40d4041503100544255003504103c0d080100e00d560040201420180034031001c03d092680f21400100a166a545d250810201c0ca03001800b07051890050800002100d02d00025044400c4418000090a6950b040381a0a03103400211040d4244165440d40c41c421804000d00310780300344490f0f242d0002e0107403c0c1d600d080c2401d04a80355007004e4500600c500200b0b0b0f0b0040075009000d0390514010408521800203e006004a180c0052075603410109210701004800e03080b40a4be1400802001120f40d11400c000582d5001d46504010a079403140d294444520140100121203000340202c150810a0903820310301882c5140b007007095000818103000082100083c2c0f40c1008407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 792875755 1250 792874505 792874513
    0x102042c060102120417070308040f2103020c21010603030503180c091618062102031b072f01090603060b030a1e090f140d140a0e130c080603 62
    0x120950360302c20b12440c006e2840ca100c44507546264007504201c060701540d03022031140c2d262552105241501c100b903000f01c80245078940e0022070601181d0020501c0c071b40c0c00d0350052030088800400d01c50500008486c2281c155501e030941c840e0f00c0000d0151200952095413002d40e02d207001100180d086810800180c010340110342c085056980d074114440c2c200701401101c010142c0410010b0790443d040c140300d02001d50622900003411a00441d50b42414001084c4c81c54104900da0310310001c80c442260785507d0000c100240800300301c4a0009172101134070858205040384030010801d1140c4400b80185d04007880406000917079541d02107410030040216060612856041c12220003403030100404050025950b6000b0380e142110901c04c0c8004814451420000a240781c2860306034540d900b4000c0d60070100d8050b81841801000490b000040202c4c0c0d100810b02c00c00e01d1044450350b0111101c501000341519180e411551021811940e080c1014000600d818869a000d0614013000345614802d801c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 792877005 1250 792875755 792875773
    0x3120506010309150c0302281e080a0906090f060c09051012050901091a060103060e07020c0f0a091104090b030d2001090812070206060303040f0509090102042c060102 73
    0x14000c0450310301500d404c0040b81102640004074000d0040c00380050311030035082c8244042d6140a50400c101c07401b41c2d521100400c1040058500030f0b40d4034203801c1c0c00520410b0024901c05e50650005900750710038503002c20102001e13114081802c1003c80151050f41d03407241c060002542106506005000070b503040a0701070030702c140181c00380d40442d1451074550780715030000e000c43d070081d401807031141c1c0c2c01310b8088000f00e00f41d455032a14443c00c903140c601003440e00700c0200d0501701034041a846840c00c0c1d8020100c10300c0781014000c0101803091025001000494003156200701401104000301800e81c1d55525145085c8502094410715405980079070402030b0a00802a030200102c030506000c840c140c2c14255020b144140140300301c04010704425004280040082c3e0309003140f41c0501d04c1642166401e440d131030205602c034031940c41544900c40001100308018280190030907403007082c1200041c14035030717500c1012040754090b1081e900702c0840390300c41c0180d0300480c5404a420501c284010700c02e0790 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 792878255 1250 792877005 792877013
    0x16080912030c0f07050607060b061312060f0203130f0f05030f07060b06040803030f090a020301050c07050d090e060d111e15030f13110316050f011107032a0303120506010309 76
    0x1c404d411025104a80f6800c1518842d12b0311422940c1200048811860940ea0f410340d4400c0518003110440f03000d8240481c03071800c2442802500c1c0540b00500003030000b10355607503c5290403003142c101100c3d002d40030b01d038140c04103006002600c15040d1602080381d40701c0031454a40f04650b420540c0300d02c030b038200340b00901007800000140c03940880000c4580405803150b410f202e01d00054010001d61660820042249403c845e0001c0e01c2c140b84034504894421a07a0107090b00d041149004101c4521a14030009200d403030108080385820340594a10005a201300d00803c000c5080f501e04d24444410210b115091410400c01070004210b11021203411400d200003200b07008a0054407501c50000340b034062506103c82c1045070102a10024202c07050680e500e814554402100e02c0340910408951107110b01a500808a294115000c1c10107403600c10704558552030800000002d9510182a54000804c0d500301d840d49800a54002c0d11990307015207200c118282501c1004100c0b504050130600040001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 792879505 1250 792878255 792878257
    0x4030c060509060d05010b18100e010e0a210c0b030f01090c03060e27010902031e071d090c01050702010e1318060504110303030c16080912030c0f070506 67
    0x52025481c0103076070381c2c003081d00161450041031100d001c01890040001101c40040005080d82c48050704c046040e00004000c00000710081143e00000c580c2c280d901c1e44256106040502400c40000d20602070961541e0114a50f0403070401e100094504015040c01440302b900c200d01c1c01805004030b40e80c030f146801da02d41e0401d40e0041c4a1500c01031785030707001c410050f0f000b50020005048406180c428600d02600b0b002c03411030070003655524400b42c181c5240060b80301801000d81d40e40d0040c00038401003201c0301c0c1001150f11122074400b11401004004aa214501d411044444031420340880544c10050740041c2080c03031845031141404000c001c40c00c0140d0700119503900800045401c0c05804610001e1400580103680201c84075250b0302c42d0314400c0014581c8150b02890044149500e09285003062540d2484192030303c1d510902c0c20702c1f401c03080380e0501c00b40000c540d116810050400c03c2031400328111140c2800420b015400110f0008a4000108000d58071400610300820b0624a0000407800c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 792880755 1250 792879505 792879509
    0x3030f071b0f201e040f050a1b050f0909040c05120f010b09060108040204020c12040b2104111c02150306030c03060115031116060207030206070c020a2c07030b0a050604030c 76
    0x40c806450380d1300c019900c41c2d000803c0360f40c0e51041070009240c0782d5165001401f403003c02e0442411803000c6502420701c40d00036039428034582070b040c500d80b96009080002d81c020040049403200602900428035031a00064038554424200091490900f010207203070035903c10784441c0d4003c1910a003000001ea0307125080c650001d0f010f540041c0e4920001340b03018146400b10918828010300000c0001d42d02000000400201c59280c0502800c000d0f400e040402c50701058801a003104c03600744002203145800e1040c6000820103e900d000440c2d840e502140060a441c4000c080c041c1000c400c00a550030144920100710008502070201503040c4544100031a02080c1c80100f0541d4032803180f400140c0c03040455128280715144812a0742c0c0f1403508802035403150500310014082ea06c0465036490191170303003d03100c0758001c042000090130421410700c1e600700c4061f4610060701050060840e02c000c8408140108415078021803480250000d2101c00d4034641d11590255000304001c2020502e0340b00c900b01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 792882005 1250 792880755 792880789
    0x19030b011b020a2d030c0f08070b0712090f09090c050d030c060c090506040e04300c02010c0b04050703020f0d1a09030405060a110d1103030f071b0f20 66
    0x500720080142002c13210305603502450360340300d80003404000d120601110f00e003102d203284030b2018101e48618095448400d140700f18645030500b80710b10b10009240301400350007912540362048020ba610300c81c1c0350201040b5400700d20500d548030314000a1000c6000040047c0c2002d9a070003400241e030b030703500074580c0d2030103440036040590b1540d003201900d00c600d25000042400600103903c0381d4130740d0014140c403603080e1030440703980301007201198001c84a9120382e8030f0fa0810000406402d0161002526842c48100e0101c2c100540a4030302c500048004003490b0140340200700400d162400c5106006400c3ca540b8512445041144042d8001881100e40d00201141850034540d46440b2100480d103903001d56000079078040d10105804000c184d00c440490b099106210885140221004090350981217a0b8107480050700200002641015081e041c190445c0f442d19100c062400c9040c204c0d408040692412280403000303030302c44401d00124203440100703400301c62416854034083c01e000412000040303011013 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 792883255 1250 792882005 792882029
    0x131827031409060c1f0606120e191103060901060f0918021215060a050619021608070e0c030f0105010c050a05191b03110f0619030b011b020a 62
    0x2030001c20a0703040e50a215005045181c4800d4201c110580750070030100018880c2c0b128001c03403152031741d641c0100b2080360b41c80e403521181410521241c10143c218440080228414030b0009601303140c0440100c120f0b6406041c0032495080d182c0d08260402c41e024140200e1681400c01c00e2250a83d814504d00443c1c2c4450300014001200d1030080d00006800203010307520185074410340510701008506800303410009a080c0d41e860346c803a420000d030244c050184541041d414484004100d02c1d41038809044099030045070101480f00c8044014400590007291594020f52020080d060344c580d0f004d90443c55820100703085213041200d040c1206814445c0780c0c1040541e100e210180078051148041c070a411500303441007440c0e2850600004450200b081340c1001c01c94401020250038022100c0603241c1c0100318810b0300d0901420010000507014032075074852000c02000f440300d5003002d92890095803548020440060007400503228065150440a00a8240414000581c0ca14030b040c3e041e43c1d05416a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 792884505 1250 792883255 792883277
    0xb190e010914120a0f050d03020f0307080a0e120d06060c020d020603040201140c061b120412270602010b030d05030103061a0d0f05010f090519030513182703 69
    0x4000f0405011250150f01a8800031020301030241e4005400c035014104659111103481c3c405c0b8100d02c5218403160460100b4000b14100320b104404c095000324a0200126900960410040c01c10059010000c1c0c99400043c414016a0050181c1001450941440c0c607540c81140c01242010780441d070000d101d84000000242160302400c0e602e82205108655103032512210300940c3d6070b45030241c402052110040540164040c0704400311000e504410104072040d4075690344480122840603800014000b202d0100305030b00741c482e88800070200b40303800c40200d19450150040d085070f216624850207900440d2010301d02c40c0d040403c50341101d900a20028505030300030510030541500400059001a00c04504810710824100300c03501e060140000f0450b18003005c20160403201300e000002e00c9508560641d61900c240c1c3d40b02044407a022b81011860510021040a000c14590f00080d40c582078180d030354440182184201c075204241950218500f20384142c0740d00040d6a95040181040604001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 792885755 1250 792884505 792884509
    0x10b0d0e0610050102101a04090507090c0207030c0b0a05030f130204020c0102070b0106030b220e061e13031704060b100906030b0a0f031712010b190e010914 69
    0x1001540c10316800d5035600e040c07400d03040c0c042115070f209007801441288141c10030f410803440b541050010518010b0002e51508080c00044c0c09a0358003500c45001c2c948001034101694084d07581e0104450303010b00011811840d0003800e0308101c1d0454001c90806002888156030480300b181d801114044c00292541d0701c00540c8015110358140094005001145403e0a000150003820f0220722850003181d2903038807404103c045030710b02e20410303a0018200e605040421074861502150841d00e190202e420040d1410035803070a041030b10030384c041c5007040c5544440e010181c45801d8120301d00f4080d41c05156001d0318010f08000d196605491200301000201d410032029511450407c680035142e503015160309000541078850a2007000e010a040203968001071030080c45801c2034800d0070b85801082e81c1907499a840078801c044551282d00f80801084d2070007508207895074001c1000000340e580e10f80c0f506184580120301ca1811806104402d20040c42036030b006030a5a0545803c0300240c1c0900800c000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 792887005 1250 792885755 792885761
    0xc0606061303051c0e0316090f02070c030807021002010c0f08130f05070f0501021225050a0821040b010314030f0408010f06150206060105070611160201081e010b0d 72
    0x2100070308501c80d0620980f000118103804400d50540c035180c209005c0b0000e0140340d12030300d4001042d4075014448605200020240d07211104420402000500341140c9039210303100080303ea0025581c15001240b601c0442c40c0220002c21040001e02c001d01c4031040c60640075065800398a80d61082c04242c0002034100d44800085840304ed4018162500c480004c0c20102d880320300a02905040340c2e415a000f1070203500001c1d140d42804c3c1c1c0c8145c003e24001171480441800d4803030040041e5513a5103c1c1103c804650b04006107040513010700101503441c5001803840d03d9005115100c203150340a4501000082401c4000141c1180e80042e051000213860380c08082c1540320307218810095090106020401c036005600c80c0c00c1a4110713078401c1003482c0d198a40c04540c100296503c40040c0e00100c00103503194400c0c0e0151540758803581c00400e40864110612102c2c1e000000800c0750a0781d0078075120295079100b040d203608201c2d8030202ca400d8140c3c0002e1030a01c0441400750b00e0354800001081040084a54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 792888255 1250 792887005 792887009
    0x3080f031b07030c050609160e0a021b0601050f0405040f150e0304030c0e13170702010203040b030a0b0108180a03140d060b0c0f121812071215020c06060613 69
    0x20308070580d2000c00d440e016200050002080c0e0b40d0780316000000384113407400078003400302410720303940402c00c9807410b050901c0241e402003115061a1b0241b000c110a114640100e081100ca000c003d0441507040c81d062101d4035100c100703410301c1181480c0074840414505000700c8405500b044002000000c0502e03000082c084001240c0d11034800010004180722490382c0400546d11380094040d0141c88906c0c0035007034a002e101c006000e00d4514172551741080105401041c4407881801644d0600395101051446a08122101d0300e0083e1074055500580d031703004080c2c0303901c074003d840107140081c403d04040390782d500325260050512502482003604070b602c90701500c42400740c5400911800f44c41b9070a17480c20ba0040c0540c801c1610443d44140c82c031020100d0040c0112002d940760604043d400015800040f4044024a40220a403400200f9040003400f0060207401ca00101520304070961511502e01017040390401c81044c41400200e50301c22001c82c060750030901c115076442d140c440030114950844540e07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 792889505 1250 792888255 792888301
    0xe061615020903010b060304050c100c06020319150b0a0f050904060f0302130c1b030512010828080708070c0803030115030c0f120c02010b0d110307060903080f03 71
    0xa81000310205400d400420b0400e030150300030f0000040301001d2010318082903800410380d800c42462405a401c02c200000d81014840c07414030601109a10380c0d104a900070f40d800a0030400342440030000d40c0e035500800c2048807100380b10880507840c4c916070040d103020354000b5804000c0c40c084409110f0348a4010303200000300080c010499a41c0d210412241b07011580310803800f40802054008030040144140405440c1c00e440d998940d981e4801d140010140014040b07050001c1030000d22013404066004601800070b04006050300920803624400c80200d41d040a251401c0040c50240041c08000685022642c401032254032440e843c6007041c107031031150f00540403501c40800001074044180112101840490700e00300510050f030340c8104ca81c4a04540c2d00c3d804250150301003403180c1601e0740b05501e0060180700016200000a00248060182030f00617203aa540d03031000024540b80c140003040043c0380300c0c14607072406451541d4503280d50040c0414286500c801000060700c40c0e101030f103a1a4800d40c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 792890755 1250 792889505 792889523
    0x31a13050a20121e0103240509071701090c05040b040b0909100506060406021b041b080f101203121b0302120705030903070f0609020316090e0106060e0616 68
    0x100c002c2ca21075045400d446140e405100082480c99000d6810454030140b071280f90304842e82151160041d0075030360203448200e1300001c090341195003c1c0d4410319010340703044d60181c140245400c0d45d01219202540c441603c503450816140d0005040c609a84112007040d20080349407561500014024003c2c84003c0780c000310344004220b01c01304003049400041e4507400d001c00c904d844990038011503004030300408015174410400003042807070300072082c00e448500a00110b00c080070301c00305a9450000240ca00d0210714030a0500450715030144065500c8514034484540b00c0c0d02d041848540c031042408060107104001c05c4040304221950410f840c5100d50b030f03003105c0c00b006041c0740c01402944001e0099403003801c414081100340c2e102c2c00c01c0300e0103000000300a60510042da200c2d101c00c404800002c98140e41c0c1d541903000142c90078800181c20707070007502c00034204a180000e0b80040e1500840044681d915001040c8039054012046c0c040000056a1098032550f40c0d145c000c045c01c01981c00945500744c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 792892005 1250 792890755 792890801
    0x9040c080a12030c05070b0a0b0406051c0b0a0209030a0f03020703120903021e030c040b180c03070f08090a03120e01090602091207030f06020a1b0605040201031a13050a 74
    0x104882c2035810100ca0381e904103c101d00c100400c03942c0b4051400001d00005a501c0400d9100c4081d400001e10082c1c0140005400c0c2d5890300003d003080041d03400e800d403152070207401000f44882c2e92031440e0700458258040d0b01c1c0030b21450009485100000004084070030040c24a41454070030440714000c0c5038041405071945a450304060300001c4d5600c0100e204020041d486403038419401075100e030850300900241020707003200c020030001d0443c1c4440e040d0440a0121010815040714002034020342d4108944c5a032030134a13100040541420100e6903080c002c261007031003040c1c1c1001a108000c2c0303030180380c004003402300e10303640704c015040001c01020b4079800c0400c6802441401ea0080c4141002103462120045a000741552039050b9880050019000d1a00100101d641034004001d000d080d031900e000c0001d9100c1c0d401c0c80c080020030302039a100d69210100b00465800d4440c500132000990000c0034402e8120000410008021580a60b81901d400104070503952542040203085030001481910038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 792893255 1250 792892005 792892013
    0x5100c0305011809050721050a150b030f07050d0201050c010c0f02010e0705010917030906040308030108011508060a0b0312070f0605161b0510230f07090509040c080a 73
    0x81c28058401c0400f4551609502c482243c82100c144c103a000c405000324510304107a0050340d0711484100070512100c0301c2c0303c4000075001d200c407412003071040d12030350342e2405441d2010007281c64a030b0086000360311548013030f03411035000100d05040360400c0320000d503039004c2480100c0d614000d48054030125820100d0700446203410940007000000c0e40e500810141140051031035603444207200e454080355000c0014000724400c02000a0381c120b03d882103900d41954080851400d5105900c1569102c9010005002d803840c203002e406440e01c898581d90341044c0c2041c00c4162114070180440302d01540e200d614a51a03142809982c0313250b92170400160b10f0f40464105400b2800da45442140e000e0b08d0100060303400000f00007602030302100c40e5074407003000b01500080f180c8601c940405039110b00c2003c03034011903288039004400d581100b19140c045404c04058615041c442c001d000c0c00400c01d080410040340a60100c0c100e81115000c580e026040e89590400540d06916600214814022512154144 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 792894505 1250 792893255 792893261
    0x20f0d020306120c0d030507170a020703140a0804060804150f09020f0420180916020c0a2702040e16110d02060f0601050d0f0608120f1605100c03 64
    0x242410f0307030058800030000c10f045403030340e11020510790300040300410b40000c64442c44c050503850303115501041803030304030000030308441c0c1100008d680180e000900038002c00030202e2044100242c000c000703204450040c0c0d039105081c00f60740550410032403410001802d00c42c040c0c000030f403071505990b401c10240c4100c1e03d221002d0030b200325003603000c0c185080ca5402e9030308240c81018022008a48066004005500900f060390b101c841e070303141c0340c800c100b005040381d070717180550140282e600c400e044200c00ea52650103070130131f1014a1024070481410004020104501300c56401c04410f039040e80031400786d000105002809283c01802c038465580d010400d9180f000c0c030741c64510446640754030050106845049a5809035408060016000320001c1170012044070941608200c05060032810001c0c401070a02c00c59005030b02c4449490b485801c20011007800b0300c80843c40380c03051188541392101d010b20700030f85442155906c0030304042041c40c1c0014400203020101c102c43e90b0b01020b11030201c440d0001005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 792895755 1250 792894505 792894511
    0x709061d042f03180a050a0b04050a0b070807120528110412050f1c0c0f1b1a0705031c060f0f0501080109020c1009020f0310022206091206020f0d0203 66
    0x4040c581303443c1140880c50000d0040e14807075020b8000c02950000b5070302ea198508011348101e54501c61428503a0018400000c05032007803c0a544d82040c604e80900c1c020040700340010340700c407902d00d40024000c150441d074244240e008640300078401440300614022005048401c03d8047d01400440c012419054840315880000e015a0031140081d0307081a000c0c5d140c4500b9442c40c0c041e0324010104644140c005c0c0d00b42d048160040d01c81c8003440d07000f51030712b00000c09c243c054851a2910070505002103280c44032000b6004a0a02445003441143e50f00c0544d2071154200b85401040c07a41c108814040403600810060246140301005295403120740d00241c5066004450104054000100d8100342e030b44284d13000c022281005010840c141d108480042c074080d0070a0b60068000105503004d078500700303ca1404003028040059498001c0ea9030907142c0030004200484030051041708114065000c160b81050b00c0e1442d4119441e1009403400c43c000b8880c0745400c3c0c007840c00108040864096075405544 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 792897005 1250 792895755 792895771
    0x21908060d0b100b04090623010f11010605042c0d090302130617030d0e0303060109030b1008010e07091406010203030c0f04030f140607030b0303030a020a020c0d0501050709061d042f03 81
    0x201300760921480c5d044450085150f00081029500200301e42c41000d80d041c400001500002d41951280046425204181d4556a508004400d2541d00d445244110792a807540c2d003015200e000c1d010341e00144000800c1c80061710540d5003015d4a13500761001c5d84801c00a141407048101c901c010561402d80b241c00092861003503500c1d00d04190188440401124440c5105070340d6040083d066a5568400344406000054190082440411500c1d4240300310155008031600500345241303010701d40070a64503170080110600c00c04000703112160340c002050303d0700402480a4251580401000540c641c0545c0d4030280025480c0c070030500a1151115001c41d518811030190303980c6554500c0143c1c00d44102a110a030150300030400180e8031b4042d5405411451414415600c006501c24002040395034264030542e01a555001403004032a002058540140aa401e00c05c41d4501180300030b003c640c13150649903001c1c58072100d80382c2294501170001b0340c40070005c0d090085141c2c1c0c440824001e13500b00721400c139 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 792898255 1250 792897005 792897029
    0x7090e0108030301051c030201180b22080901031d03120106030e0313090506010e120304080c09041104180b0708090105071403012c0a021908060d0b100b040906 70
    0x300d14141c0c0402203905980d009000f00d0b440d025001000b40310070404000036030855584a03074030000c1101448800b84c4050207020300c075090b8108060f242c280c2d80d8a16102030f0000441156610004161805645a44000342400034140c640045120210841811030070058000060302c030500f80082c40405050311416030b0b041105240100c1481d940c2d10925003001504070024508006c00c25250b00b00c0d41d8401810701d400780c080b518180100343d0090303010081e107000ba080420305000750300c42007050400c1d0303c50865003022181007513100c40522070b0040d02440c0c021a2140400c40791950702c0c000b1080c1e0f4a51000e00303101d4928001800800d80d54003594691000d50810340844d003614031403000301840d0352440000300d1469103001441101141d10824111403e81c0f0960803a444658030404184652043d0401580d201c4010103001c01d6803844001440c1407000c0c178030504c85140c0f030b40c41e071581c00d042d0b101c1c104000c1074440c42c0c45c80501c1041540400441c000000300440d030501150400d10403036105200e80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 792899505 1250 792898255 792898259
    0x7120c0509040203060402041d0d03020711090421030204270c2102131e0303141e0a110609010c02060603060403050a12060b07060b0f12120906090907090e01 69
    0xc1c1a50181e0700039500d03501400108002d41740030b60246914044815071246e52074164041c04c1d040020381030340340c008643c2c04203da1081c40503090f010034501104075200d452600d819a00d0301d00c0c04000d070903460800000211683e0b90700b4021f81c100c50140409241020640c06080c1032110f050402a24181c405403e200d84401401d0050024680e903049034204240c1120480440100035080b00e5048480704103038840000d098203448100c4032003c028189a901042d081d400c02500c500c100c076000301c691400c100041c8003100030701e5048081003d65501c5007070b91203402c2c2c2011a007080084002c47d0396401810140305d9406030561100b01003e007103400340c4609035034100805882d07090455024003c54003c102000916226040c81041042c500d5400600c0c03035261018041150403032001191125680c034810740c1e5901d08401c1c90825000126100c040407855681313416120b8004182c842802180810b00e8012661070038142c0300d5658001d8107035a00e924014900030301e074805502c10404424040b03000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 792900755 1250 792899505 792899509
    0x305061b190c06110316090501080a02130b16050d0813020d030e120601260628110307030e030903100f02041205030901030e0609120307030621050c040c021b1207120c05 74
    0xd4504070350703050310b8042b01070b07071069802d4010703500c010b488600300d60349010f000c08c02d054600c1c040c0200c445000f05404c2124801d01d03220345032402c19075100b418810b4040400c880c0c10100320312544500d0781034400031204501c0e4541580d2802e43c1c0c4420543c000c085003480364100c280058168100c0700d00031542c0c0401038810b030f05032408010740940449503808c198002025011440304080c1014112400c0740b010181c04440007044a51068000e05000030020600c50001d506001c2c14101903004005503107841410000243e45261a020300c0310000e490380f005c00d0051469505890060650709080c0c0084101850416160f92103c41c2d010b010030700e04450b65074040400039445100f2050800100340d81a1900c10301c0d0400e41000308040c0806443d2000801c02c9039990204016000005545c0814140740c1c1ca00759041801035820a8016883d1064094400d540040c00b61902080c40c1c61015901601c0404644124100e440c0d61070031b031007165000220151400d88444010b406500140784454503441 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 792902005 1250 792900755 792900767
    0xa030f050c18100e1002030c010b0105041503240617010f0506160602090a03030e090a0227130509031c06050d020405130204050108070305061b190c06110316 69
    0x1602c00d01d00c55900c00a9107071814000c0440200c2c42c1d15003040500c00d141040000c039056200900c44005800104107070301102c0302400384509101c0c09080460901d41009100c10702d1031980d001040406458a00c50b041c40b421002804400002403640c4524880d200e09018020328103a0024120700300c45100002207041c0d22000d00d0064a100601091615401c907100360040c0b0b18860066404ca642000032001e00d40d81c1c40007003802180301c1c2d210341510038034003400c101c3c0c0c035000201824203e60040010003481c1ba42040044034040900e1039103020010b100001c52000c0107184640f0482c6031070042404160580000a001d288810154034078480301000103003030648880388607480e000100c0301c0d070b9800149010b411990740b01d0001501445a030000c0e400040030360318203910203c0150007020060081c004144001036001c0c58886900e1045082212605401d1150000004521030500314045200388200300921016820080920071408006a0300307a00350f205583d91100107404c000070418003070080c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 792903255 1250 792902005 792902017
    0x105040302120d060f090605180603061305070e01090e060703140105090a0207021e041104050a030807081b010213050102010c08040b15121006080f0303010501030f0f020a030f050c 79
    0x54040c2c00d000d40c00315001d03486038000919075203695031607200c0400d0f00c00b41c3c000c0c5a00140100311000c0395151905080c0101c1c1141c5500c801d090144940402c00070380c0340010b445400c40e411b00f0810134044801c2c10214101031881e0410300244c1d03103803c00003814100503013154030503800340e00a41e15651286102541110b890400505028480350b00410040c82c10002c8103510418851000d071829255600207240050b100010401154280304803242074141882030900001070703007110354613240c100b0f80050301c1c0c80300314400200513503800200c0c0f800300300a0f001642c504d48070100d0030b0000c00c005009164040d4221003814600080d5200001802e0b44c4140034850b01d66000340c0324a64181c407951100010300800404144900003030106e80c114a860321807501c58520481c80150561100041441c8240e400640c02015154403031504c40c4041c14022084904403602400c00258502c070b07806840b0050040e161500c2c018502c04a4503120350741e0550041010b003080c0810421180c0c1d11008842d010380144 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 792904505 1250 792903255 792903257
    0xe060f0d0b0a091a06041b0c23192003100c0c0b04050c180403120b010201110c030d0f0c080c0306011701060c0209010902040b04141516060e0607120c2016050301050403 74
    0x301300c2240400c0101c5050249c041c0d0990400410020045400789001181000b00c42c41510f461419000d0040240d100c0c629082070034003110380211601e00080ea514040700d0318040280e502c0c0100502c01d401409010740d003d6101c0707449106454182807950301c0318071540465018024a071241090346c600c0616492103298983c840b81d031a018500c03000f900a20f10003100ca815076507078102da60420391812001d010080c49400c02103984002008008040e105042e000050140c10010b4004040da00036044030344c001101900310707031240d850310b0048071555112150601c0d000c403032400128025038400e00804080c0e000391141100d9981c1c80c44a10101e120302e12030350407c454140000d010010080e000c5030000b040003440d000c0800460720b600030f80c82c0d01004103900d02007184201c440410a2034000d110000010303002504161030501070242c03400d016445098005a95001031002d014080c0e0380c1c0013400e0400310b803500c0012050100b03595a69000fa821860031010f6004000b80f07526050151610450341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 792905755 1250 792904505 792904517
    0x203120403030b0f1e0a1217130b030a050603011b02072607060305011a030105060901110f1c0e04050c0f070c0e0702070e060f0d0b0a091a06041b 64
    0xc94a0440040c83c0c1e1400003039000310741881c207003040e03621021054a520156007009001c000040c0410480842650280c81c1c1901604202c1c0d01103403004d19865044d4110301810356523824400c1943c41c0003012500100c034810004000c1c000c2844541c1e2140c2e100342410303002000b0030506d2005030f084c0401c07540b06003c01a400100c00340446428401d1102c00641c4003240c00e81145408194241040d01940007100040c3c4c1e03410041040f40d40030b2003800d88469059946514650400011a0040c400c2646031070500c841e21001e84c1e01a102004401485007085082d01c0c19246021381d0320300302c54a00d0102000107007130584580e00b20312b8184600c80c0111144000c1c40c1c500400c0102081d12500100d03c160303140014003200181c4e110503840003a10410080d030141400130301b00440e01040c10405454a0f0042c1101489065281c0b180d40741142600d400490780303801507450800000240240c080020040034043c80801c20a515010043d03002e44400c4030144503921240c80750349c1000305004248400224 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 792907005 1250 792905755 792905761
    0x703020703020a141005160204090b1f0608070c0812190f020901081605071b0303090f060c021207050d1a0f0c030f070e1f080114010f12140405060403020607020312 72
    0xf000708010711603101114507c1950b6166500010200c960341c0c2415241d0442010070051201c0b02c0028030700303001e81c14004554499043c00700c004d04c4054000d05040038400c23102c02000910584001303450013100e69001840031480c1285504007201aa40807081507503060400041d12907600c0d00a0321b40890040c2d55145490b900d0b4100e128801030094000d1050100800080d800318855122404001c0c0c00c3c250340b0301000d450340c90300601d0190950b00071403800d00c2da0300e4180302c010362007144c00340300e07a40468107001003c0a0848003400d0407150350000c0d50181c8070070100000c000f0300030f502514440b8034210404d05584c0700c901004040100f20b0302c66402e280d0810004440b40b500140c03a0f40c00c0310305458006d503000300d02c1001c22090302e2040c504191803408000140340003a8801c00035070141400360445075004c00c0880010346840b94031240740090150b80f0500350506641940b0004004c3c468100e0740d1403505113403d20300d803248415103060700140540400107107450b00000c200c40410340d4044d04407481782d0b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 792908255 1250 792907005 792907007
    0x170d020d1103070308192310030b041112011a130c090b0d0204090c080a0c0c051e03131403061609031101020c0306090105060103060e0f04060203070c05030703020703020a1410 77
    0xf03400204186103070645002e5080f600070381c40c410044607041c7c07040030300d422030300380819800003000003810828441c0300503009000142d1116810340d0481c1e4010041c480360251400080ca400010064121140d232030110f00362505044040f40084624082e1000d540c01400b40396001c05030741086891401182000c00100001d00c03075003008260180100000504140e2100300d850180d0f0b0b032080005000520850511030030003058844d507400341a050405502d85030030b943d10141c441440c0300b4a0150a61007020707501c0b0960f0284221041500d40d0001c02240a44800301c01c400d01c1c00c4500118080c1c0b04a400003074042c5040103202141c4409612031014540c90366540c540401140341d0228114011516041050b841c20850300d8002d0283d00004659403030b01c0c0b07000500300ca905500c1090781c5010542402405070f0003142440d0441e80104025a1300e070754a41040d116201d10040080c00b0707120014000c0289517002c10b00805482c403c480c1ca1100b60740c0c4000f024200d9a10442e05075000c00f000010340e9080d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 792909505 1250 792908255 792908267
    0x18050c0a0f1808010501050405130f08031302090103140609031606110f030a0b030610180b04090503030901020301031709060a0f02100e010b100807050301140a170d020d11030703 78
    0x5541145803140c10a01c1109940032250b010f94050304490b0f46400c0180300b00e1400f80a200c0c0c0c882104524a00e020005807a6011941141c090140c144980000440e0b071021480800c5c15036280c0180181b0090350f540c0c6032200001c40411001d0010380a0900468100c41c004030441e20784200c014005510b481403600c5910042581c1152160b0b64030041081c22422402407011318402c19580314001126503520003490300f0603070010310109030310100f10014848084442e0149140020400000805c5c510810118004151200d405800d52002008001422505400442c1664800d4541d402c2101d00d01c0d06105035405500c10803684010700f4481244a9880b51507510303001e488500c1118148801001c1d20000c9078180c1141260507510744142c0949420030710894030a035005844c104485152820008065001c180298000003a60f440b000c0038580d200003500d4050100b8685040c0d0303407803000b00340a41d6008114000d901600600d14100b641a0146101c01403409145000c1c52a0400a682c21918 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 792910755 1250 792909505 792909527
    0x90105100825030b011203030606030c0f050c0c060c03030711121c0b0909010c0305370209041811090601021c09080f0604021908030a0c11040e0718050c0a 68
    0x40340b169440000101d2400e4800724002c203100c51001700310b000c550500034141c400712781108083c03501b41071a001405a11201ca105001e1035443c000791a144050100340c10044140701440d40004046014401c030300001c00290300800c001d40303898485001a601654440c1d02c0c0b8205251510400d200c074003080f82c1a0640c41c202000f030000700040c1c80c01e0701800105408800d4074554a603a5450b074552100d9a05071082c581c00c4038040300a030311943e404502c21220560485503151049441e100440301810242d0140c13825918018030902202140183c880741d041c050303113000d032107030114100b0a00e480d0400c1032581d0b010f0241a4040d04404403594020002600c80741c0300a010041c10480001315440180039103d0100203d00c007411490138a8010030855402d03c40b840056490f10b170341c00300900080001250031502c82400d006240d40d8a0741040b048809403e102c0680150901c0400340b20100b01003600070943c1c07420246621801d03e144850021114222101c2d0200744080003030901ca540191a0601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 792912005 1250 792910755 792910813
    0x8090402180d1103160503060103020f0a090204030b0411060a020a03051312080703021c050d09172101150207140d08040b0c100c020a030c1103150901051008 69
    0x703000301c006000c40c0c29162154001e03124400914802e111601d800c0c01000a05606404101a00c81c01c00001030f48503103041c0300c02886951008031f0707000c80751110644c0e840140417508045444e41d56038144102c40c00d80881d000c488140e045c0b40e0030442072034002c0c02d442c4141d9195000b08200f500b5580c054440b98843d0301032450b0700242000024841c140031401041e440c1c40b440394191561224607003c0c0c0741190300ca90304200010442d03845c603021a80030081d960484c40301100490a00300b0750070070302d0102c0401d96103041c6010b0002203081d00312460401c50041c650708441305040f140e981344042c25030244102c3c800b4006810266041000304680294850450703001410340100128075030790902198800c0d802101c81103404a00148000c02c203100d0a158061842001c3c0031250010324000d48804481d10020103000d0412909001c2c441a068003100d07403c400390071201910303880b240e480440e40048400900315070070100010110001c19004900712420240100600e20070303810122410a481c0042c2a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 792913255 1250 792912005 792912037
    0x604080d0e0a1203050c0c040c05120a0605210c0405060112050c04050405070809070b071a18070f030615150c060f02030708041a2214070308091305010308090402 71
    0x20038007461183c000580d0303603c2520703195aa4010150480e00f49500c00b06410710407403601814041e41c0d0b4101c000c56945026800d0300d102c0c165990000c1a0040c42241c02071f0741c014030440b9041840719109500e20301c8100e190421a00360054080801c0140c80080300c06500291441c5001c00b595070186d0030103600041e1544440c1d0134240c0f95008542105e0049079040c0000e83d1620612002c8041801524045c014032202d681c506070081d120000302490a405211240c040c0b0300000e60714021001080043c000700c581039541203583c80550003035940fa6400103071822443c048001e000320f05180c0984013142d40014650300094070700f03042600c14080e84241a42c240d03071590440e007802243c1341b0056100e1803494581c944241028144440300f6104000f20b000c5c041101410b0004100348502025088001d0800301903200707505107402ca04600c44542241c4c03203846841004410081c0076005801d0718070003a2001000c1d00d80314401d10080c2d400a2002500b00c0108200f2004241003940050642d2120707543c2d41 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 792914505 1250 792913255 792913259
    0x50a0309060f051e072a0f0305130605070c05010c150e060a060e07120c02030c0609030306010e03030f07060b010e1c05190506060d02040615020a020f0604080d0e0a 72
    0x80301510b2240080c0801c50b66078404010b20312104169460441c9505148056140740c042c8010b40b1054806454241007204880e030350024291a002d40c20b03601c0c0e888900030640c1080c5180151864010b2188040048a00013010440a00c60070a0351540e46c0c0110800d034601d40b810005403280301902500b030700c240d20007002c0d0f0900d84626000c4d50035003a44a400503c8289030001000007111800e4100084086a031002d1141c91680b02400c0241c20f400d11200007081c45401000364514415044078201c1c0d0f000340410010384802c0840510300c2444c003038841c4407014a003941010380380d1040e04c10241d0150703c2440504046804c03903100b4520500103050425422001c1000100509040603002c0b941e00b07a41826a810028148034007103002c016034601c5000c0d803805680e00381c1c5817000209514050f00311031104c031055540e23642008008200c403502c20031041070b030420000e407100c2d003a0030305a001d12a40c068401503801e04200319812903a03040040d014010001404a0704812543c240315440100c0307040c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 792915755 1250 792914505 792914513
    0x80115032705100204120b060303091c0506161409040b0d110102101802010e15030702060103050601150e0103050402040e1906060b090a0b130e0c0a110d0f050a0309 72
    0x164000840c41082807508482503454118034040c1c4001802a10070f0061100f0005081d8410245103515809246800d040c0e0781c00e800b10b807541c050220103543c403000147e6280034151030b03a265042751a0095043d40c06c1980c2d417440c40905440441e08da10002450707001c00c01a049046800741aa0315001840401d4a84021000442c605240c400c266440d12910712024159a010001c09008800c030030014004407202c20740550341d1292014002e8140300140c80300c1001581e940d02030031100101000200d480c1d0800840096a0b503c0c24081100d207881002d0012841d050105034807c040740b1559240e4441503090170044010f030601800483e00941c03034009100401d032060110604004d40105003030b08a100e10300b40303c019106143d11010414408100c40921900c40100c40416906540301c403540c1c91807045200429001d0303603440f11800ca10380c3c000b032208150404004001e408507a03650459032003403000c011500c0f0702000015001042c04a1028952a400340c000b0386056030081c100080c405840d620703 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 792917005 1250 792915755 792915791
    0x2010e0d0305070e0108060a0501050a021203010807060807020309060d09081c0f200d020313080706060501080604022802010e03040f1d0f0c0313050f0f0105011508011503 75
    0x140310100e92203104102860b540802e03070302090f05003440d01a000c2d040c11804103000c40d41c0e6000ba1810810000741080805008120001c4219070011417503969683d00d8600a4448641d0700070301c000104880042642e82d1720000955030107810060480d0320300b80340641e400000342000380d4115054001400100881c58000c0065030000400200101c2c4003d2108105412038581e000b10360301000b81105246081c189090540303000304040c10b80140c2e00d0b01c800520200c0215143c2e0002c10701c2c03000241c0b4104101041d00000d080703130401c0e210314030305494031405c0106a0182c24120040404440c034092407030000146031000c00c0702030f13000009200030000d600070300307581c030681006c1501101803804000440580d14000e10300c424103107184856050821000300501009840004441008000303c1c442110310900034100d40d5001c01241d412804010002e030300c1e08503200c94500b05501c0c00b0000a016254401d40090105d110354626200341e003000460200c1c24080e299003020965143d10500f0002d140007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 792918255 1250 792917005 792917023
    0x90a0b180613050d05100608030a02070311040e0307030e040c05070b0a110c0307060b03250e0705040f060c021806010c0f15062727030c060204060309050c03060403020d0f02010e 78
    0x5018006e144d85486031340b001c0e100650300014096104100c5806c1041e40403c103039042c1c99010146003a0761406000090261003081c03142d040c3c1380400280d080802d900007500c81000f60003541e052261001041055981d03019604001d00305020110014000c0c00725980424801c1a48170340c4a404d009101002c2032843e0081034040b00d0099843c0b00c03404191a003007200e843c51101074a0030134483c1c6928000744000603e54400c99a03224040070100d108a4012825180540340d00c00700c0501450762901c00506081001006074040d03c980182d6102d0f820240503604c0c403d9806841c6c0c40003402807130380c1e0810740381800c500980710000303e0a980d105c20703103003405410000d0480d8003000740300c01492a100c1400c0c800300380c1c6803408075140c400c0c507041c07070300500202c1002140d035a103400c000c004803070606a4102c0b20240700142000e100180115609415a20404101e0300541c00c480150300e4050500d0b030b645a05440240140c2e2002070301801551081070100c0f5680075074400824800d069403180c5d0324044844e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 792919505 1250 792918255 792918263
    0x1409060a1518090606080a0c052b0c1d030a08040b1b0106090203090607020c010e0d0204140a0606030b04020c030d051008010c0c020909010c0905090c040b040b090a0b180613050d 78
    0x19013010000700384d12880d210303046007036901c08010b02c0a04180c003403c18804d80018111040c0c5805000d040020700038003a01300c1110341003042c0100d070b0414a00818444400b09520b642000010320604141000200c868441d54007040e00c40c901814507510516030303004603030342e42100c10641e51181c1c440c480a016603030040222020141c0c61703080030301505061550050840f0304650121107180140d81e400040d40d1045042901d40d03c84450050000c1000f900c500000e070400c11902d08144004450658421011120155000c00030140ca4004110aa12482e91201c209074000e10140c030100c100c0b58003154000808080c121000741e9144100303801d60304446840408102c41c100d1407815414800840e0317500c0300219000700410201c42c840540fa0501a000d401c0c002c6141100040d0944a0f81c022600905500380c6030a488683c0c1d2032050010390b000496050040c4008000012165601026901d8507100a561000905602c00500c00c440d00400c0404001114442c000030b6107490300001590b9983c05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 792920755 1250 792919505 792919511
    0x406210302010b0126040201110102160318180b0307080a0515060907050a030903091d1e0903030a020a180603020c070602030307020d11010e070b041409060a151809 72
    0x1603410040d003155181d0701103e040c400c8544210403601d41e000000400510741803c2d412550304c0354001212040440e0f80108450743c40001c0e664030156181002c42c9000c2e10950b11038500c50305403940150905494400e40c003600a012072140d01c030105a030002c4130f0710070020301143c144964442da501c2c40c24100032015107081d042000580c0e0010050b86680d80c0c0850182e0b5070300064142340900034403520541d00344208040d900c1000000300341c810301c4141c0060280c0c0701c01114036605008080d800c50001e58401d99124039252090101014601509100311b051602450460360340e110510b020b907202e04201002c0000b210401e80030007250309000c00241902d603600586038000d07078100303500e4541d9903000241554030178410000c0f443d1b1b000541410701d08040c40d000c8a641600b00080e80134013280c00f80100da5001d10034022640c6070814020384111404800701e2615030984c6000e0084c000700560301c054102848201c00c0c40711a403e000c1160b0514014030f0482c2120400003684041840709410034110161 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 792922005 1250 792920755 792920819
    0x103180c032604030201080c1e0d0c08181518120901021e031c060e0f072003092101110405033322061b0206060306150406 54
    0x40601c4010401501d00d0300c2c080d02d01400d40c1c00207000540c00402100078100d00044641c13201e041000f5154180f40380b0582d4948800e11400144040c1a04e41c291b03d0010381b088001492401e55240603018440f0440c010b004e00203941c001519610800501210601c3eaa504d0400c005120400a45421390340b01c5001903180d4180c6000242000b142600c98548a0354075410040800d401004554032100320007110101e0b58581c11150340034014036030101c48018840c4082000e560041e440345c5100c1da40981d54443c48443e0f4044642150041c0c000e0b00c04154803d01400120303051040225000d44041d10620f03000351341c55103a0b1425038114081342640e050303000c038cc10040b6050070070030702c0f20310800801f0000c1c039020349100d1804207401e224130003901483d00e2400306050126114031104580080914030038525068140b2101405080714884404010700c2482003000d07102080380e82c0207000041c058036103a260302444441c0200b03030f864940e40c8682c0e01c00c0b00140c5d030040700032500b581805407910184520 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 792923255 1250 792922005 792922043
    0x19030902090f1b0d0e01090503030403090f030c05131d100e0f0318121504050c0d021315120b1803070c03080d02120103081801020c0f0103180c03 64
    0x40c0c0041d0008540651150074080300012014800094541490380f1a80b91003503c034a0401420340801030b5400d95191007030010500902000035449203009460b146511965006c0402d80c04000f072001030002103542509010925140320741c1e0811804240300810a60b56807441035880042400703160000364001e61607031624603900e000d04058481b402c8007604140c80300616254583c0b00d045200b060450107580d41062a076130309c0c2c109000c900207820455084600442d00d035030103240c0c1910103950034443c500751a40c9030310341448030072150741d03014040306070315411095000d0141030270014440c0c801c0d12240d4049840c9a0301e001400f45c0e01c2c02040c042c5401e00b0304111a4042801c0701103181c01c507070020080030022511094003e81141c1c0e21079451350307070b03001110071b040c0080c0030b03851001886207026800007051218503030203418111040342400111104120040e607441003008403150b00524001c1d4520301e5580280d1211018031450781c0c0b5051f83c40d00540d2044040001500101c48180d00340400c81810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 792924505 1250 792923255 792923269
    0x150604081e03130302060c010603080a080103031d0a12020301090803070507060e1b060304030e100504150305071b030c0b070816110a0b0903070c0e09010b0a0f090e0319030902 77
    0x1041c00700301a601e0000e0700b280b11000c9941501001e40280c0e000104280c1d03100d801d41c401f000840d000b56005481d0f0307000301002805020288020b500060340b0b0314080d48440280521500780102c02080d40300d9441c40d1603500c0c07524150b0b208069905550310300e030400110b0740703001c0158800c61255942c03136901c50842c9007580c120345940240100c0c55206106201c5e8150390485440c503403c90840ea110b0b101e965602d022640c1104600a03950864190313200382180c95001405003042d642d00b2600b1030089100c3d00030880484400b1180c000002e100030584020001400c008200000e0207841e00c840b00d6031107a150310412001c1600c0c810002000d110800c14190b20703030720400910701481c3c0b42191400d81e001129035900d10f94144007400041c0c01c0310114841403802c00441d07036120b070722094800c0019611494007542500480344010300b5424221818054944a5030b4001503a9480c000008114103145600d801040c200403404101c0c4000c1040c40e801c684400e1180c0010002d03940c010480c8070580c4148410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 792925755 1250 792924505 792924553
    0x3d0b1804020f01050c10110d050117100b01090e0c0325020d050a1115100618092705010501080c01050703050a110c10120506062115060408 61
    0x1441000400d00005a032441e0181c44891070902c0c0164442da040a000c6043c8280814020815480c08810f0fa00c400c0d070703082c0901001031103202e0800450f039a0340d0401d400d2400002e4090095008075407510f01c1c1c0e6410740e1225640c1141854103c66103502c506900024030300070b581c0d2010001c4017004000600c0c544520394240c02c8550913450300500e84000019544081504000080c0000404d88407c01072142d1195100c3c001104110f808290081e00b41c011115019500242400550400070480074010800809210009001c010440c0e00e0102c221004000030003480542582490007103c012501c034001004080c003910001034a549803022541c0340210707046c44981803200900c24031010a400c00103580c0d01410f58142640c9680b040c41003542001e201680f103d900c8490b880d02c1441141d44400c00d12075052010108009544030b10081011300c0c00303004013110f15100c481c1c203800200000d0b4080550060398a001c0b84142188490002d0502d8005400200080d803248500262400300b0200e1322749 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 792927005 1250 792925755 792925789
    0x4030203010c0c030f050708210916060e0402030411120f0705040c1407060906020a020307020a0e091e0a1502070b060a0e060d021807020a0b090f3d0b 66
    0x143e0b40659002d404000c0368220a400d00102050400c1402081c85c1101c000400b4141030103030901c22400b03e00c03c007100583d0440d0540c0f144c040c510710454220301030b1500307498154540b0416803098008010107544014003c80c4ca0f15075085074112951580188c1c44001d1010501900300c0b08042e141a615000044d13004900c150706060a801065130010818a40c40f403004200e036544411906100000e000d4151000b0001440051568103056010000e080000d108484251166540b04107010003010300781c0e0021065001600081c1d000408030484040e98244407040d1a01202551542040c0b20013901d50a105035800042503010400440c088640c0050212052110b0324140b40440d164004001c107654010890020004150359941a40109a1008010706a0b40d49803840000b925442d084608607500890a0b01140c2090400f107406801041c000d00180402c0115028200700c2d070007408501ca800e00520420351003030314042d039100c000c0b451280c8000b00d001d040140510000501c2844101c3c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 792928255 1250 792927005 792927017
    0x10f09120305070326060406090e1902030f030c030301212a030209040c031a04050303070c0309090e1510050102060412110d02010902031203070c0b04080c100204030203010c 76
    0x482101051500050301a03054505a51945501c0c0340580f0302d07642c0712038060600b04200d140c00f00311030011440b16100f0070050b0390900c41c89545442d030400356106100c0404940c0c0110294115042034070001000050006049588120400d500320381968801e450300d582c0394000000601c4220b51266842c080100b20848010100000d82c440a10800100f246141100d40921892521884940c800800b0f56001030005219041503c0e003030030311904502c0215501240b80d800c0b1307074000210380f0240f40324a070010081d40c44e56651420031510060740300c0040741401154040414211a0740c81031840881000000303040500c40981c901a41420080505004065003001030150f640e01007211504154444408002e4010225042c1e84409044030902e540d0703c101d000b840c601310f6054200c000254001d9080d02c1c107400c000c014080c11382c03104803060000300741c5690388140000c59450300720f80d02600400c0742c142050300c403003c55414550140405d0f145030342c000c60244154038081c0f1a603d0141380c01e003010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 792929505 1250 792928255 792928259
    0x5010609050f10020717070513150e0402060f0f09180105010507110f100f080c07080306090a0908041205330705070206040905070e04201b060f0402010f09 68
    0x1514104000000038010400d41203d410b2050080007030f075000c1d101a90303d58034480514083d6580d210114807a83c2c1c0f00d00b0307041001c400300000c1407061038450541c03075400010306810a00b4407070890300041c1c0220b810650809c00e190081e08100043d0601d0781044002a981d100c2090030054881d07600c1d2f01c45d403003144900004022580c3c001c2d007101d03406540701c1901d014440c403100004100840ca0309500c0d400080803280b1910703e43d84210985811143c0d41c503610410740b41c1202000d441d001e8400e000300764a1040001c50305918040c44650341c032a003c480c000c00c5d552450b03a501440d68100b0390017690038072004a45801002070070300007044c0c48003503142144103c1e0b07107130000070342c1d618903090038081d83c04071010104494905c101c044030056600038010740c3e51141d4401002005000444403100080c0800c24502c07103a10b0030f0701030281815116901141107020350b0003201c20706c3e40400c0518100a401c80c492522000d0306114481c41403070340d21403080039490a4000940303960804000101001880c04003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 792930755 1250 792929505 792929509
    0xa1b080d0b2d012d111501030f080d1d06060a060509090126010e0c0901080d0c150e0a050a03080906160f091809140c0a030807051203070807030501060905 68
    0x62801d480c842442c01801424500321980c201403504109103040404600904060541040785c1c02d038141034850490b45c10002290045031a5902804000e06105031a0020300200d021100500205000c1c0c100c00101180318458031010b04240003407181843c0c02103001c01904e403600c440180e00074112410218544420030000420352401406601c1e01e4280e104180c50f4801504800310b1050a01d4030001c00480c0c00200e01c95030390342c0300c1240480c0714010160000c5042c901c081924035030307650f5a44032407000c1c508075660400d078094500c6401a90507500d400403101d50100b00800d5a9413802000980b030010102d040040c1104001003e0040c56070010082c04a901c418582c1442000900c1c40c0400000b03031003200481c7c01401c164403281540b003404590054030411940300440c018400c40000d00c66060032000c40761507000d030f003d00c560702c803511500030000305060000034002540705100369400503502c00f5080781d1a4200713560400004c1d201104000350103401d446518090714290500010043c13070040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 792932005 1250 792930755 792930829
    0x1c0c02070e01150c140c090601050a1709100f02040f050411030112020f280906260304080d0906110a021309020a0509091f110a1b080d0b 60
    0x10800c0b02440f95001d403125158801d044081000f40c2c49003941001c0000d10600c0ba0340e0744080c0039007501c5030100c4000700c0d0143d800344080310124046070300c50511480014200f4001190001c0020380310780200410031510300c45500c9500d2014102d41c5006031a2420642c10942e000a1030300024001d5113030417040209101c9880c15241105c080180005c024900c610102d0721000c411810260450f8156000e6a246015041200c5085c2240c888035405190b9801c007040075140184501b01c0707000c1181100a41c035407102c2c0ca454100c25400400c80e0328095450f045240b80c42c08903030803a000502051000d002803a444150004d1450941c00180040c0c00da50700042c3c81c3c02c410391350003007601e030b55100c0c03000841d281d0151400040c40010094581454a1103465480300250201442c022586041c43d1410800c188100c028102400f0340aa0401090342400e503260b241d840d04504069004d0001d4200040e500c000520700102085404905281110284054514210140e074010f8003403020722080009404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 792933255 1250 792932005 792932009
    0xa12110c030a0c0509040f08040f03120e0a060f1107030b0106110c030d051612030501080c1c23060a0b180f0c13052e110304050607060e031c0c02070e01 67
    0x171031081d800c2d100e81c0303002c000740c484020009003440e40200300000c1e45c1031040c81200c1120b00555103050314000480c422224400300e40da280ea4488200301c1d061000a100d82c501c902c982d26541805014000361500c11880c2c840168012507188414600500805034003201c40c9800c2540d8100408007600c183c0006610707041d090b40d48000b0000080341c440c507408071141c85404241d400030078020b000540301100802501e1300b409408902d2044e202c074940681050b00c00742051889454079840c04640c660b4900d00c8824010703090542010b14071500040450080c0a96400781030205400100000d112060004c040c0c003400360020700070710301800c00c0a0310180d481ea035540b2204e50300c0341a545043c0b000d140e040444194000c1d54001c440070005070304e00150065a040c5440160102e1200300280e004100d0b8000e40b80c0344071180c603400520040240f030612102a25030b403403203800041018408104042e03d50b03000301c0003560b0703c41500b000f111a02d00241c807410200d00d03054405408186d08004044410341818 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 792934505 1250 792933255 792933259
    0x3160b090105190c120e0d0f140303010f0501080105011110050405031b0a0c0f0302011202030705071a0a0e1b060d02040308040b0c0606040c1b050a12110c030a0c05 72
    0x514030303000da105004a40d80c0700300310814000340152801c4002c0119112803022101003040c0245d54240a004482040068900414118101c1510b0740ea01903014910f0740f0865444016a411500c000c43c18400b440c0600301c40c0c2c41340000d803403030400010811130060b40b00c13505100241030203051241000c80e940a20500b0350002040039181d6250803455481101566464901c2010200e05012400700301c0c00d03202400385100459550b00c07540d6a0f454100b1601c00240420103046011115501ca60081c2d94400c41c1c50408905015480e114255a41c00c800442c0c85120040c6080100711095441000d50003030669000300340500c02e000712041104050b014917445428041000c80300403085404840107142d0001c030190b21195a54914035140d00407241140c0240901030000d8a43d0419120300091540c00b6a946103241405003118a480800f0b2102030fa001d001c0c002c00000030072000c03001d82288054030b9461441d0229112101c07400c0a0186520398071079004401c802022504242d0300070305441c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 792935755 1250 792934505 792934507
    0x308040609030c08130501020f24070c0503070c23010e010c0501021b07050a0e04030909020919060f11010b0d231209010e061c0b130e03090a0503160b 66
    0x240b03060503100b004004100500d8481c0004481c41384500080060045402c00e808680001009200c156110356000e10a021002011800341650121154045400001c0c6042a03000c0c2103442d100c0a06560004c41e0035118407030307155410480014590000344504484034080c4298921140000f8441c800c00f8280504008880310b80005201003075040301c2030300c5405050000840c001c04002912101d492041c64450b07460b14800140f102c051452140c407030340e07140c1da5054009080082c0d250094015851081e080b0001091a041c40024154048090a40c1c5c0c6c54043c446954180d00601c1e01c007011480f041e0903411b021a09a00b82c407503610000e081580071000c141c210740190a01448040c4100084403203100708800315003412070200050070401802e91b0b4184000700394001340042481102120540300e85540d90328140000e6550014a02d600020000400910110020801da80003021168400d8200150300700c2149803140d0503000400080c0c0c080c005c00e2051840321181c42545105155440c44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 792937005 1250 792935755 792935771
    0x1505130216020f130e0a0308090a0302070501080411060a08041b140913050a14070603050c0a030e01180b06040f0c12050a06030c030b100b180d020a0330050703080406 73
    0x284184095000c054812000c2180c117120341201a51b501c1140c80980120340e0001c04200c444130301181e100801a0103030002c0c142146008011201088024000d40303030000304c0c522614031960741034010681d038072040e0b840d00780038109810f00c1141d1054480a41c8010780c404107080001c1448159001089402202c0e89000d503070b143c2c4007003a550002e04a00408a002c1ca680e11420040003038042811200108101e039031107516070100b0b0707040360300c1918000020a800e00010b00750520030b40240002076410070020035511000c1000d15511907020f24201c50085c404401c11156041c14800c083d006c074006101880032000a003000340041186584580c0c440b42c40740d00040e0703085000d070030800c0215030002c005911181d4908011207000002e03038441ca040d01d20200000f5041c0341400549015242d8a25203403070b0100024108150640142c1089130070807480000000811100074003419104003002c44060074681103407074040626452034403030090010920030200030903400050300f98001e610000001d4901 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 792938255 1250 792937005 792937009
    0xf03020d08040509090d03050708070822201c08041e050310051909020f010f09050306090a031b0b0406050403170a0b01170f0c0f0408011505130216020f 67
    0xb12660700420b41040e030020600140042c0020040c403034140c259000c00803a00c0e03103042150f5200c0c0c140d903024005840c1d80b02113500003100e90710724282c03008080c1c1800040e500b950f80e84581c0314800710f09031900c0d40c6c40c080700e0340c0b0300d003440018a1010190f50351140c0342c09105a5489071a409140584180020f14a55251010041c0c0007124042e00b4014100c49140000b43c1009002d480211844c01a5546115600a90034014042c3d00034180d1300a0040352107440110045070300880c408130200c20801130400001d41030310144007142c0110300c040060210262030b0b0034003500c400600d0003a020016011001e01020414008100f5080f59001d40702242545850804540e04a043c510810700401d542007448024030341c60780710403003000702038903281c034010b4040d82028100307a022108600b40454000000c1d9050015000400411222401440c00d241d00d40702c0071400c4545d51240308043c001c0d682c105100d00e140001c1e118840c250410419850720b401c03c0e50700c0c0d00028011000070300598031981c040041d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 792939505 1250 792938255 792938257
    0x30b070c050f0303040b07110a030828050115020d05120a020a0521010e010f0501020a0206030615040b030709170c10091701140601050702010903030e0f0d050c030706090f03020d08 79
    0x1240c2c2e0305003181d0b141d090a0130076541d032800548120011a003800f1411100a00204000f6001d80c0c040d210070300e240e507444404842040480d1a004c0c000c000c940c5400c9406a52442401d01a004600340e40c00300c0200040d019140030011885034040c00001d10550290000600341700d60b211101c48400343e200c85003442d00342c986009030340103000da01c03c0340b864440182c500d5000320f40c101d4004061a6846036600c007907040c5c05811034068070340140c01132030000d03002d0704080005540100c8d02038501c00309040b845440410f80d42081d040603003c028000240001d27640d001c0c0740030018016a0703600d120343c080c2481d4070a5a41240c401d80074020212007055001e02c44c0241c80102c01042c51943d416404d00c02e81400a00a0860824241e0301141000100e8060351084080d244510f5040e1540b04030142941c2b020f4401e01884000f4551100d82140444055154100e050040511400c000c040c449010800c2500303100d01600f00720100f000c451030030400c0c036001d06016011250152100d544a59503400c0002076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 792940755 1250 792939505 792939523
    0x90b070e0409061410051f18030f03050703031a0a0501120f020f0c0123010e0a0207170705150c041404020d020c0f070e010e0a020c0c030105010e0105030d09030b070c05 74
    0x44c6403089100743e0b002640d80c03840c4101100c0b20505045900e841c1007101c0c030086149080c000304141040b50002c80e001364401e00603901c0c1e15851141c1391340d8035a2805040c01d031090040f400a0b502080d00c20816030180945042d2062009451401c0802d010100702088140d00c180d90402c01460340602205406502c40300700c0600a4006642d110040524004603034401c40e0000215881c01402c0100c0101e440c104c9800000c001004c0d200720303460300107094070095002c0c2c80e04e0003503a07080000d9000658038000414104c1c00311501180c80780103d04055003441010901d8407640041e01e010003500200c580c0c101d5090f0743c850385101c80c0f80054040801d009028040c40c0512291001400b00c0031010009240d034440c07144c4000312544c3e02d845010140b2010b40078490352291086290100c1c2c00c082031070300601280d80204c1d0807074020f04261130010b82540c0080c1c1c412100000400c1c0184903600707050141040c038001a0601448507403031650340d00d40098005100c80e0400403184545020400240020a6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 792942005 1250 792940755 792940763
    0xc150403050702090c132106090302071e0e0a051312201b010f02100203190207120806030a110d170309010501050a060e130b1906081801090b070e0409 66
    0x11040c82c085e0520851584040c1d801103407148420000958100d2640303100d4000ca925840c2001c086445030307a8000544403078003048095005001b804245000e613000c0464207070050f6020f42d161940307000c1802801902c050201c440c0302d030500c030802100d02c000205219040e0740c8213003062180e07010880704483d5000f4880c6850640300f940700140c0c00160300010f0520211003c06190b0007071210780701c01511050340d500044409600503100c0100c500d513199000c3c5502c40401104642c50421011441040380c1c485001298981d608941e60100ca55014118982c060001c0e00108104c0d681604c804000310701808080748a07801c60181c050810401c015144d02001503400030548a0170215680ca0181200340281409040114000210030307120711244c00e80e200b4064403003110900460703459806842c50483c0c1e0ba4100038451520003d0003400c1c4030480007401e1642e10500d10f4202051103c051110006c40603a2a0b13062403034010109404800d056002181400c03d540d01107140b00109000e414138020142c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 792943255 1250 792942005 792942019
    0x150604050303070501020309070608040f0b15040905010f05090624040209060c0607020d050403080d05090705030718060902190f0c08120f0604150501030906060906080d140c150403050702 82
    0x700130414150091400740c417003070003551142601c0342412116400b04540140c91072071840b00e0400410001958107400080c03244103800002c0803040880c055544000701162980e543c0c24104406128078410b903500000d0101c050080b60420100c04d03180c00c0309460132001800340e40780000720140c1c1c0d954100e605c42c0b04050580b60b140d59680f14010345030b03102140c911000d400381c410107030b0001d0702c14000c403020b60ba440684a82404003409104008041c020000311143c4030320200480e19a07020001030004111404060070f40d4011540c0e50030580341140d1040c4592401840090148241010400d002084070302d81240d4020350000d0440d40041c803402c02418908000031040300c0101e0314000300d8491072046c1641681600d0b088140b200b115071000700f440702c0008200040c0007940c4290402e0b407400b8014000490880e071180c81c04000c0342d07451780c8041802c2e489103c0c01914960044e41e9a010743d140d0f0203119090003001c0301500d880f81d190900112188501c200000c08050203401980c4840780c01030660 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 792944505 1250 792943255 792943267
    0x170f06062203030e180705070f060915020d1d030d0b0102031323010e01022527180506010603230a0b120d02120306180718050904050303150604050303 66
    0x141c07000410703c004e01c2c000e02507014201551401103544a0140c1d0b115a180b500d8403500c7e0315000c0300a8010722044481503201c030f49800100301948a2007a100130074500059499228a840c0c0d0100c0d41181c00b056240050b078162030702104c0c8080280c8001304c40d0300c00007080310145400100e0562040e100c100c0d0410207940404640c43c000000da64101076000f810800303c4c14014001034500581708804580183d00c00c00ca543e6100900c103400342d05011201c1051a13500c0d841711440e4500840b080701c85c0c02000c0c0c00b000da00012041e50701400e0071800e0499003d0b035080c40180c0707030140c45034014019101407540f584d6810044521062403941c0780d2070040880d00050500d864040050b0044c203400d00c4c8102d44420320801c074000041150b203440182030300100f145030070810380402e8642005201c1a0b000d2140095454540190360443c2d1180703100b6a02c141c901e00c031482d00c645100c1100e802603401942c0100400c000908000212500000c8038a0070492804200002031484d02c00ca410440d0140404514 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 792945755 1250 792944505 792944507
    0x30c0f010905060c160609020a08010f0504020306011a0a0809070f031208070305010f23060403050f0601060f1d12010c2102031510030f0501030b07170f0606220303 72
    0x4000c0341c442c800c0055035035680381c1000c001c080703015003003c0e0a080c9180e030804000054155020048080c805000d40728240e0b50b0b2503801d8211762540e2480c00300151684100021489c05000380d0380581407882d0740a070069110010403105016a41580f0140b011038000325120400400c00c0c900209940c000c054075040e00d030300c4c142151064500540020861980114200c10f02a0050505a03090007403940c07103d41c50902c0483d1010b1541c408a0a02d07a036000d244807643c0c64900041003d18002c3c002800c0704591130713403420f140010503848403040101c54042c005410703074480b01d1030f0490180c101481448048800001304e12a510a03291015503190034420030700745812401713401480881d540c1c0b451120603ca041c00e4140e1004840514101c80c0d1006170808a1400110b101c88052803442c0c0054a404081c001c0b4003180c20070380042d101081000e08002000d540200741500122004103070300014102a54010070040b00a8200352040c10b002c20351000703401e644103c240d20034202c061045144d55603418 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 792947005 1250 792945755 792945761
    0x60d180305040e100b16110a0e160c0c0501111615180e0103060c0c05030304030509130218061b030319180809010e120604060b132c030c0f01 62
    0x403074600d8a841e81c1d00001c4d83c84188028a1080740e03c0112035516204e080e119003c2c6001d0782c04030850300088010024415521118002c0000c1d14240380c8044180c10040c41140e8203c01d111351001c00c200f031032111038002401c569002c5080391800c0c03e0607554070040140c2c484c28101401200d00c1210b104080c005120440c140003d45071864985814242040300b40c8010a0300c01c4500507090441e8a020040002480341c0d4090f550b8007101d0301d007451915240c0d0307030741a065501c161800c0d000681c01288010b110f28000b07c0005068006440c118074200c101011324001c1920304d071840c0d01c1a00c5c04141114552034284460808a020600b41c1c0c0d0340e441e092340180040c06c0b19143c5800300c14900705019507020343c403101241d0a150402c408900b080003544c0110756002511030582d400000c600c1c40034003400700c03c00c0b0450207944514408240c0c03540344428080100042c0c1e00c1401020300380f441040640200310241221240d000c0380000f85010303009985440c6102d01411240c643c450340501c040038480640c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 792948255 1250 792947005 792947009
    0x919080105160e0a05030a1403210703050109180b06010210090606080706051e0c03070209070309060f0203010b0f03040f0b0103120801270b0a150c2d02060d18030504 73
    0x6203514180b00700f0b4100b48651041d55004403500b5038000d01f01311002c10b034080c01d2514050302c103d0442e80b5001c060192408241806854101e40c100600c0601443c03640600032140036281c00941044141014400a200400c0f42d1801070082100c1102080c40c40e4030a104850100c01036040500c05c848a0707103030200050910384070304030460040c4200400d00078403c008640000c00d41f890302c00030300341c802404480031768001c2c202c0b4203242c4002c0114900507140c03d5291481495070392000500c0d0101070800000f5103c840070b802403040e10400060144c90582000e50f59102d0101c8070301622651149040706148184600c09800d5124076000041080181c86600c0008400c0350754144681c0d98900320704050700008100b401c1480340242e207000503a001381c0e001e4255014020312040e149940d03404000280c1101c486007c000414041006040c805006003615090340402000d00300e03082d040350703034000145095034000e1085600041c210242c002c540c0202010144240c8858040521483c001d08654024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 792949505 1250 792948255 792948257
    0xa03050604090c081614030c10020a0b191803481a090c060a1206060e1008010503100504050a0c060804060b030d080402192d0812091908010516 63
    0x804004503030b001854086c0030144402030028000080807408201034018034122100840c8200156000884c181c0300602d4080c81400144c4003086401408080030703900090580305400c1104042000000c0d4050b0078070702107010115401a0305404041001201c4030f125075956100500d808021703664820740da130781000c401d2141300295400a4008511281910101c07030046440d044500e2500c01d9007800346c001c185aa00030710b007121280401c009860100c80b5503400c460300080c0003030704c41003d9040600c0380e01d00110720fa040c905c10540c54900007d03540c46091800f84d41807138841000c9010030008201201c0b507964440043d001c800c0e1141001003019004072001da901e03d040a0705d8100c0340c100424000c480750801e688600155450350240007100030045101885a00b0281000443e80003480c0c40c20304035102c140708031a00c0410442e0951052685030404901500880c03079184103818142d04803a5501c10556440c406466554402c060300f0344298484542542070504001c0d100c040c0d281c0c010703c61555 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 792950755 1250 792949505 792949543
    0x21201061107141c0809240405041d01090302011e020f0d090309051008060a1202060909090f070b070204060b0405010203160f06050106080a111c0f11040e071d060a03050604090c08 79
    0xa001030003591104010007031b00900030081800240ac1a4221020142d044148a4007005000b54124211056400c2c1540140d545048150b9018981c1138082d103044c1000106504069101d6215060752150817403403107055981d50000030400d070183c1e5103034005000045c24070030300d00031903080545602c03000c507180d40c0305040550001c40d505202120300d404c002d8001d4030b224144030b40c407418401039110241604a40344140300c1c51800b591020070001016008101f01c040e180d030b44620611080d2507040e044110107a0003400144540c2e6400070584440781006800d50100c0171840c24585640d50041c840600003c0c00c000001c641c00341c00c0740c070581c00744241c2e040400084860b0310480190f4020000400c0caa6030134003c1e4810200400d400184405800340310014203a592401040a5540035901104000052030200226140c20001c1c0c403149000b07103000c000c60202c007040011000c1c403c69031100113140e901d0020641c140c459510001c0358952082440f240c090310f580741d6981d1942c0c54460324001010b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 792952005 1250 792950755 792950779
    0x151d031603080309010e19060b0f040204080106060809031206010c06090515061905150f09130b210c01140d0603050c0f01031104030f080f0706021201061107141c0809 73
    0xc00003603d083c69114080140c7c0341d074155a80c69a001c0e02106180540c40781c2403c41028046d52141700900061100400018511b403600d18082d00143c0d0040048501da00184110075008407a00c0209500203001d190070181c001003490100c008081200d000341292003001c00340030300d030140f8124150040303100b11031902d5508034014000d4030f04102c1d4000d045d00000301c80c4045400c040107001070000b000d101c5076400e0030311200300045500c600d40485c4486e13100380c0315444541395080400707200c8941000300301e46d94a081000301d502559900d10300026410007220750040548540c45805580032208510414400f01c3d43d01c1c103006503205070011941d0311601c00001120036540c000d1281040c0002c0200344141000d14544030308220080041054601100030008110001003440091402a01c604001030321410103032a60070400e00140c020909214050084129100c0b0005220040f40d040844440d881403946012074a9001040b0722428119150312181080003090703c0500306e040d80071b40310700c1c02c084 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 792953255 1250 792952005 792952031
    0x813120b0609090c01080912031f0b0309070b0a030f1506030e2a010c020d03030203010f0f03020904020904111207080c0405070507030806010327050106151d03160308030901 76
    0x102c800d403240f0106501204000102e54002d4148a070310892040c10780340485500f11020701d04c1d600455200b203802c800c11200c040d441800701460800341c81c900b907000b82035241c243c0c00244d4650f800c0c024200c06500110380e40f00710621a401c910074281c88248240956640804003c01d03056184c040c030030220782007006035642c0c200000340c0c0c4100304000341c0d00201407001d01c00d000c00520309602c2e61a410060305085210168441603580007549109a07070041e529850a02140e10040880c0c0205091061050041002d41c0e41c425006401a80442c1c3c48038080d203803460306500ba0071031001504e0f0400000d46200c041d000001c0340190441e10b11a051f200b0160015081008403079007150400c0100d0310500c10724001c60f104060265001030181000144482184903541908030075016181004140403c0710040200031b004580c002c0c200c08070800489200d46002400c07074a4405610070b9642030030123106296603030400100f400000844442c645182d1603040c013804603401122491215801c140f0030a13610 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 792954505 1250 792953255 792953269
    0x30f030c031d010e010503100f060216050a14010e030f120702130b031507050c120415021506100212070305091c0206040312050d1506021501080309010c0813120b06 72
    0xc02c0141e5940300ba01041e40b005403140e030006405201030703c000d07500100343c0c61248200c2c24081e020540081c40031070000124130024064907001340d03010303400005c0200181d010308072070080300640c00d003000410401800013003840e2942506107004540705507022001d070288400000e2207190700944100802004050140042d80c03007000566815600124055a0070b500c1040030302c3c3c0204840c0361051034211208100c45c40c2001a400c4c1c11111503000508100e880720511030501407410a00241c6a0001ea901c4040301d0803500034806402030400c8800c01d01a0b510a20194141040d002030594441c10103080043c050340200c1c05082c0603105441da113509101c0d101c0500340da4154010001e034541402c50352085901d401080224040c89024000820710010324020304101824400060348014036202000745030008220214110b00d044000501c0303000b0001c01283e0340b4030020700b082550b0b6541407809031041d101e803800100d110810018040f80c800e43c003040001c0914081c4d04800c2150311000200109 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 792955755 1250 792954505 792954557
    0xb012102090a111611010f1e051803030d09050c1f050a0e0d120e0d0c050603060a050a0b03010503010f020309060f040309080a15230a09020406030f030c03 68
    0xc0700800a0014001841581005100c094460440f0382000d820f4054444118114082100d170b81c011741c10321000c196400042e03c00c001e13044e8608a0f2284041c0d500c0c4401e2030040c08a5481040000942c0c210000c1084200350140d44000e41140d68940d820b40121000301003c050440c1c00c0c0c0113030b110340c0082c0d142503003039502403594000095001d880000341c143d81c21792246500009020503a4280040740c1d4500002c41401c5000c0c0710080c0c0390307c081800c02020b12100c252200d03c1403c040c00c4103404907030240106400c2e248140c0d455075690700c8500000d00314405c2640300c207501107241c3d03101051241d400006541242e00550080c420480c060b9240c505070300003200c1c0c01c40c0390b0703100c0400202002c02c0329100130742050003802e00c3c03a1426181c0d030542e42841c0c445581642c1000072202048204400303407240c1c052104004017031140b22244103498501052002d40f2041c8015115801c000941d51070340c1c055001140e0060030030000c01024036014201844508098000c02c07140040313a00c0640c0741c541c0441c0c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 792957005 1250 792955755 792955759
    0x303060303040605130e181c0c06091403040807090501080712060b04090501050c07050f030c0a0b07030e0109060c020606010c0804061413030f0506010602030a02030316030b0d0b012102 81
    0x30400f410718000b112180c001031004545083d060800103840045411194050105c075041803600801c1043c40e14500071800c00c0030514174060100064905a002c1c0000300090382c881e0003c50048514109200a01c5051000880c58000050000307030082c0009512812129072903014083d0345e9a4400c0e158030707403080348208002580c0c901582c00c0041c4907030740825030f6104001c1c00001c05419a07103400d400c440007210007450005000440c0018003a0030800b561111907030340c006514103070032141c0b8542c0312040340038001c020304804400303e404580290071500c0000300c030034000c1000000c242000d01c0a816840c0941002d8058400442d220354850811002c50300e8101d400141343c180b602404941d40890034142d00d050803820700c007071403480400302c1c40c0200030b40c0211085440d20304142006420641d040e405001994020414110307040e0b00802520380c40340c0101c8405d14000700c1140241c000d404800c00b0300e0340c40003044085008006505c807800703050340c0072150003200800c0c29414800a010015101135 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 792958255 1250 792957005 792957007
    0x30901050304241113050406030f031b0b040303022512081513060302182a070218070305010603110306092d09061e04110109080d090302040e0303060303 67
    0x3004600c80400c4000d10320758641003802c2207a03000f68400c013194142c280c04140e0680005001803000c1240302000042e0204803000c1000b00e19540c2c9014000404050080500985400c40ca075a10300742c26000c40e5890300400748801920389450024000c0d0700c9196203440182d1107941c00b002c945581c504e15a96a580140c0700c07069280d03824010f40e46200300038520320341110300d49048075040d1158007002c804449820710108566055104111002c10485401e15600415070200422000c08042c42c1d41d20201e11446041e03a0010341000f40c200303202303507180a9002100e00003411007907600302d20b611348104580ea070b003000b00c0d0b621000b048050300c1411803c05d405100038000719106140c010241500039a603544c014000e42072284034a04003400208060850451060421001d641c06101d240e038407402d030010082e0000340805603181d101c1c40140c03000c2e08140003480310701e400e80d02520050015140000c2110075041b0400310060852820740801c13030096040510741200000000182c80c0605401400b071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 792959505 1250 792958255 792958261
    0xf0306060516080c0a0606170d091a0412030507112d0402091807020d0507020d1e05190c0b040609150203040302150304030e150d0e030d0c0801030b090309010503 71
    0x10303080040241400d40741c00f20200550016407a041000c0480d5070320841c000f08070079103045410300c900300510700003131066009184a0002c1c1c903441103a000603508003910a0441e01d00304405036002d800f440c2c005040c1e4018140381c070814550004060452140314050170440041300200b0711182007164001840e05041d40049000c1e1001ca150000c0d0780303480d000d0401410488904001081c6c81210003207104901c100c001880030f5680d050010300e580c180607051451810304568086030203103031506805014500200280501144c4039249040117941180031606100c0d50419050501040100701700c42e181c440703040c0001d540b41910203035401c032035154459904c01c2d441c100603440c0c2410300445240450100b00f1000c00142d541e0148040d014840c0072400e1b07140e10f40342c60054001005100c00c9845040380030398030314078400c2c443e003140c120408100002c10040580682d40340b85000d420314803103100c2d04007141180c00300c0e40101c099040f24007551624101e51136420302d1a8aa218200f10301e80020707020800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 792960755 1250 792959505 792959527
    0xe030d02070509060f010e0901060807020d090303090510020c0a030b1008061e0403020a0b0a1a0d0f11120f030c160f0e07140a0e0f0f0d020d0501060b0d0c0f03060605 73
    0xc0c5e04e1041810000a000e40000004090050076080000461150b0003031107a07559042040031720a10250915604560850f140507003000c4c0309202c1c441c8145642501c0009441c4244042540104090f0107140c0301d40c0c6900c0d0040382c0150032501558103d0301c05200040082001900501481404040c40742d0107500300200d0315042001842a0294410100f101e40050701000c0081e20400113444000f9111583da0402d030040322000319010711510b880260a40850600d420a00c1742e80d1f4401440c0c2100c80351100442e118014100b00108a0301519401d1041080041300130316502c000403098034114180e00e9142c6240940c207006000f07800c10f0743d001c140000e04104e280d2039081788140c20402044003141d02c02d03a407150710100c41c080c0090040c14050304a030401ea41c2c40640a541103606c55282041c1c000419059000e51001a2254400e1212202440b03c00e500c00b0703001d03092817021650f03161480410791000c2d00300b56152900280d447d102c0d1007205446441044142d4400f680c40c1c526001c1c1c6044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 792962005 1250 792960755 792960769
    0x903090e0c160f0f02030d0201050a0b0f012111040b04090506060403170d140a1d070602101a040e07030b0a0c0507080c1e0708070b04050a06110f010c0e030d0207050906 74
    0x10f00702d680d0255280c8900159900304940a0074461507800400d45142c14605541034a42c030712030381401011030b000c580e48a40c0c3c0007100e000070099254074400140706200c10300004dc00c1440380c46405000000340c00b0a00814000042c015647d44030300900c615100d0f41c040c4a041d2140d0720000e840c207504c41d042d0030140890840100801c51602c28080f8221440d030210922036107055403686107150b0b0b51340000d680000d40d000c80303090307008900f000b03094924030341800030f91039030001e0001c10fa45698170728420410841035400340d10180b002410411858000443c0642c0d102418001034070b1103c1c02d440005d1074000e189c05411404030a0766600c5040500c00c2d07079012901e801c4192074800c58000d603003140300b2400e2600184c1402e191814014014a40b5042665003040d5003500000500c4030104014442a200d5400c000102c600301d24160a0340c0400e01c03c2c460038620124104a059400c0036642043c03542e00072820000c100c021405e40d8004800310700b081c0d03661001c92140b50b8010090800013086850060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 792963255 1250 792962005 792962033
    0x904080715151d090105090303011514120615090a05010c06090b04080d0c03090c05060705031c090210080f0103080f07170a0206100e01030602030c0408010903090e0c16 74
    0xc0c0086951070b0803250095200c50943c0000d0311128600304100794848858001035040310b04c002c001c0026052064000c6d840303100c140281502c408480c82c00754917481c860050341c0640a01d60900c1600e9801d400c1c0000304e144010b8a0140c4140420050440444171110859031518402406405c0366882c5c60019030b00406d90040c00e0ba00c240e0348228400204000321700b850711681c41040600d540d0364030072501000702c03161400300340300301441d014610001a00e01074203c000c0e07030310440760303035071070b07414600e0114954810140d0300d000c400c400d4000101c40c1d00f411b03008001c4643c420ac5010419200c160400c603030940c41140c0c10402045440b00400106810200078422055105601860708203152510304103a030020390250402100006d4072240998140500758129107881c8100100c24034041e449a821007042c0000360606a001001c203240042d0102124001c10440000344410355503801c018150100511500359200d244100103944516034070200e8403003200c3c10121000c02c501e02c0c0c5890340b24150103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 792964505 1250 792963255 792963293
    0x61106070f030605220c030b090402040b1c050a02100507050c01031d0106030807020f04061d13021806090903040f1a040902160c082a030c0603070c0b0609040807 71
    0x74900204168940005c10380c0c0b42c080c1624408002442c000b00c0d201101e100007114020140381c01032403c07480e6600b514483d0483d40445000c1f84030b02c41c3c030b00080c00350740103016200c00394502c0301984810001c000c10030380141c0b4002c9949404802e0200016110380c86a45d030014459007041c11a170815600950054014445096140043e0f030007000700e407400c6500c142c0090300c800102040007811880c090100031041c1e401658107022088c42e00910340e00e14003845400300500c801340c1000811810a0001480d001c5030021b003030034140104015110b40650050320b8540c05900400d0006050b84c900000700c81c212103450f03d2450480786055580076500c1c0d402508207150304420480007505e03500394005004007003524081108070043e41d00d0000c1c100101648030a21030b030807094180c207500304640107040d940c44002800c64498045000024248440900002e5100e04e0200511840c10351260401824500c00c140c4600c0302e03121441001a02c03207003110010720301c40303003041034000091100700c902620300d5039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 792965755 1250 792964505 792964511
    0x339030304080708072103050f09101214010515070c03060e030c070602010c0503010e06030f0706110c030a0503041703043f0b0f10090e16061106070f03 67
    0x100290956010750b21054556001c01c0f41400912010301a54004158443d1482c031268541c60103078003400c3d0000809014490042045c0095081203400c030f42030701e080285001030111803901c2c0034001c104d0003010454114a80606801005d5401e4203841c1130b50700040410b04011001c0c00002040d522201d811181068468400070014099004010048080102071903c900c049600c42e45841a594410030442e0304040d0000e1156400104580c1902d250180007041a612080131902e4641c2c455210549403003038500001e24154010301542d0001c500702d0903500c0c3c6442071010582e44024020000c0e21980040000f0408010390300d2840212365200c2c0f041c5e03820f00f81e0361000a40c0c0c10401824814500c264424072154110306910403180b460280d803011404041907481d02c0c004108000c1011701900416408149010071100441d4010020800248000c4150181240c0c44016591100004240390340c00815050700601420350034602107402081d59594078007003107485280030707401003051581d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 792967005 1250 792965755 792965863
    0x9011206060306030303050c28120f231504050c040506160c1e1202010e030d0c06060905160c051603030e0906010c02030a0b0a11031303020601080327130213031103 72
    0x42b24000c0d60074045010500003140d0207154101007005c00050004001c000a0008004035800f500120840341c10b801c1e20006441d136039004501c041c510807038212503448100820307071203400883c04000c0b41440b0710400c000c0d961242c0d69815050000300c0d81d000e0100c51381704200203012070b4041c09201c070300d164014905140200f41400102e401d00611051080000b030202c80f45605100743d80c01a43d0007800040000c103c41d16202c485c1600048451000e04100400c2d104900280902000900b825800c04c440d0032407482d5403841c01404054043c18418003500408000441c03643c00b0301e0030300784260b802502401200c03031195140040c3c00801172003031440d640c2d2405507820f005002005584201c081036040f10a06030329040c082e04e4000e050303000041544c4100508000c0d010038070021060110a03007040d00c5110110000655082140d00310201c9040c800b1550714545a203001607602264013841c402054011028289911005058103111848180d001d03108004208400c034400004110084c2c01d20140c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 792968255 1250 792967005 792967037
    0x624050a0b031302040c02032205090f0601031401060f030b04020403050a080304060f14061804031e140304030c03090801060e1b070b0f01050109171209011206060306030303050c28 79
    0x901b0304e04a0001170340003041010154000b01e0031000a900d19111101c0410f2820f030014000503402031600d540c107001d003030100e40207034041c0e0004034196403248880c202540e1101030003840e2041003107090001a04000402000d42070501c01c840c140e903001b00281c00a219140c647d0341c51503202601c203c0d401552050b4103000d095140c8100603091100300c440910509182c030421074111040b400d5111640e01c2c1d02d05000c00030b038001c104840e42640042040c003084800800a40f4025024040c003400c0d130380300008100c10190310bd00e0358802d0038070a844014070f84d41c031828003500b280d405004001d0301611480c0410a00c0048400e4420b0140b120008503280450a0341d03001752032681070703804187c1c1d0000000188000d40e0450414000360440041d076201e4503c080483c2c55444d103107440e40303c40d000c0000800304580e900c60320179101c0c810000441880f080d9924500140245414401600001d20f01004a50200000421541c541282841c1c2401c40c0600807400040060710b24400030034009140c458200503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 792969505 1250 792968255 792968261
    0x30c060f27060726130c080616030e031b0f060c19052b06090e0f120c160305150a0c05192006010f0e0c04151b0624050a0b03130204 58
    0x703a105941c061746400d20601d024440d1105170341000f03800d80c0004040001031256401516000802e070300d03002c5030a00102d121282503210b45141034407610000f04401500c2200051613a0400c0d200f0b40468040365640c081092107805684580001c1001e00c1d800c04c0a544e124501510f9a070710b10684d1540c003820140866406e1007042c0386d4000c01c0079181d80c01005140500d10900c0018070851003d00070b603c481c005141d482c1c100380c81c0510501400898030580101082040c0141814840d07010500d090701c2e401c02c0b5aa58004ed03800f510702c1d05503140001c0b41d19119004410610a098403003901300144110300d80b540b0290903440400300b001e103140320000030045601c0c041c0081100c4010f00030a5060031011100114a03401a098407200721013032018060158007142c0c100c961002c00b01e040c80701c2070101220303590350508008400721304181e45542400340d42e5014009183c15031000f001c21604018000441d0040d62161540c0102913000410214107100011a1f200d00c007129641d00300d080d41d5000a0807 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 792970755 1250 792969505 792969511
    0x8060904030c0305040f080f2104050d0804030f1a0709360203071d0405130b09070e040303060e1302091b0915030118110417030c060f27060726 63
    0x455441108282d581c143c062001d6804002036207100340342c4005c0c100c4c46c0c08060ac50780c8500303809503610b03132502001e2202c13078000d880195a0210209036900524248150300100c1560102c07005c05890000c5644030b40901642c50840d1003d1820020b40785441d60400c1075554005640400d11403007440e07260550a0a00c0103520600c115202d81004c04040d11414400542143c078460180e07181000303219603030400b5103103001d1055214903d8010b13556501200c506009441d80304104031a40c0c801448105505031300f20409903061403d44210300c6d5a041c1d0880016200400c01a4100c40e0385030100c6c58601e5403818280d0440070700101185806010310208540201d040e140d1444a80080700501001d21aa041e0b0b480c4e58621107014820300c450125000340d1031086100f0100003611601152030a514140705544003c00840705031491807030040d80004403e4822075241c11108803a412112505080700040b60940750160000c0a1a5403070b41d00594011203400c030f400d074051024100c0805030a484040b8a48 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 792972005 1250 792970755 792970769
    0x60903032a080c011103090a080903190614150117060102012018060f040e060a031a01050a0801140a0e070e01030302030405030d0c080d0b01050d02071a0708060904030c0305040f 78
    0xd521100750f40e0090844031611500e19811004005000766000c0001d4040152030304851920b694018410000785042c00020014016080b000c6100c42030000e103900c440003404007140c1102d500d90710002c028103075400402855011600c0b0380038010303100c44050f505c0755000700103000002c0c1465004038070800d25a0041c00c800010400040e180740e41281c81380c1400750304841a2409803c11a240000d107802e401680610256110550001400c03070355800142c0c0021900004141000740070304c400711038508000d006403806245602c03400a050b031414410000d40265103990020706803074001841000e0700389a4403030b2119210f4464082003558480c80124021403003600110f80d07441c42d0106060800c80c403101c0080c180000d056982e4007088110003240c0c41c1500000b0001880400900103880354003501043d05a0b840c80808d40742c0c1004554108103c2070540b44c1d0000c071300c40c1e0310b0101c1141c48000440d40990804818804100081e0048070070088041c03103428064245502e640c01d80b8170404160384085 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 792973255 1250 792972005 792972007
    0xf04180204060503152806060302220b09120c030f1506010903081206030a1b1e0b04060813020d030804031206060e060c10050925060903032a08 63
    0x200840c942445200300404055010309040d41da18040e103003070500010112803400c0c502d10703c50f41c41c9078941703a03c01d082c444030860b0401030640c65002c020000d4011180c240f90850007074401d000c0e1348101d0301d1050100d4a8071000c3c203140c1480b034010310080203402c030344c46480c91040354030320318042d60709100c1d0345030a0004e03c009020300901d629010001e030001804013410700c5000c6030140701142c0c034041184c9400c8a09052031030a51104008245000801200542003aa503248402c89460101c481c08084800c1d52904119440b170041350014101880c1c440c85000f079a041204120090041444a80c402e070a002d5030b0403c0707001381d0003180d180911b104044000420100401c402c254100380107048580317904c0e60410149061040250580011a449a21035140480d1031a20584104481c802d2001d030305509000d54185890301c260b940100c440c145410740724006640710700e0140d582c07010003111341c0c540e0f580c0400b40c9940ca09a8008402140c84954410385040d0007003203040460442c0700700e0703200324a09 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 792974505 1250 792973255 792973301
    0x1030e10050406021306170c180a170f0303010506090f0a120c03021c020d06050c072901060f020706031a090906090d022406030f06070c03020c0103110a0e0f04 70
    0x102480c2c041c5c582115040c0600d0007003241101c0358602c59598000303110b1281d00c2c1d4a600b581554400c650100140c0c55101c6000d42000c100403407035480c2c10481e40301c4c500445031449698950580c4a000c240542078014a0500c200095864004916840d20318040c113101c248a49518441203110a42502034810700d48014007081182002e200da070240181c4180091a0b00300141d0024110440600c40034059a0321b60b008100c4c0c0c11304250840700050f0340801a0003030744481c1041c000d091440d60392101c080741141000010024001c031040000310a40340d000c1c00311142000800c1d0f00600000d0116203a41800c5103036421140c0701d0402d101c0c054000301d0000d060300d1800701d0f40e040c40c1100d41c0b80d2010464020705072060200c20f00350711541410101303a400380d2855880202181c0351120301901c0c4030040c8941e50900c044290469045c100c014040e900352103c035420980150107451502e01c20b01e56000f010080e0241082c4500694550114014980181c9061200000d4180c40c08102c0c81d00707100079a1000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 792975755 1250 792974505 792974527
    0x350a08070305130f03050f070f0501050f040b0a05070905120610170a020d02030c03070e180d050d05061306081014090303010b0706090c0e010e070e090601030e1005040602 75
    0x805580300303140d89801d0055140210a4014450840e03000808480040c0b0070181054007a5003a80c100e4418103110075241c840900707001c0d0090002250683d015480c1002107805104148005449980c0045c120203142e02d940d08080000d02c00241110704010300c446005c5003d036560700058a0540d5810700410140c02c0200003040c212401e90b220322400c006901c40c51024860100e50750103903540440f628900c400a07800460b040c5010700122903890301400700042652400c0c03110307075801070540350b04180181030507206940e40c4001111000021500074000300f550f08075590401584088003915090750407141c0585401507078425008965560845500d0920200341841503404003000801200c10318180300420f16241e21041c002c06e000030700c00192000c1400355030303041501a1680f00c00348805a66858680c2500782500b8000c2200b50003001c0042401c50340315914480c041e0300002c1c040d411030386503d8015401009100080c2000340600040400c524259100b41e0f0720a900941c000350b51010030701c1c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 792977005 1250 792975755 792975767
    0x20f0715180807110a05016603020a140a02030f0d2706050f04032021060601080618090f0c010c0804062a031106150904350a 55
    0x340b0280070304d070300e441c040007280e9000e4100c1e0381c452440011808001440458111240e84543c520902c0c14000558940f400c2455480414230101642ca80c01401d80e1004002c3c81a50400401400682c0049111400308205c5410070103002008412989503460b82d80c0030a00703012131200701480782c0d04403264210007070b5040032030728506e500110006018070303609d20800c0120401e9402072400300840860b4680c5c00d0304840084501858020000d0720500e074580d4003540c550480011007074000c2000c002d030b96844040400c40140c808007014090a090f0b503c80004659424009288135400501003900100c0d4a00f0b00f41600c0c0905668009450101c08540f1450f10701248440042c2c100300d0017032009004941c0300340949058988038907100480b112100146580440c9044403842d0398180f800031030003015000f4035010600b41c50f10007030307400607a546000014800c01071082d082e0010601c0c0d00140008518100600190500003601e0400f00030307040c17480740030b0740010140701142640010507400c0d0b240c10030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 792978255 1250 792977005 792977033
    0x5150f13120f0b060609060717090618012c1e0a0e040c0f0b1c1407030203060a0b040803090d02060c010c0210060906150e0315100e0a020f0715180807 66
    0x5d40d08030300d003400303040108074244690240075141300300c0c160140e94a100d403d41159950075000f8080c680740e0703001d50641440ca10075410000e01041c20303503040c20800003502c41602d404242c0b17001d14004290314003060105800c0c507107022880d0355a480840302c07110398a035150007018004040c980d841c10300d01458008801e982640108601d040c01d024100b054081600483c2c40c000340c2000d02d0b070004a0820b6405010300042180c0c030094034840020010120f5169020f1441058202c80c0d0801480d40c80c40100380340d114601480c0d0030b581040000000d2410702c204000c690302e102030000c0c0c0ca07000c2a4101d40d421900425004001030f042480401540030590280070b0141206840c02c200340362070440d195800e00005c1c20b0880070b00030b40b850070200c1071360180100c00700559450310414852902210182c2924610301400e101e020740c0f031000c03801c4440c0703078400d45455400001407585000b686880300400303101c10702d00c0c150095072508510254000000c50740e0044d50f00c206002c603200d150741e1405000d000a14 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 792979505 1250 792978255 792978259
    0x501180e010902060a210f0b1c02060904110c0d0804050d0302030603060f0403170a32060d0f060e0109030e0409050c1504050301050115030605150f13120f0b06 70
    0x80844000f5a4a180850b42440203a0900c0c25080c82c00c841411084c228101c1c0000f2040d15220100c00c58a45d15080b081c40c1c14004c5904078045100540b03207241607046400f010750040300c14000610542440d81c0030030f03001014868060300703140d0400800361618a0070504400061a01002c0c402004000c002a2006000500301981140b074817001090382d0b02c000400c0210045103840100d014140a0031803600c2c0071010449203045441e01403004005800f011000170103440c1c90b41c2401044c4a080412941c031140c094440c903220343c4600c0200f145c0400490801d44d03a02c80000104000200c01e0310a01d054062000c00111326140d050030050f02032910f001d00381c1e000750b04010040c40001d0000c0340030704030318004950104140ca896040d492550260b0740165801d5031900d000803414111111844500b800316940500040d81c41d08140901c10380848040030a4540c1803003072508a803000301c05070800c0314441007040e511980e0781ca100104030302d00f00b105a55510b06940f402c0e003440340000400e5409602 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 792980755 1250 792979505 792979511
    0x19020301051b12151009030b011217090414010f06090506210a180305070506100e0c070204021306080f01050306090309040e0a0f0b0718050d0308090c040501180e01 72
    0x641c96000da00784a1943e4032080324a00e040091a40e1a011a01c0c084040b03010701107001d08080582d000e030400c0481c0c00141c810031900c0d8000203000c102c0c003940e1800280e0010320a074140c1450031002c0c010742c200890042d03000d5283c801d2964001000b0303114038002d041034010300d04503903c3c10313001034015502a08014090181007101c80724140310700400000300c40800d40b405a4075940c1d16802e10040001f94000801a07650702115018545d1141c003402d07400e0b000d08180c2d0302644985c0094400d140e81d600c07400e20220004800100b034090b0303207800340000c01d0004c0d101600e0180032110360a02024107401890100e10402c051001114007a10004c0c0134040c141c0c0100024180b404480303aa070b00400841c684260f40741c0d600c035100d07083c040c0a0203015030340c00741b0604e00c0e58126103131031415140c08541d4040003804503002c050201604040010480c0e1000c0c14800d0009455101100c547c1401840607040d88901640000c0316241c80c85054000d18040c0750090407001c400c90844261864080d05035493780c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 792982005 1250 792980755 792980791
    0x714031b061605300a12270b09060103020d12050c1618060503060a0b0d08040909051516030c1b03031b022b090b27010f09060f030207051902030105 65
    0x71001c129010f00e525406c103c01d004650380f4a9501802000040078090010042c2c104500f9414010412403180308246c0c2d10b08650341c500105588003000d00c0043c3d404503c000000d00850008420110494000c1c900649442000d1100601c1c0855445410780f202503040010488500180f2039040b0710602824184051442e00c800170b5035038000075061501142d0358580d403e12036594108219040c1742d0000f4929200ca07541d228030f00c000d00c490b8200384c4540c05400c0b034811038801c0c4a40a00d01c2140e0404084108503130004003203005100d441055018000120110401101550300200390a0300c2554003007180c1041c092401801203440b400321065502c806200080642d03030040300140d01c0c0c200b000a5080d9204401d08668450490b80840c4c602d1078005001006044045030301d2034034800c5070040c0c0c9201c15405004449c07030700c07100c4c0d10070001510a0a061005900c15101215940f0240c0380150404606448560070a108800644c0c1f440e5084141401141000e01030242e00a201601480c0910 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 792983255 1250 792982005 792982093
    0x80604050f0109020903030904051014100207030b0a02071406090d18050f0102071a0711010905091f2c0c040303050a0f021f0e0714031b061605 63
    0x1c401070048108258004c242d08045880801c250b80f40207400400920043c10941c60302c2c86680b009002d0704400100c000b040c010a82090700c4240d01107102e503070050403124030f1a01c03943c80c2e03d0400740c0354403a0b07103408000000204074080007000c0c07003c81c9540a0700c01411300d036040b0340c23810441c058014240500030206c0e000b0068030400d103d049460940d0414581d42c2c2e27480041b42014007030b40200b0942071034040315400c0d20094801500c1414030550844620b001000015035011039184140c65009204a0018140661658540c6405070030f8140d0b080d403da468a6010707101c0c0850110300310783c1008101c50303071b800c1c1460038007159044040801c0e0715240901350b407001855840317400d040070103100d480703002c120380e42d0310801401c01540e10120701c0d100d868000e58051070140000c003551201178421450b0100b03007245c01541a40004100a000b050078426400050011540c24050f031035110500344125628488041c0b842d00d003491060000c1c004210100716501154151000d60580105500381c2c1d140f6a9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 792984505 1250 792983255 792983281
    0xc020f071a0739081b0a0308040f080f0309090133031406090c040314070902030c09270105040905010e0321010e0714030a090f030503011a0f040e07050c010603050a0308060405 77
    0x200484003090281d01d5801020881800047d400280031a40c00240050700183c820494000c0e0742000c01694840c03c041d452032690b90003070700310840e072006800300100a45110114044054840310113080e080400c140b0031580312481c03d4044030b02003500c41005240000320502c04550100089a181c04941014100307402c0c1c50059000c010001c1d07940c078a03811034010040001400038856008150341d00c1c585000c49a03004d030040c50916010b0301c00494410400440c00040c400307144a11801c0001e941c0c40c10023008050060520141d825568a80411202001c1400101002c01050000100e0442800d400e41030303621050f800b40d0f0b000065042072180062f40316400203512032020706160b440780c0315903803250700606203103000820850111b00703034504050b00b010103541220b4815070300c0b54100d44200801c1c500c5104030494504441410001032040c040c94101107038028030780746800d07030910f1003840300a42102c0e101c0c0c000341da8591101596504042d8440c101c158804416a010b01150034100501004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 792985611 1106 792984505 792984523
    0x13080715171b04091d0d020a0f02010f0e090412030b120c0d030e0a1e2103080c090607030908010c020f071a073908 51
    0x8100d000d200081440c42018000009540d500700c2c48109859048034a000e90942c2400040303180c1c0035034420f04002a10440160000e807507540a05854039032541201001c40d4001000070000425210000700250390a003450089800400700c00e0300c80c1c500000030780d50030005040801040c030440d00c80146507040c03a505c04003c4112190240401d4100844001c101ea51018544e01460b0070320441102010380a1710f0300d00d0b16900610f0000b4003900b107942c0f0200c07050040c4c000c140c0c0320a0030030062000400b15040c0d00c23030800d2a031880c1703006049900c4002405100b048030014a58400d1081110150000149a581d8920309444c02130030002990150002640c64609890031322800041d858201c0080e00001384005481c00820042d4500003031100e40c401803007400100c0c0050681d0b0ac9450840c103a120000244819180c50f44401d030707031001c90494030100f1107201040003030000f00340c00030 = true := by decide +kernel

theorem cover : BRFrame.Cov 792805755 792985611 := by
  have h0 := BRFrame.cov_init 792805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 792805755 ≤ n) (h2 : n < 792985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
