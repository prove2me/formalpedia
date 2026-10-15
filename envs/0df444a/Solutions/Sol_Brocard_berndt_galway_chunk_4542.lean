-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4542
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:57:31.983325+00:00
-- url     : https://prove2.me/submissions/affb493d-b419-4ec8-a70a-b7d87b7dbf65

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 816726618 ≤ n < 816906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 816727868 1250 816726618 816726629
    0x915111006080a020103050c0723030408070b030f01081203041e0204140601020d1704171b0f010f090302060703270602071a070c0b070e06030c0c06010906050a050409050304 76
    0x41c08100282540001c221503540383e0003601c0810a80e0340300320445986200b601c00c010503d140e614160500142d43e042c0000c80545032104a0b030500f0348460555281c200070341c100b40d000650201c10440343c0d00380c10720114054424a8050085c41686404104090001030401490481c210503a0f18003803088056060900350000c105000e1482c1002c9021080c010a81e0005c0c010f01a03e03410b204d50a01a0b104071a00c10306201041180b942e40d0345600b40d240c1b090036a00b45502c2c1040001c1303210808421001c0b21104112005020080030406019084407482001c10386400c3c2407600b1000400d40110b0180c1d40a0400e080100e1340300c06d480c14000020034651186480642d58000440c00c1c030a0355070180100f944150b011400c2101c40c0032040388600c200b2240200000c52504114000400c080c0071150004a6400c050303400d00c1581000413540c0c2c1044070185800c0602066246641c6020800d00e401090800300c10401181443c0105104519502509002e20340310201142003000801c103c1c1c00501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 816729118 1250 816727868 816727871
    0x6010504110408030a111606080702012a0309020315090d020c01031505040218090c07020108060402030f0c0f0403051e01052404090c080a060204080601080d021b030f1e070609151110 80
    0x3908c524001e0502041500c2c200e0040d0300c0c01c0300e21240301000201101701d0440c803850050080140392070031809025400000c071b03058046e540881580f46038112030103000b00115801b0b010720b46141a0024540400102054101401d2122061000308080c100e1029248250380c05070365090031a180c0c50b5841c034048c01507a04500004204008100550b018041d80c074402d82c1c989440762030307400401051340400d80d40c44a004c41858042204201d10100500c0b162100688042c1401d030303a92583d6060450310418400c0724194982d0a164000003881174580c8100c08003180b805291010900c0b00e40c0b111598450360045d0740e00c0c15042c0034041d03401c002d000246150760445049590510f414000380d0064443e0440340c1c82404004540d070100410001c032851060b0380117182400c100d070521210581c0b19020290580180b0002040420090042001001c01040d2619018092055840c9071140380c3c5d00c610204104923005010082804c2925007040301c1c0381c45d140c0c0c1c801b180c140040d070818030007100611070079 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 816730368 1250 816729118 816729163
    0x11a0f061e04090c03020c1507140706020d2301051c2a0f0305100203041110080601021c050f130b1b0d050403030e12070801090506010504110408030a11 67
    0x100d02140c0240b0581d07120308001c0c00ba810148405606a008168021050b43c110507100d4017503690b160038103036019002d4641028030030004c94150065502c10714040d10b90580010300f100405a0b076000f040c1003000c0740e00820030245452981401c9a001c103000f000d00c50a04440c0300100c841101000c01c5c4615041486c00e800e86820f480008025101012100000000d0340d200085105070160b1442c100c035080006800003148001c418002035000030011504000f00f10121245030300d46003c1c015100c0b071075403644030f000d0816400182c074141c0402000404213031080e1225016a42c004207850300e4041c00070030562255040010658500e410f80c015516140000c507100300d6034060a842e80c110b02a071401a190f50f0307150410201e40c203224501001d40070800c035401e00811030030072001044480e0951000d035210291140c0d11542524840300041d6020342c0800018001840e0600c00c40703400380441000b00d86071078a0701c851940c590043d8044001801154408001440e00c00d120184800300702022031200d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 816731618 1250 816730368 816730417
    0xb040e01150f06110d2f060a0e07060f051303050f07030605090313060e181e0c0403030e010804060902060304120e01020d020c150f040f03020111011a0f06 68
    0x500c0740744078a1801581004001805602803040031521252a001030084c4114201c0e068842201e966800030328040310a01e040358541d140216040500c0d60140940710b03601704000a0010707640304603074003502c40c1c01c0803404104a603001030305c5070907074409400d1940d00c8455070001001c0080007a0f10241582c080c11000200c82c841c082411010380703115040401443e152040030641d02d000310301e840e5081020f55031060005901070300094410410061403020300d80c2d070702044940c186105468200400c441c0c69044030010040ca008140d12841c4c5250742d41c1040c0c03850714020302101110030420b042c0882c04003c2000c0c042d10381c008c51740c21038000d04803e81d68149494002600c2d038509004038005100d209102d007040d0f1000c642d000c18070b102c940c000c10055440008000c220003000d500701e41c3d03207c800c021208070004944040c0009001a11141000070300c3c40c000580604c14260719904641d03d41240910009140070321403040000c00e8071080946850039011038058851030b620b01440600540c0c04084 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 816732868 1250 816731618 816731651
    0x60f0309080f3609040222140a0f090209010501030b062107110f0c1003060906140a050306010f0905060f090f1006140f090102120f04091508100b040e01 67
    0xf501864400c03541d02031841c11440748202002150280e0300449902c04030f009450607101d120044005400c00e150951120842081101c1d92008151195007144040109103421481044501b010303c107424010200b5541c002540708005000700c6040c19a0307110484100d84904c01a0380000300808407507110302d00e01c8400c2c0014030300c2c205d51100015201054000000202007014800145890010b0240c801e000081080d400c07907052051081540c0e41c90700250045540c0503440080c07144024415141c0103074814000c03964150b030071041c007d620000040080922844540f02102d41510f800262500c443c4000f0f22840d9404031003076400080c440074801007040c40c0c07500c1801100b6141440303c00642d2101d0546040f42000041c42e038042e4280b0655500310901030007030900f0307401481941e00c40203952203108540d421580d612100080007050078840104240b15502652010001c408079003403030300b00265902d0b00c1d92003201b282c80b0b072500c03a101d5450f02c41d41c20091042c4801070003403282c1c3e40810007904 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 816734118 1250 816732868 816732907
    0x301090614121506061306090503010f180809060409060b12090601080d0806120f0a150911040221011403120f0301120c0b31060f0309080f 61
    0x7214500040c00401d60380c9000d480c0440602580800303070501c3c80881c60301181090f40248429003015003040009540035502c1c248030b015020a8540e008000c4c2010141802c4452202440a9a03490302100c00301149040d403145200326800343c892650b038116200400c00d240110b50121200c107003004008500f0003813420150100c401528100b100a0782c0350f1461650300c001c00e100701070050f0400420b0f1a4120300c11103241d540901d02074404904101d00d11003042c0303800c1c0b0b08406070400e6000700400c00c0c1080281d48035450b01c0c58281c00140852103050311403140182481c8040d51040d51300081c1405644058510b0703445112907001d440703003a03603035a802042c0d100204050040c0f207400380e19501c040003000002135507000e00004200d28156801c10860305000c4043d480282c03060821058005548030840000705840740c400758280c0090f01034080d1074213030424800600e102d0140e40610500c005a88001414030306001880c02080049150810002903c52904648902c110014010000d0a40c103240203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 816735368 1250 816734118 816734129
    0x616061103190606210b18160e01120218030d02030a1101051e04050a05102316200106030c030201230d200d050615070305040510020a0803010906 64
    0x4502c50119802c1e64200c50305801402c0208400100b02c0091700c4540c0c22196040700c0c034200c0081c11303000e200d001550400280e040c0e81e4a145881d0200510b5451a02481c25071134411700f0015000e0002a002030201c98003101030a01d2242d022496820802d03c1c0b03400e8010850700602034400d0703d09200300007504c81e40110a0540440c0c0d81c68070a4030030b0101441028414040940c4041012040c4da21000c075081c1e001c0d0084c0c0d0b0610030a0b0300b5901151050003a1500748150041c001006641900040420000d100700c00c40d25203080400c20800303100c00c0d015410411207903d0700300c000310030f02540708000c407040e0200d02d00c65602e4a20040304100006d0065000d5900036214400c0100b0307075043d00000d111401c4d241c00b00b582d13001d108176030610289803c90075100604202c1894240040c0c0754180254100e124118003ca40b120180162410030703100070003140038041c840e20725150715902e02406a104510401340590f0185520250162080c04a413804c15409100e19a0700e581d100e07038100c0901070078000c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 816736618 1250 816735368 816735391
    0x210020601051009050105031909081c0f0b13150816080f030901090603110403020d080a0e030118170405190611030a0c06091b090f0509010504050a020616061103 71
    0x30304a28054130403d0300300c400582d100c1d03195a580b00300564000050780c04910b403040d2504178030340004807010090174070a1441c1c54140307201c031100e40710102903c01d1740103074806480c5441005e04540d115081a02e045940f0094041040d0a14694180c0c1008d8030394000101c0c2e0144401e144d240000314641002120244001c03645504030701c10007192207100309044280403030b03001ea404001d0640a500f11010800001440c0e0342455a203030007190f4602c11994040f03034103910026652220541229400f01c1c0070405a00030000306400703840d80031004200d00c1c4082c0c40000d8018003180c40440d00c40c01c85011b414003400141c08140642042c818a00103402007070702280260020404280c000001d540b0005c225070b943d0b1540340e48544400000306a0318005440551035032076405030500007800c50300d005215211001500c252a0850201142c10140c90014540d04002c2840f0104d8000071710a01e0050b01200c0d41540d503940380ad02070036901c0c02c0f04402000c8034109004003507060b01184c0514802c07040f180b01c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 816737868 1250 816736618 816736639
    0x902041409091b10021203180f07030818040e1204033012091b050112200c0a0b070305070e060715151a0d060b0f09040c0c021002060105 60
    0x40c0035111402c3c09001582e880712101900003614111580e03000150790303801994907080f0011100e004560046910b002c609088000d41151f02404101c0a165180c002c1e0240c00300604540c0e4034211845500f2010f0f10128171241d20180c00c0e91254030200c070189103117003180c0c060b2a5004950700c840e00140301c10f44101c0e0040072002d10005c1c0200320160300d128145030321000100030400641e1500c4100713070400b6209a03075002120000e19409400e25000b050f0300c2e0203910903842c002c001419030340304d2040030f268107081550001040c06142c0d0944070f00c0003c40e000b01e8840d030090108034031f01620200050311140e04d14007444603c0e0b826a1015000b09019942d0002e881c00b9179003800f82c0e6124020005010140600c0707450144141e50b44041350981c071520340c0704800b99840c045550000304540c0b00180103480040c41500d110b01600c0399030010702202c541da50608890040c0004140034401555010350b4030784946803405840351403609141980140980300e82c01030050001c3d0380d000240030744c40c0118903004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 816739118 1250 816737868 816737881
    0xb09060105030307080a12090203060f0406060b0a09032901090912050a0f210e010b0301180206030f0a0f020f070204050606030114010c05070e2a070b01120c0902041409 74
    0x2013280e40d0740e40c2000581d07141c2604c070702c000c5451b41001c07904024440c2d82d50f01d20000507602480814000c0c0a0076800a1075420a410030000b00c5815a101604c0079000f00180103156400044070382c101e81e0441e040030400701541110514401c04280740d811600028030004c0385503203143d44030304801ca020313030480c00c442c15506030140d03030307921440ca03110300890100340070701104a1003018590092001c0854810313503003412140d080c1c25140e50061030400c6035100e4842104a003024411000f422000340450611f00301940c0200b585480080d042c2c244070143d01d00058032030b01c000c1e00010840c20200a0071076481c4465107910a40b03400c9058128032135414071021625920303010050b281a00d000300d0340701611042c20700041d500f851403030f031044403d070080080c002003d0014070005441a0006120040c013811180042020014900308201c030b4001c05200050100e12031940072410355664050124040364035040080801039254004800e050000801144054084440c7c3c001140d09440032406511000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 816740368 1250 816739118 816739123
    0x90507020a11100813050f12090102010e0d14030703020403020d150b09010b0a030209010c120314090f030a030b180702031c1a04052a13090e1023040b0906010503 71
    0x108030f00b8000840c190040f8a2000140c8039100101d4860300c200d0746c00e02601440f070350500b00102c0c901d03207144101003080021560280940c1003c4a5048060221072113260070281c01d503070442c400ba2040301004400140c080b40294100e8001d103400400103048000c85260045641d4421485040c4581c01c0c800f8481c12424070038105416140f00392181c50400301d5000c0110025003050480504018020a03113a01160089100e407008040c25075000c01c041c8610782c1d00380000c61010b4504120b650040c50440c50103003020007600c1c0d0b948050700d40460703680b072000002180021110031070904001d803202400300643d00080100708412034a1108000c070b0f0082c0c500b06003106c59102c000b96000e15010085045403030030307510560340001008801c80d072004558490001c00d00c60f81506008038800000c0760b500d03200524140030002d0009010600c0f401c00768081c040d45501d80e003091505010740783e00c0401c0345144541d070000b030340c81034411508055107480e040000c0251400d442c650310724001c2a00100c0c982c10007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 816741618 1250 816740368 816740389
    0x40515190c020a0c180204030b010801050109050c0f18060c1b0108060102070305120304080c07030507090b0907020a030804020105041a03101505180315340909090804090507020a11 79
    0x5013803c9001d1801440715007064200d20000481d507400c00001c4001440042e00764040c04100740001100d40c18100c1c1c510849101508040d80e1380710600c08025040000d804540e140381c00c01c08c8010000c0e64020210380c1314007446150f0703403150040400c0010100d83d0714000d210404401d031f842441a84500d001603031a201c4600020341240c001c0c081d0080d00c900558001c1d90458883e024141c50800c26244940c2840c5840c1c00444030f54205090401c0110b105003d0001101c008686054003410500c401958074400c4580050030300c54400000303070a41e8001c0095800501041e00c1c8408030844030340c10070710107503c03c60300009003114503400400c41200b07580d042009a0040d4035128904041c1c1c0003160a03210b42402d203650f05200d42c04030361142d003841100c000d000e4600400b0703a18000114211519281c0c44e070501d0000d1a41a907070204480f15400700b20310b000c4612524000491607502c0c03c10b0521403180341c104800d00d6081c04140302d40d43e030b030015911104500030490b10f0f401645030000c00c40003901 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 816742868 1250 816741618 816741623
    0x3031a1504230d03090608070e0f0904173c04270f0501031119050d03111203070809071404020d020c070605190c1a040515190c020a 58
    0x90500040c002449024100300b803018448580c0b1552105690020b208021180b0b401c42c0040c200007010021282c00580043e00002242841d222003192179020070109041804420300c03442c10500031500740070500c0140160458204d6900350b80b00c680a40340d110040702e403900a03038100c9920301d650462000001580620400c52204145450710b0b0510b65200114240e600611007500ca0f094800044083e01c5403210586842a001c5519031460400d0b40800713402007101e6008505400921010030203026000b030540c1c40480304007140d1002e6090440315074441859a007010701c600300c0e418240c007821001643c0b181600342d4894a495844ca121507803500c103d84100901c000042e0307444041407429401401c0714480c074807401400c0003551200340345400640c5d44a10081003000034100805000c0444140c001d00285c01e28084142d00d503582ca007868905513150340050341516010504201050001c0f035841c00450f0300d00b034179504080b040703884984000f0540c85030003844e1074954200e03107002260350a0286d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 816744118 1250 816742868 816742909
    0x110714011b02041d0c100c0c030b0402120102040e0a06080f060106031a06040305030d1b021f020c2d010c0c15020408030301090c09171903050c100b040501050102070317090102010603020d03031a 85
    0x89c036640d29102c10085c0640101d03030058110819814841d000d1025000034440b0b04198000b5080002d0940d00303c3c1c11540260900d50041d83c001008140009817280c112a41441e000070010301d01c5c2c0b4401c030101519041c0a601200019000040c8100000500181104c000d03080201442541d21401c2e0743d80d020390316901580083d2041c1d42035840b50800603a0400304900c015190982c4100300a08106806000700000e420020b410810138014070242031100049400800404541c2c5002901d08140b48400400010030300b0040e403400542901514005d1050004990700e950b101d01820340981034a0a000c40007070605100065111018401e07070310481e035610081d000402c0032102074211040700305000d5041c46400c11483e02460003c2100584c0c00200d04070000d040b0344110200825504103a100c80d04541c001c040500c0490403003101c101507061740d1103c103603655042000613809440f865001942c802480b445100034150181c01a20120070349115191041409104000c02c4140e40c0340900a40d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 816745368 1250 816744118 816744143
    0x106050d150b13141530070e04080a141216020114010602070303090e06090c13030f030905030d08040503091309050a03110714011b02041d0c100c 64
    0x154420b911641074800098440350b00c062070541c00703500383c440304600046589551420840e09403050314040010708003c841a02c41000c101140c642019901e800d100c0501c8584145034038081410809180100315403855840d00385000d0428200380c0d0465800078002c0b68403c005001c2510701c450803034000c140d80f01c402c000c144d10b850087c88040174508187c441507640e90f0b88914410403440040301e000301260380c002e108a03411442c00500a50055105024142d420703810711445030748102e80580c2c081c0603e107000b6202c00c03820200d184003014543c0701800b011001e40300c280500d81e00c4113401007503440030303400c544110440c68000c8803862000c440c060700f02d800500040c09035280ca0910059484041000400c0d03011003238440b10f05040145c001100460316074100f040401e003060002c400103051680128082c0f04c20180013821800c00d0740d5051f5039104a0380c0c0c0c00401c65032682d00041c0342118044260000006008110750703100740c4a20014850140103008241c407520592040b940e180d0b000e814107885 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 816746618 1250 816745368 816745403
    0x3020306070c020f0d050106050f120a12171003060606110606090c04031a0901050f2a190216050f0d0b071b030207052b11040b210106050d 61
    0x11180d4218100d034031461222075104e00766038800094590034050b05c00042c1c924540700030010f00340c5012841a008450407401640c4203507001c110f0381d40858000c0322119000c0400402124014102042c0c3e21904802c08140f0550307035071903000e4a095070310030541040300301c0d26107000303540780140680701ca86598496400202c10b0300301522400c0d008281c00080900703107030300e9581f01c17814400008180000300c02e1039010440e1a000074000c15405c4203854041103074a050402e00381c13180700e1900303217420b80369a20785541030801101c00c5c00300c50716140746040c1400c092100c40e00007901d82a1121170b0400b007000c44940800c2e5480d00c401c01515001c001803150302c070100d0540d5044180500140001f047c0054040c00c668203903095813450522905c603a000d404c040b41401d080003070b00100c00e51030000d5076403180400d240c0d41c0f080d041e605200d1500034010101160152300007a020340002e441c2d503900318000340c07145040025071846114280e911000240041500e88080c056090389245003d0034854407120300001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 816747868 1250 816746618 816746627
    0x3020322050c06040308070b15060706110d0c0c0203120901090612021204031e030501140405100503030d1d0a02100c0602130b120702010b0907181a0a02070f0302030607 74
    0x507441101510682680580050540c0c0c00580c0260303403181c0001051400c129941150550004005081300941526030011501c0c900036144005c00e900c0c3e641025889512101003a94621400601309001880c55644028410351000000700e0203881201e0160540150700416240d1000d81039450080c05443c02c80112041ca52603034003554140da0820607080d1500c00e04002c0e620031400394580310044240103804d03d08081100e2410801c01d4603106c0148000c850a0301c001c07510741012640841d0b140c44040e8030a07011043d90703002c40d60520000840d041c0404144d0800c0e60307000b01d80110048010040c10070503803070f05480440250b20408509003044ac107801f4409040380580a0040103081884590749800d42c110103030005c1c4010040812143c1d810580907186a0b807081c0c00c3d100074080c000c5041c0119801e0310b0050300306818006103050070800b140754140801d0040c42d03041c1d9050400c8e198901c451017660b0103803100300014040c500020840c40c13001000001229070145c02421560f40d03400003250b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 816749118 1250 816747868 816747931
    0xa0c1e150f03020712110f07080703030c1e05061905090d081e040f0c0b070c0312020124050f0d0521160302010e1608070504020d0b090708010e07030203 67
    0x42c1a400c0c400e203804100b09858030f030030a40080d2224200b036011000c030700c4d103000c060f841d00000b0307640044428000a0030200b004812030350300d810108104101072801c20341c2c044403250002108410341d40441d0a0150015886000760720b05604507030306c00c112541c40800d40d10b044172040d0859100340030810a00b4420054207912036000300b80001c1d20a900402c010081030165415144845034034406c1c3c0074032070001b81a900070070440c416107140ca0840e0355410a840d03182c0c030020b0700c00280002425103c50003034002038a80031a2022041c0d0001c0d17841c1100403c0b6109008083c095031581c0f44020309402c0406c00d0580042e042002028800080706190b1002d5115106101d1604001d00c4170303804489000f2554003c040c401c0c0c00100d031104038001d040780b40030a07526800201b2100c1c040200302e0010081100420b680f4103490241e41d9801d108500c0c0050450b0020664004035080304001c0000d622649580c10b0301c80031035040f0708076180c2510803000d82c04251840e00d402c04401601c26501c000c40c01401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 816750368 1250 816749118 816749147
    0xf0e04020d060e0d1e1b2a121109010b031614030106020a0b0a0b0f1203120c0409050703021819050910091119051b0a0c1e15 55
    0x120301041000d4800342080054942200032800045d4112aa68101d410031000003066241070140041007240c18403180e41480c401030402d05014000025048201c00742c1c240d151594048800b0b00c1c2e07912640046441782059058510300f60b681442c0102d8689050a24129462404080e00b1030f1106041028000003108041c0184681e40c02000d0303441c144074000d54000c0415402801e0310503921705000d00688070040400301000d00c2c000c054801079581403000c8100c072001769004282c54500720701d80e61842c0708003040e4440c2c040d601c40030008420254002002030740e40100c1d05004079101c402c0c054099000c3d01600003110741c40c02452882c05d06041034180c4801c164855804e488598400c003191500c0002d490420f540c2118050034404034a0071b002d15807007102010b074842d1400c44031880c0c2030b04495103200e440080200016041040a0515841741c0d001c0a0300750070b51782c001000d4600294040e1491141c00c05030f074500254403070420307180b504120807600100001e805000c16054100d40020098520 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 816751618 1250 816750368 816750371
    0x1404060b0f13080a120305130c12061e0b150f03010b0d180606051509030601091d15190203040f1101050c070e010f0506070305090402160b07090f0f0e04020d06 70
    0x140f119410007030302c01d44034003c10540700d1401a1135030080503140010215900700a10390b00d10000120314849102c01c41e06540c501a84055262400f40007402500c0850b152100240c2c100803a401c18580c0304408030001200c600c00200300d0003811032490301404505440000040c001000950703441c00040045418001c8006004e81c000b4413080042c0c252000b003034800941e184800c0c84607060441003040c0c10031040716440d0403c000000000d69480c014024090b0300c3e0740302d804641001c042d07070204940041199050350301c0111454900500540b017210303134068400d1030440920791405540308070ba005503000b601d030142014540c0c075114000c1c0318400700c19040000170490701440000600001d006003103040c1f5820000d5240000038401400c51b074118906c00d01c010021800044d401004550303e00c5021f032800b60715507a0f414130113480900150f401800040b001402c108a140d0722585540c290348036690f8031134105440d8119603d4505140c09410398555030f010120b07015181201c1101c506a00c04c040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 816752868 1250 816751618 816751657
    0x206040f020d1a010939020705030d05070b0a02030919052d060603010510141504031b270b060708160515131b09060b041404060b0f 58
    0x1039181d00c20101600000040d01c0b180f0042c00244094058514035805a00062000d40312100034842045510310310700584820884041c2c041d00d00a014200080c03030010181c6100310780600300076200da8001642100c8102d405400071b8629440d034403e5074000e07001070004101c414007626441100309851070083c0c58611444441080c0c2a41c1c2c544144022210f81d0001c0421080e2100e04030b21b0101c001d003810b031199051404104003440c40303015a0040b50f901020f8084030704102c0700441d544003804141a4020b40b8002408802c1c80344c00000e002c00b03888840654140c80b036481c2c82a5218548108840c41005060f4102c541100c0c0c1da50000003500900501c05845c000309581d60260b107a005071001c220013880b200140b4244901800460002d0f21001d00c640c4080c50a00003000e03642420f010001c1403a1040214403030070885091030303400600040d50003008031a89a81c1c00c105141c205100d01046059030212940300c07400c0c40d0040d00c08507562809414140300b400200d00032960060800ba101a00d0b8154 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 816754118 1250 816752868 816752873
    0x405060d06051309030216031a10150507140703240f060807050102071d04030c11030d110c03011a0603060d0816030e09041505180609060a0c09060206040f020d 70
    0x3110000103640381c10000748210549401b0b414001040505406440000000c001064102074465107004c2181e00a441c03a6480a041a03035480382078024a1044808039400b01360a42c000004004640c00340c2e00c481c484072490120304e171faa00f105010091000f0300d52040941c260001000105046500000104070200040034500456005502400041d800381c5800c0101d0b50301032042201030f1165504400300b0070100d6540c2e8000070805000241040404140001030000c0d20200726040f40d002002d54552150004009101003000112400140107102001010f440d0502c1003075403284102441c1d10909040904010460b007004182a070003136145401c40300003c0c2110011b0500d944810000542d0010234200103200c034544050490042041a043c480814103144ca14203e0320005440400c2da80d86080020090100c040702002a601c501801e2040c041008180035100c5e0310040810070100c01c5091040310030080d03d200e4607000d03030405004500407401104080400f180090820405a0f01c02da = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 816755368 1250 816754118 816754129
    0x61e0d0803100e0a1b0c0305040e07092d090b03070e040201020c090702250e152803020f040501030c06050705011b0c0507050402040b0a081503150a0506010906050405060d0605 77
    0x4540d48108640d480e40420740170862010070740361504044c81e00400010540e81e0103801d5101e24043c440d44125044000b0303500601c036641c1d8002506100541411804c505154021100003000420406c05184007000c00c200c002e44c071401890f580024001d1182c03038501010b1854054010b0404e80c1107000720000600b10351600400e15001e0b600e0b0754000c00d070790341340da80c0c440040116500140140340380407038080001c114182021b90300000802101000401114001036034080c0e05045803000b035a280050540e860b00d000c403820100c03402a40c52240082c1c00100b00300440c3c400340401800408104018082c0b6032040001d03101e003d00c42c4000046001541c2c80558000079000c540c440090002031000d410800706200342c000400b0f0a55042d0304060800d4554680c50150301004010442044c1c0001d18a540c80501e184400101609440742d042280d400039560074401c0b1000c209450034880410040d500c2180c1e80e00403170380c4a549180c1414100420040d040e80907402d0403105a4642601103a00e0307880 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 816756618 1250 816755368 816755371
    0x12040506091201090305030a0506091003030f0c140c0319080417030903030d05011e0609050d080d0c032a0504030b0c1e090102010e120d021c060b03061e0d0803100e 72
    0x6030700c6e001d03160300c2d040d0280c0d001d560005086600420b52241406086814003214009032a4181407002c800700c480c900c05c0300c545001e40310182c11262219406c008132134001c034504804540c25019980c88010b508140058034843d804010b01081c0c00b0030082105138039510034140c0128600050b04e2900318841e00207132840d040714000c0001a80d4441c010402488007ea8000400b003c00345000c1803a46041d1025080940c03c0c807403a4000c1c044c03443e08804100c0c01c00e04031602072030700b01c1007008407400c2004020700030501c403007441c805403960b0b104040802d16031183d000b000c85050303035a07545028159528505e401c0005800444000010710480d6100110381d074802900400d40e90b12903480700100f4000a0966140e18460322494014031440f000080313081301120f07200c950300100543d4518410840c07401c11084520389072001890540041a120210401180141c0b000c64100003014a12040d01c000e22445440d6070390b2104402c4100400907070b90034099a40520000c0154003c15690305c10740b04070303000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 816757868 1250 816756618 816756623
    0x612090a080c060f07020c01020a030e0f060d061502150601200604030809060a0902240c07270203060306040b040c0b07050a0b0117061f0f090902010906021204050609120109 76
    0x100307000300300c40301000c86504c0354040070300c0c0300401c400c06003800082c1d102c1142c0716000c1d003001a0f42c00042000e49a24405070800c2102410440d503404040741040000c0419000d2800109407a4044030071591001400d03090031030441440c42c1090b12200300541c0c0e20b00c0b41d5140c001e810024110f08a0b131429080c0680c0d41304a0090712850b9807880c000f1055828540c00070950603010b4070b400484009030711800501c13a10180020f001000c1d05021048000c1c0302c2c00b40701e0146202e8841e6840c042203010704c1d00101300b030307160f000c1c0803101e56150000b442c2401e0740022a040c0750146d10200005010459032100c003500503008040d02d0064544a454800c007036030101e44c2c2030b1480d61000c040041080000d80303200b0f006050b11041c510768130f4521003825071100e4002c0c040c5c40c040050700080036210b06070b00344284014207000c144510040d40c1c0c0c08811018040083d42680460010007002070898000f060001910204010881c0380c142418100f00030340e0440107150b13030085441700e82140c80410074412040001d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 816759118 1250 816757868 816757873
    0x509012006101707050906030312090f0c0904031413030204020409140c090105030c07060b0405070f030c02011413060e1603150905060f04060b09010605190306050612090a080c 77
    0x1802484840794000035901100c107003100d000181e5180d110126250045d1081280c0f401810385808000a1070750141c0403034081c80d0140a002e001c0c5000c070006020381210811016184015080d81c01c020b00024122009400f04600d044a0f41c04020300000400e410604030b03040601050f00c0b80c0101d81280c205410802240da66400706c0b0b04a0030742005e01a600403075a20400d032901944000081650001034400700003034902040344010050581c002c00d00b611009441005540740c070380c40c000e211001400e4202702007454a1039491025106024221008641c030302d100d842602c6000484c0004c10342428240c4409654118400c4602001e020038150006502c0418a08600f181400c501d108149094a070301289444007040002d03c01146141e030148261401060070307a603a04200010340110b0700e11580c040910300010800680103c0035041035a0345100e9224401a100400e03400c036841c500642c0d51214091048084101581d050700d9400f1803140140e507400032003581d800080d500038020441e8242c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 816760368 1250 816759118 816759121
    0xd0204180b0403270f050d020a1e0509060f010827060f0405070f0e0f0c041502010903120c0804020409031e0e15071a0c041203020102030405011d030a0509012006 71
    0xc60780b900e12503040c404c0d151303816840324a40005103030582d015120b42c80c01007215403130715404c0d90348180024000742045182c0b05407071900d204c00514540028000d041c4110665000700c0c4035400c00018103903c0030010384604074039880b02c00a11584075464004ac0c60070400001034141c0104042c008140241400810b003110b504051074154180034080c2c110f0112101c400314208a5903840c001020f400000790302e4801c8c4507444811590849200380c0e000703d00a00c940611404030503905600050082e4040d130b0310782c410340c00f62055860030703074210414071f1001501550114003d0318040d848000c0551090410920303826031020104040300081d00c11501045030400c9013191030411000d40d0f40300302095104a440c1c00c40729030354001144061903060402c480070b02c001074002983c400072100903003002503404d82440443d1400a010307500c11141103650b5424510000c0256203580f940440341d0302c5001c061418130810000c02c5560390010000f203030402010301e040000c5010080e0703036059080524405003038203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 816761618 1250 816760368 816760397
    0x80324190e010503010221060303070b01030506060a080115091e0c09031a060604060c033b06090609010503040519060204150e060d09051f0501050108010e060d0204180b0403 76
    0x40c1c0300142c1c4058066401002060104c0001d2203c003502030000c48802d02c13a43d2070b810b0210b8914007607440000d02c19180c410011041c043c0024005101d40000c0320700310405526a4015400e0b42c102100c003e2220750f0380e0505200074482e5801200402000c40b403014000142c0d401031500b524000300c4039a0104001032028000c1c07109103810307689000410341c5940c00381e05240780070841520861140710100081007c03c001054800e401980081c0403101500e04d034003400108201140d4501c003040b95582c9242d0150a402e400d1450a035034803460700030009410914820015982c550008104582c41d009600d602c08081c03194a549415007402160010b0f2181e04103042460301000c0b00c082c00080c011380390940ea405589a10444480c280340d1013000c1000c14041c45c096250040d802c1500c80124480440c5a5840301c0c5940614100c4000340c1e41e102050f681c1d010100c2e1f1207081a96400d4202030702d01c60007800360031301d40c10441c804250300012a00104440e1190095030f034055604500041103c50700151 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 816762868 1250 816761618 816761639
    0x201020d05090a0302060a0309060606020304150e030c0402160606030302010f060e09070611012d050c04121e0f03030b01180e0a050c09030f0d02160308032419 70
    0x10100035420041e01c1c002c490000241c1c001814840288a03010000f600d00d4418401d802c4803084540c00301041c400145c07101c10180d03e9800ca030244140d5a40540b011024582c45050022460000500034140d40901c02c1c0500002c0c0d0b000e81032801c81c441103590144002603207880341800842c000c0d800011551801072942d4140e96a6600031080040d2403014000c220038041a55011656a4100404034072065010306015060302c4001e141d681014500002007a400d041110600310b40905040129607101d0b1281e110790700480c0a041c2d40504000304860010356454020b403442864820050a40051070b80c2e0340002106100c0e04500098071030400344103658220340015004803078403003405241410103142c440c140d40010440941c1c0340e102d0380800d051804503003c1b1100c042015003524010102800c046548000c440f244000510426022a4075545542d44a8007a80e0b0320840f0070307141d41c42c2d4407030940c202845003000f440c0401540b41c0170b49407540c3d6603000040c00c0692070300841c0c540b843e0100692 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 816764118 1250 816762868 816762883
    0x90f0e100302030d21020a1d0102070518010509090d0f0e1309060b0411160609060e060f04050705030604110d060f020408010603030201050903070305042303070e0f25050904180807020102 82
    0x70014011f018100d84030f5000100d107400c0d4416441000b0001e008540100d00e8004c01754000c5070488595810140740b42c4461005905a40382035416444588404500c0c81d50f90f2007030220100001c804281c0c0f480c1e480d00c200c0412080134001402c0c0304070307070342d500141c00202c41040b00e04440c41c6507036a40c2c41c2c03030740e0074140119071220490380c000d03a041074a4041052040342c5000402010290b80f92000d00c00c00000380e10030303080000307000210348032842c1c50307000c15081a8054405a40030300c100340c40024203180016080d445564040d00322000c3c000c180c024841014030072030302120041c0e110300301c83d4119401880500002c1c0324550000c00c000c0e00d03506019003100e001502c1e4180e142c0041141d9000b0030382117012a0100d90000428110030002c80100b4005440301d0303100c803035040c016582d0001d450a6491486030081300e58481004460f1070707086c81482600800e14103a0913142400c024244c695001e280074003201400500013040c1c0c0e84880e000c500030140e4542084482c80008207a05056590410514 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 816765368 1250 816764118 816764177
    0x18020301150216170f0a0f03080906070e12011404060f0b06040b040b0c031e280801062015010f05060315060a050c0303090d0807090f0e100302030d 65
    0x504510030340054001000c0e9440c0180307210000360007406406440108504080c060819041e14200a01d0f8504010440034810081e000181c1d210f01040182c00003180c0f03240a08081c1d140c1203260043700b002e1181d5542440c403080440e5503240d107a40c2c16158968041c1d0700c11481102c0000d20400358030044404c403511540b09900a0342c0520061241c10050b600b02d9003501c01031582580c40e41c1d40c0e03217200351071031003004116000c054003984004c03038003062034024007402072903047c18454491040412403c202110701c0c107600001c100c500100602406605078666801c0301d030105440e0000d520941920b03100c03039032031101c41006c0719400402c910081ca1341c120006d8202280c0711443c50038003009500c048a42580840c0c403503203000411380c41203801502241c00e50242142079a440345041e10042c1c0d280c13000a2070241c00305016a0001d16480e10074005141660011124108400d08205a81a03003900084c07040400040300b41d004005039404020008030f01c0c12581d00c10011000500c045150150814902e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 816766618 1250 816765368 816765373
    0x708040b0c0f0409020d02272d010305060319050a0c050108070203040306240311102105060d05160f1a091018060c050f0601060c0f0c180203011502 65
    0x4440c40c2e41400700d408842d0391310f80150301c0f01900d0f40e0344002442480c41076108582000703030b503180c2c6e0001c89842e180e4900044130302c1c05808220f09400e20794004100a808103032486005901820f40c003c0c0d02c880d40080000c0c0c04c581801e80002c03554520b0006a0b4820b40307850f8050000c040c02c1010445010f03014000070300e0105410708250001079607d01440c04004c04080e00c84a01e048010080c1020044c0c6030305c3c4036604105503a0f01d04168148405400c07100e4002d4074034003600d8045600030008808130b40030008100046011120040c40100005082264003908402c1030074041541042a140c580f501d0700c01056840c1d140c403101004c00a9103078043c20592070312143d03201d0b40004c450241c5110b040c05890000c44811003640032503085810860140e0210718000000c03405a0f80056407207a818031030f1040344c40078640300d4042d40d070f44d100900c9080c00180c404603030440000c208425401c0c1c2a882000380410030b03600d55650a9540340e09440007900181d012004002c145d0100a43e0f0301c0080c0107002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 816767868 1250 816766618 816766627
    0x18031606050304170a0c0213090816110d081b06060a0605090423060102071202031b01120501080606012c100e04140402010806090112020118030b0708040b0c 69
    0x25042540965403080c401030220120008003808021035018403c00b00090000d0b40d19050218003415402c80d5200c00c1e802620070414040c110311880c810000700e19082010a41000c1c400241b00300a50300f2000210b400d21a024040748041d210080310212541c40303152904d89460341d08034484643c0100a0041c800d0b0342c048414080d0984a400d182000c0c0e900524003540d4840b54080400d02a1041c100c0c14468a100110550034260b008135030140204000d909452803c1c0d0b4810640c4221001402c0280d4550000440440840712110000e9440c2c841810541c0c071618071100c2110840c0c4090f0700201e0640c100d2001c0181669104c00100c540044816807018011150310041c110b05054070349642c06050010359210016000351040700a00200410502080140740c2c0b941031050410788003240440c45210120b04c0c2c0d49402002c0380c2c16201e00c160752030145603c5030011181e00044c44100e5507001c90140c004800f0584903403080b0b10a026648480c41e881c2020b00d010a610080240b80240e5880c040c003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 816769118 1250 816767868 816767893
    0x60b041104060c0807170703031505190e0709051503010503010c050f030a05100b0d0b24030a0c0504031403070b150a050d080c1c030e030301051c0c0801050a021803 72
    0x764008105130044811070310380200345800302d1917901e040404550048045a034400301030381504540c920500701c00728003400760b03030312402e10107849903005203c8041074a1000a11400c0800c00c0d030146c1c4240d891812001e5903540d0700100768000305140907050b40782c100100502c0310b814240140b041d03055640c03800c3c03460100c2d030b100c02e07042c140000b62910340140c1e120380204103c00c003030000740c00103030180115180c0c1c1c509040d80d090000b00a00c6003050300441e0181c0381000d101480130324000e040c106c0102510f1942e6100d01020000340050000d00040c44030611002c404640c01039480c41014101c3c40c0215640c1c043d07800c3c002c0300000c00030105003002a40c02c0e61085251500c0c1c10340c0c030031a9000d5409640e044810304c0d0110017401141034090030b5220300c03840d2000d02e070010359a0000144558a040100c1406001c3c41901d0b48001d00489420600054007489030440101040035503a01034154103903d00e072580d664a0a5400c10350780142c00e40d40102e4060400407284400c075000c00002c90040c4035003c80d81 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 816770368 1250 816769118 816769127
    0x31b0c15100f0918050f010204031b050a0e0a090c0b030105040f0b03030901231809070906050a08091e0619090b010e06030f010504051c021b1912060b04110406 70
    0x81c06030941044e2203005141d0240601007484810395800010f4400d040c1e060f9040303500075002440162a881c180d0b5403414181e15071400c031300301920340c094000c410890030f191f440d4105c8480940741502c0d40307648114030320200742d260480c00041c2012074403a581d0395150008001c01d0f56003003403518036110301d131001050b00341e0340020495038101c00030300300052480d2040092285010764040401808500021b02034541110602c1d0151030040895640c441e40e25081401c9403078600354041c00c3c01041040000d580b440f80504403440c1d001101400702d4940c11030040000403481214220030b5020741c0100144605032610700c035116085048032008101c54541600c40c0c0c58076070018401d400d03140c441240440c415071814051102c1c203100d035000a1101d424075207403007035035104544a09508910724a45d012a02440810f450903041c03c1c0e5015030b482c074424201000381460040c103600c47c1007401e03020005103130302c0340c0411401014011500000c1c107500200501c416901d069130720303000d024402c010038071945410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 816771618 1250 816770368 816770399
    0x180319030b010228030306080d051215030d170106020f121b1b01021c1e030f0f0b0406080312040303090611040311011220031b0c1510 59
    0x21840d02250500c05103006030b082c40c40c0c0300c00d00d1600140041c00590401c0b400d8094200040c0b017543d0800a056039001c0c5141c82d455101d00840004504014418481a00d180410303005402c504100c4180991000020300c1c10750780d442c0c900007040442b000d82e4002803007124641d006164a00281038040c5c00c0540d03194480c4522205804400004102d195040c1c40c3c040d11041d8000e001e904885a17001d02c0c4408180c070480f003125041c0103104800300b11400500d981c0718102080c2d400d07210724012054540711a20180c140300a50010142c4d641894036201149009015044890740000600300c04190180400ea030300315008200c40703905c204188802d6994005000c0c2e4001c0e00f600c3d0000711403840349031072006001c9849070081c1134007000c100801802a1513a5200205100341c03500720410707a5107021141a1080a00c8040c0320808070a040450106014011356122100484207410601481c010412039040000449440d501ca2008500100508800541c00c10102c113881c09071580f810306084004205c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 816772868 1250 816771618 816771667
    0xc090608010b041e05041107050106050a050d06050601140d0e0c121e0109060501181401050603150f0a0f0f09020909040206070305071703100b0313140f0d02061803 72
    0x900079658070789044404d14a0b0140c000200180001048080700f040260009681612994640b240009080c6000400c55040f1207020f005140b400e0310380d480ba04000c00004011606200e2031500a0400c3c050030f5009040030007049000040035a5a0105245000e10304404a4080c41c5201241d55002c00b00048800f0f0880b80040c600b0000303a040f40d4041c3c09010300c1007008007082e00340f1002103900c40d92020b540e0420741c0452020001d03044110744080c0114402e11035503030840740420100c2c1c1c1c4650851000081d4030400f50100b04c842000d000840c02e902400d51210040c24000401804190720452a5100901c2c031403100303600742141000015a01c01014000901c40c0c100050f04800701130041d82680d540d19044080550044040d03020704030a130b0700851358907404040000d00400d40f02e15000030749020380d16400f518041c0c5981552005100d281c0607034101514800c0c021002d0440030100802602002c0650140559080611000383d84043e44008200700b03030824424074003414000e000c581c83c10719 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 816774118 1250 816772868 816772889
    0x8031b01020f190207030f0b0a0e0102070f080306180c04080105090f1b13140106021908220806090c030c01030b0f040c09050406091b080408030f06010509060c010c090608010b04 78
    0x31003d840a074540004d81d807000b032000310003090742c00610503422039092203481c80c1802803244a15a81102d0700703d11400b41c1c010314001002c000e0002113110007000e10790101011382141415541c2440204d40c400c021078683c903070b12a0008050003800028041c3c582c0102402d4010084e125401202d90348924802d000240a41a41c4c444011580d4590000e0910700ca48036404110700c030b10004080d0708541c1d0074000c2c200940304540c600c4043c0c0b0340c40086141e02d90380140c145814031180c500c07100300449284003041940c1c503a213400800c40311001d01082e8018028140180040e05405051600b8030341135035091414945441d540850036200d2100490740800c00300c07000900726800140c1036800001640080c1e400500e01000400d1500082d4001c500303081d88050301c000c00340c503042800c6440107030450700107005150500200e07000c00214100d50742c02c644141013441c1061555800700711141c02070001d00710b941c0c1d15041c10040b030782d400506440145c5503a00d08420b42c1d6040c9001e04482e442148104a40e95 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 816775368 1250 816774118 816774157
    0x12081204021507030e01021608100b0604030602040803040e31030c21031b0e01120209090a05011401030614060c010e030d021e0a020c040c0e0a08031b01020f 69
    0x1541c440b840310460842882d00c882d200c0286050007041400001107180c094800c1c41d80f40d0301104945c03100401142d14850040109048602859010b00b04011201d60003020600005c00000c01d10300240002d000074400554603240340c00d0351407100d440d0291581c101c282138584002030901e5a080c10300e071f20950704002d5810715580fa140072a031114551601520171422401c411040f0590064441000031031987d0a1001d40100c003407910288004a001801003041481d118145500030b00d40d4181d06c4003203030001403d0509003030106d00390b00401c41e440342280b41e03104010300a00b8100445135204060a1908200e61424002c1301240c4003540a1002d20585007c6070407507424100b504120801e00640d0242d03911601c42e10369010294124140e25811420700e003c2c0c04504103000700540d07180c035016500600d0080641402d100c020490002c0141c01c00c120020817010030744400c0c100c1d0008060080096507203024034525044030011803039000405034010403119044c0034080f41517a610b100c0300c20404212 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 816776618 1250 816775368 816775373
    0x30e0a0816020d0503031e01081e072d0e04150b04090503040b0c0d1707050a0e060a0906030c0c15150503060406020406080c07120e010201150806090712081204 70
    0x1050746520029442a5400400020090301102550241e02c01100c40280e03c01007049649841c04240250300145d40030319824904551480103010700010420305170740d82151a001d5818000a81e1f0000c00081c0138002507490401881082d40c0b0010600805001c44900301680c44440d2a141c1c00c42c9030314544e07204d0300c00c0c0d6256a0f0f16400100ca5682c024101d07952203a80e00140840c0e900b016030004060b0142a00401c503190040307401d4a10740318500707025451a038800c04280c8242d04030601c1e030010003560321560309883d01c448004000022081e12850503107031818900138280d507500348070603007040100e00b81200000c3c0785400c5040710540d442404500a46c010320000311085840e031050360701d032161601740000d001d01c56005005460040e5103240d095039810000007614403482100801030070300c80c0d20300741c6114406e42704035001040506c00850480c501e42036904100c0340d19000098550404d505000500204205100007005c000107117030712030b8059448440d1140160400510031461500c000313000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 816777868 1250 816776618 816776647
    0x23060a0b030f030a0314100b0703180f120203010507031b0c050a0507180b010e0609120c12010c110f0c010f09030c090207051b0a050409021201020304050309030d030e0a08 75
    0x603082d0300e6104032a00c810103440c0043c090101d464248a80e0900d00000c40d060b164001102ca05881c0409030042c50400c10399800c440060304404803586050032000c01040880718207110382e00501c801802100001c41c140105070840d00d014107480203042c42e1448044003034550001007100d0b18118184010b90b94994103041d401c0c01103101d0014820b0145050100342522040100b00400081d1a0100500c05018005491a0010010099204005020401035460143c00c450300355824001a01c0c0740e00511004201d2058061004404607510342c000000c41a81c0a40c0c4407880c14078a100400345007501092184d2500c0074401c0542c10811148040284140119881701c01194090050b4110b80d03520b0030380c0d40c025009040700b210300d03015401c114188040c0f0303000000c4000380020706084589150204210080414410403600140010068241c00c0c0082c405940b00b40c0c0110040d47d42d5070740e2003080600380055070301ca00c01454500101040540b4002400344000395020920554840e40394240d01c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 816779118 1250 816777868 816777883
    0x302071b03030207060c05030d0509010b03010504032c060307030e120a03020a1139120a0203060106050f0a0818011503060f062106020c1923060a0b03 66
    0x28010340101800290900202501000701c0303000c1e509542c1d80e5911041d0441d80c510710048050320301d900078807541d0020602c980c00550410b0b0510000507180c80d03d24082425500d04403010780120b01c6400301081d10b8072250070346140c0d00403210440541c0150900001e40c95000180c800301c01c140d82d4100b4043c4d092400c002a09082203000748058441c6107031540100694132001c544030001341e1100b006e030103030b9100040d040500345c601401141d03014050241001c8148001e90803c101c441c030300e03c2403c1143c41d40706841c288080b50384040e2032600d006005145c07a204040c0d00905c00c01404000c0010031141110959002e10b1041c64500816104c950700c00360414220040341c540b651038654000054002e81b5090011a481400140b0080c0103004210046448a1117014161680c60011039540c00ca8420081c001d94030800005050040000405140804c9a5600c0c2030f6104041a90014041803040f0341e0316009011481d0900c14520340d40d0152140340140c01d818100351104e0684005ea40d05120f5203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 816780368 1250 816779118 816779123
    0xb1021031106010b130608010503100c020321090105070504060c03050304030c0c151101020405060d0510091e142e0e1f090c0f051c15030308090106030c06050a030207 73
    0xa8845513119003074043d09900041d104441e0a4440c00e000603214010742040f41203a400130007414034141e4001e4420058a104882e11046000411242c00300780f00590351000103445040c150181ea107410368242d4215140600800e050040c10b00080003c182d1209001000c0d55042c501030b516610b8900c3d060f1080c01d4015001030001103604008110350344000c80c41a080e401c01d580707265809281d00022800c038440d80c062070340c111204000394540300040350000e50b0080802744404402c990369078945000c455600c03801a41c0da0300c0c407500340042c081c02402802880c84c8250314595160800003a141e07844450b4207c146041202005854051800c0710300d50700c0104000c4c07844617024a804011103078860040440ea5004521000012030104c5240c400c4035a004503170744451282d41c0c908001990250414080c1d110340c8001c0300300c030040c1c5c02824042c50340340ca201004001c00150440c58054034014005221540c20f03890b01e0710400100d0300d010008803c17600d180c10075175030350794581100324045c0c031414102 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 816781618 1250 816780368 816780373
    0x270b060f07060f0f05090d080f060111030c06010b120108060106050d0c030b220c02060906072a06051506070c03060e030904060e0610021c03151701090b10210311 71
    0x1305520f041070354000c2d52191040105682e4210036a0350306460820040e41c0010b0241044000a0307a03075405003070007104109281b1308aa06103039154601518080c0260000c515101d8046a0407007040800481a405454500081c000341d41c10440001d0042c090502180c20103038031142c00e074000c0c40c0207611981405801a1446580c0079049004030b80d4a45003121403000c251400302c0c100304040c03020034810302801c540e0000c5c0c211a241d08400b151684003076080d00d03899080342442c0c0010a140505440c01441c40341c00c0205991800030016020302a1420415000307042c2002407000044940304d051040d40e601000002d564500304100f1031a40c000e40c2c00c01508035107030605c0803d250340600303601d5102d0034044030545c0000402820403a280c03c01e54000d0110301d0300504109064a0294210384d500151500c24500d40c0e1350381d54030038034444000590b94129a55075407a02c00034003205061807039100d04025004161185000789090309000ca2409800640504032403843c101440340c00240b1040861404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 816782868 1250 816781618 816781631
    0x302041d100503011811030115080d080606030402030a0201110c1c050601090b090a0c0203120a0f0b030c0d03050318150712090b0609130804270b060f07060f 69
    0x15081840032058030a000e440c0300c0305500080030300e01401510414205081e20b440c25098503a200d5003400d9071000030700e6155480b50086403151403c0c00e0444024030003480200401c41d06180702612a2802802d050f00601003041000050385002610011403503081c60302180d000d2040c0011030030480131041e0550720008001800381c4405030300300101c280c24041c43c20380e12140d0b81d843c09102112030580105800c040040005030350f84070740740d003ca000700e4000d0040d20305e42060003452a210380002c980c40c0c1021a03691400034040e80c0a4070800030504010340090803404a01e0340000c004070b412400003810001d000000544140c00b441d40c84002400314002c44482420b5803840c55219042110803038006000e490402400500501443d1400d5411500313800c16619504240459404d0007000070f052569420500b40c0011078004c0140b00425020030f1990381214101070411409a62101d88030490f410842c00807080da035400c040b034510040c400b240c0c564a22142c034001018007480150719001624001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 816784118 1250 816782868 816782909
    0x230a0e010c02250e04120302070206280c080d0e0c0301020c03091e090402010f110d031a0d05030306240301030308010512061504020a050714070e090d02030d0903030204 74
    0xa500704000d83d00300b5010022244441c51a0900310a446102034039488400864003090741003404e112103056a20300036180ca0b03101d4001c030b4a194441140740c402e50030001282030303501c2122070401204183d240b8160110f80090b03140c850b074a015841950342015540d00403001c64270300170400d02d106480c0150095417296a003800840c2c80c0e4000d00b80c0c45005d681040800581d0076001c0d040c990304001d0080104545460f036800440761108406d91050502c443e441801c1c03107032007003084540d071090300c02c4d900802e44460066003a8244001084404d028591007111302c40054008170540b50300c4841074800074001c0b00801300c445007076aa010321010f40f0700300c004000300038154400104c9068a10903218071b8031700320048540d180c1c0c5250861b4208203003000320055a8241c5000d40050008000b586442030130f00500b03440d211030741740d80803601a11341d47c4042400c103c4091214803580e445203055000e00759004204c18065124800d100c40c0110081d40c8a034032908150013607055030050900f0f80509070952245a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 816785368 1250 816784118 816784123
    0x4090c1706070801080a110a0909120e030c1305040f140708060c040b0d0b040e15040203012f0903390609010909090206210406050703230a0e010c02 65
    0x1400e094864000d4100145503140120b411a0499280200501101c1041e031101c0300c1540c11001030560000040e500002d0850413800380d44000c5010703e254881c111501c0c600680004021041c660007604403c0c030310942982d40d03200407403024002c50b101044c55629031a0800c1070080050004001210480e42c644511400117114415201c50340c0440320f054455010410240c0640c1c4140d0000c6c40041200b1408101c150304401002c0b00b01420100c0c01e60a08501141421008031000341aa22031604000035442e09000e10039034000d508171002d0b4074100e07a01c1c0c1080141004502103960020001d1910300c01d450400402ca000c0c2c0d4800f18070035102170358001225000501007441600d00c0391101c140f0007203150a504645000c801611100381907494288400060035514000340c1c1e1091050254a034400e1880190a081c81801b208064280c40d1615006048900203801d03101018070303001004c10740744200c20b246800d4041018400c2c4560343c13034400200190003685503c0090394204a820a002d9400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 816786618 1250 816785368 816785399
    0x5191d093304110403050c0a05060a030b030129011403101512060906030b0619060c080702030f06010e0c07020a06140c0f070f14130b01052104020a06021902060904090c 74
    0x82c01541c1003210040c003044051001405128ac1c40003042003005c085a019621499a5a802900101f0400f1a64104480d0001d01c0062450141c00c501c40c88449581e104000486c000c1c4000c042500794106183c500b28500e9440c0100c50800e0090040942918050726403200c1c040d0706594144000c940f61603080c4003501c1c4903c030807200015801d01107400fa00d4005041000c02c601c3c03c030040b12181c60800100c45130f80d21060161543d0008000010160320144146054100420000e004a5140070800740a6040040c03030b0114611080c0240300060760ba542d4074804450441c5070007011100781c4050ba03001889600c0c0980901c0c45a0854840520f20100740c040440c1c2d084601101801da490211003507088808200560004c110703c007101103120715610014000c0e1043c9810350034050b48006100d020401920161078141040080004520301510701030003034805407016008080b490030410b26000404e03000203110b035102107030901464849900c05e10000380c02600303030300703205503901c100d80c084904 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 816787868 1250 816786618 816786623
    0xb0408070605100e150d030e06070b041b24030b0a08030c06090606010f0804020904061506020102041a0c03030f0604150306020304120c17070305191d093304110403 72
    0x26a00020030807000300176461002440502813244000283d58200e901003881e800d1b29621640c180114000310388102840c070b1007103101d4110a0550320750072000503c3c10040740e200c5081740d0301d901d012780000342d550180e2003c2c5400754180403170a1039040001071104100d40d0404220b600c000b1810450561000407203a000e2201c0b03800b13440c1c0380e4641c1f1004440e40c880b0310040f840821540d1002c1001810070024840d0f1160040100041140e0369564040700c0c3d441d10303849400140c0d00031406111000c45d011080300c1c100c3c0b08240031441d000c0c1d50501c2a40b2408020060490580700350001000d1b501c0d140c01c404242c00d0032015141e40c0c0c42c1c032031034560000e400640f4159130000d01c203980d04207014012032403070000a8110035030303010030714018110f42c1547d03021b460120108201407100080000601d440b10000c0038003078403a01440130803054000402464440f510b4400e4603141c0c24070080c10380032850101f502c040c400d030f43d9200b81540c0b014005507034901098913130001c2c80c02904407400004c0c40d01801c15a0f1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 816789118 1250 816787868 816787889
    0xa0225061a0607080904020d0203071106011e120203070503061009110414211608010f110a03021303120c02030d020d1e02160303020d1b0f0b040807060510 68
    0x180408500c0310320229001c010340c1114040180d2030204492030f000d000c3d0908001e0000d490201c2e241c0c0044242d03041270350300d400802d1002c07000c030364020b000f48082070240115101400c0307500f260200c0790a0f446060300ca00d8080c0303c44458054103544061042a0140002070210b0300b2600f80780a10544400161203081c490b28a0034403c0190000b80c50f084500322a03510354001d0303850503c0c404104a181c1d00030308a0b504005c03480b01190b200d8405101030901c44c045045811a1b591502d400ea600b90362040b02107802c0b45240c0307214070f101b507100b080613a402c508443c41c0060f143c1d212030103c0148801e0a03000a41840f15550000c40401e61260601002510943c00e41d8140c0c0f401901c2a81d66405038a80341c40030031815102003503e102c403068100410740d0144102c45046103140f45988103843c1c41c0d0011740050300080243e10040c0e0700140340d604242d00311f9008070502c29640e25107070a1100e419000405038910400800d00340407841090310300054110004001c5414149100b85141d42c89218048a10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 816790368 1250 816789118 816789131
    0x50406050a05061e070f030905010f08090d05030903070506090304090b0613090f1b0810060207060c021905100210060603050408070f210302071b0506040e0a022506 72
    0x7814060305600c2214409058541000e011000800e54001c1307000d14004410414485c004c003051540684003500e500035103d000000e03041600050103030100e00c40c6541400034200510048500004112802001c1d2340340c46612501c80405a60940c42208070140140c8107a0b000d01000e9000800100201c6048480401c0345000c1402401024020103800b40f42d000003003141009000707074940224584a442c0000090450404100018402d441100d2000000d03c403070304100c0c10b514180410340c00380000340004c0042910b0404020100301785407500a000b00f640c1c614403140008113900b12005232100411001c0b1003d61380500030b42e255103000e68140078a040100c0001c01500034803601d4042c41d000070a07030f8035107010f47c1c603030403015040150111030781440040681c2c5465496034500151081643d400750390f401c02400c20041c10003007200e1140140c0b0a92104100301e95902c41110b00704e80f45403900580c2d5503070f40f095080007400b9811800c5461903116030b06c14002070119416a29180c03080c02d08001d02c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 816791618 1250 816790368 816790379
    0x111803100e1e01050405030a12020904050f07110c06071b0306090302031c060b0a0513030204020318060a0b01020d0c03030b10030c0f0c0804210602160b010b1201030f020d06090c050406 81
    0xe885085e81c01034600d4004100104140d4851000c0c0075503500040000342c9062030400c041021aa001c80e506808035080d2000d000c034069100e941c140c01c001c0410028959542074900003002442401801010721030424001a034402080641c1001160030072420404205075080103522a48416204000d019404540e444003135814030510007611416000e560a010b42c42c2016502c0b6802200076040d03150074180c0020050341e990000b540f00312410a010007241c600d101c1964504240900031302000380c01c1a01c5500030b07176170004140840074903925281d10504910b09050300200460130308a500f0400c000202030280f501504807183e111401d5560f03100e82d0300042c80c100c07007804004200420904040104101c61b80c85c450741480303600c820080c9242d00034860b60350740702242d01410705d41d01e01d9184180e5200a02c00750201c01401400c282c00c00314542111a0992905a070050200a11041454822400f036450300846254110740c00b40c0c0c1041141214200018890014400e50b40300e40c1c00c0c504042217 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 816792868 1250 816791618 816791621
    0x409140109121b030e03030c060711010605061e031e040f0c12030903081c0504120306050901180906090f060e0705180c090301180c060210111803100e1e01 68
    0x203d041d102d001440709050f56a040300d20301101201294135100c00d020060358101c1c00d2104c603001d02c0c9030317031039004c600b01680390164207480c1070350300c0039101d100300b844010209000720500780004580030b80728960725500d144d89c035a0b1b44407000f45207014480c0c800c1d003000100500b40641c10125030040074a5500a42e44d05484c102e801034074200200080c000340000c1000448440180a0107001c10007800c80304034404201c00104e440844003034442454583c60b0001c00d582521801000d4030b801d40315004550705085d800007000f1240460804c010f90754178000411301c07940d80c0c03002c1c00b080d505c50101d40000c2d042d806e116004c0e1420103507442240c0510034000a41d458205010820547c0880410b08035603140c0101d464160030109886c2c1c0c040d52103030030858209180c050410552441981040051418024004d01c0d12504140c1040220710b4000703501c2c00c3c25046002e50b0900303503195191904421380003001c00d04003102c031081d04001d01d0401c01307420000000400c3c03041c000100e82904030b10161410f15000d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 816794118 1250 816792868 816792887
    0x150904110405040303022203120203130b0a0509090f04230c0402030901200d05010501030621060f0609020711061315091508060f0f0a05010e040914010912 68
    0x10a250042a450344850030941c1056030300500a082c01814607400805030400c1050f09200031210024030030003441013051400c1603c403c00d14a10085040c01c04208a203011000c2034002d141c0e500341c0125403a518280f16004880c1070b200e0240110045013840d840c5c2c00710005040d80c0490741c0b03c2510041c030b071a2150286d440350711201d801c1c0003420002412401d010095002503c50b00455480c2e15a40d01d00c200e0327404405011070188c5107940d58440051006a04840701030704050304250034140204582c5c0c03103c900c0310072418100e04003844102c0840c5804001808104d5816060324180080000c01c03000c1030707001e000214010f64040d2036102a88041050500c0f5491013680d03024104441802080000280184002c6031402c1c4044201d807661031481020a0328040ba100081004003006842e0900c255009100c903010780e96000e440403404000b4000030f07114010141003003007035406c0217401c1d030b2241c05c541202278000403404081c4041e183c03100c1c0030b05110070081e9039000301c3c0040460101d00c82c0b09500f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 816795368 1250 816794118 816794123
    0x90218130c1202071a0411091b040306020d140910110424020a061b1e0c0b0709050a23010804050a03081509090c030d0203040608130302011503060203150904 69
    0x401c1401840d001c2c040250440c0b2016108003918080410400b1408500340380110700403800348410550180411803241300c010300b071200458001315092810f182d10780549040c0c1c4d40c049405a12401038a1422008040c6c160010790040410010700070b5010002c1030741d03e0480e2421a042c000d400c49610051214801e0748100c40da000e4030320301149902149481c442c4192181d604c182c0704008000d45680d400d441402d20480149031400c00291546500005000b10152000f0009064818914000f80c04949a50005000f506e8100001001680b0031700c03001c1c000d00f034020300c0c0c0c00d0060384401700c1031640311855020108450190988010319070141081900c51503014009040d0640c50359011074449030042d2403600820418000c83d00c0580d112200d00b4440c81c11340006000304850b02082500c2d0807900c001c54825908204800c6c0a03803544221420340c0041800c0201116144a260890040c545011030070b004220b14134009c0b00700580d640044d8018202a1512620200b45078102321030790318140c500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 816796618 1250 816795368 816795377
    0x9090b06040312090302060703110d03110d05040203011506170901020309100b0103090807120f030203090d081e04080c0105013002010e0a12061112010618090218130c 73
    0x4100048003c9000c11032440c0618010401960703d5001c9000340e0851582140410140c07640c010072030f1400c12500300c0890440c502444078001910784c200b500c1c882d0303021110b0966220400181552000d400005652a4610314110100da4032000103100c10300301d000418510054202064400505009490044101e10042c1c03080140b0030044500414524000728181134540e101007001c6107130742000d000424014112282c41d21840140104140c1000082c0c905240c814002e1200ba8040046d00d40f0020b03110f4100349200b42c030b9424000083c80b14403582540b9551441c0108410003103040701400d034143d0418020702c05a62512800d2000c3c45c50744e00ea985282c1d00f04009c070040100007180805442d4018180b25101c00700d6038010070f1400c0520782150101400c040f00200401021b07219000754141000e01160602545c002c2001c40700106224000820003d05000e207821035101309000018400c1e14003c41d80e031001c0b401c00608140b00c0f00307002d07031150980c10010302c80031000d0f00416404403a9682c6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 816797868 1250 816796618 816796627
    0x50706050a0b091501170f1303030f020318010b010f0806060703050d05100518040b0c03150a0f05030c010504181e0f060302090c07170f090901260a050604170903011b09090b06 77
    0x140007604514023a004d50400d40c03071b40141c078441c1d40c6a100641c029500e0680400043d64000112170954200148042c1005001d903040e24000d684094140d4008100302da070300381c0c0c800e41424220340e28001d10010303150701c1d0303e400140044090003c040e00c1c2211029581c0140c0100c00d10041500a501214040d00031226000021581c040010040d035011074102160015070700040c0c00710b440c07459143c103d0203140e01007500500107880c040200c1034214000740781c014a05400d01c003000c1101581c0000e0000703860340300c07070341050003080c01c68400d40317000c41d0700401b040104a001d00170b80103040750348411380c02180050b0108420070380b150b00b219181e64108a6105440300b04c200340030342e00d602510b0612100c3d502032101c80d0b00c660346e584111f4002c1c00e50b000c4c500d070001c040782030002c03200350380c5c5107810450b6000c3c503840741c00104040f07140d5520a41083c141076040f00309080414180c03080c030903201d502d5481c0c12040c01140000c5400c001c0c0c8205950703a4515100e0b181e91002d82115481c159860b070001c000d01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 816799118 1250 816797868 816797881
    0x3060c04030f0b07110307140708071a0f0405121b090609130809041505100302040e071202041a270a031509050313090f020307050706050a0b091501170f 67
    0xb424a8000c4c0840c03a004040704000c00005045400c1541c04880c1c8600b80b101c0c030b2415900401900c009400c400e4007034040249440030344080805905143e00b444040418403092468050060390010f00010348031018a8201800c81d5440e04041030420801a050840c01c18175814a00c0d840c0d88a0741010b81000203d407120042880f64520748203084506d407000b0018000c80d42c40b580074080d1100c040322003200100d0301344800c205640c13a00c044101d04052043c401085044078007400c8503041070540c1010f02401a0444079400a889203400a4015050868840403030030b8250000340360300030b101001c406884d40349010307002c0245141d100d9194400104c003410301c040382802d41815001030b00301c0000164030340b540d55501d040d43c20042e0400e001034028181004100c00501503489081c00b103150461461401c43c030007800d203010316080907040555900000e190405681e026034050040240300d072791249007034090020990702c074a2a82c0d000926070304045d21381740301c2002d150b8010541c020b540c400b180d4541 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 816800368 1250 816799118 816799133
    0x2040504020a0801110a0e27070207081c02060f061f030221010f06110303010e0711060c0a0e0301090503070807051e0c100203030f070f030e100b03060c04030f 70
    0x40e1099900003408200021441c1091050b400d64002c443c4000b6211020301c0d6014194084400050713000d02c650030801e800c84003014071904a910f480006403162602e60303410407440e041540d0401505d51003004001c0c0306011190301d0748448a132059089901c2d07652507800d6080032030310583c1c6094002c02c035030303081510800b05803906070010403043c540142040f541c07842c1c6641400000c12504050448140144080d02800380c64601420680c1031240703003103800327a0f403559891005100f03a0500b0303c410004659164410f070038180d0a841e03258110b039410b04040300300c004654060042000450400e01075501981010700030100101d803c40055428404240c4825640d0f91080c4021101c5020f202c0c1303034020407040b00d07820040b400d000318010001038140390140040c00d081401c074031095500500c02c0100000182c0300c500d030702144919049414400c080d00660140640d411032039064011003960b0000551998000c54944804404984c01c64440400c0c04c40b05205038040585175820a02651000c913008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 816801618 1250 816800368 816800371
    0x606031b1110060e0109050f04050613150903020606100c08090f0d080a080108010b040209030c0d06020f0c03031b07050a0b091f09030e030c1012060801020f0c060a1107020405 77
    0x320416500d001d0340c8880448215802c070303000103003a0104c0300d0050201e03010b01d100301030340f007207501a54174010305060300c4142d5201030003090348aa800f0721000307440c104403080c401c1e085010100c04042c400140c0f03a160103904c0e0300c0100c40560082403458034043c150351103403034906040e942240d12149090b00351401d010000c1e2074000b507150019090150003002071361500003081603003841e40e213090055041c1120a402e40b1000c007622846540103018030030090f5070126410a0180080310800d2a05000303240c003001a003d024188002c20300e000c00c000d84105d0010004ad442802c0d840c8464204c601c000751054440c3c001c404001d051a13006119000015101041c0c4076085840c24003120303c18035855900d0039004042c4507400ca02c882d00c5024074410190400e16100b12540101c01412910009502041d641c864405480b800c000c09500a202c044245522150207484010002e641e02c14003c072623070910f58400680c5202502c41c03480040da03110303543e105a01740c480008004070f2400701e080d000c0201401c5d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 816802868 1250 816801618 816801647
    0x1220010e130b060705190506280216050d0e12030408070e0c160c170705060a0e0f0a06091e050109181b0806031005040b04120c05060a0f0606031b 64
    0x40402840011800400c84081c1c4980300d07506d0742c480740d08075140c280d0070001c015020301030315080c04c5101d8400d800845100c451080c40140b0042c0c403510012020b42c1c0200c041c02000c2e065010341081c1814155000d0b410803204ac1050703d08900c01e12201200594a00c228440d4400c2d0fa080fa00701441501d40120031a50006e4200301c405080c0080d080100740d411254040c102d5111031140e031b041003003460100901c40490108400350010525140200d106440340071607070740800914660f03480e450750781e060000103010700c05013169410a44529018044884038026452100c03500c0c600c04540162021105090303e2060b51003d20360b518100761811110b041c3c00f000540140c4607140c5035200840e4803c07400a9413a103940b000d0103420480141410000d000800e8030241e41800300f0000030558802040d0f400c41d0340804010500c0001790022100510300e160014902d0180c02c05100703101c4030940040d00f100c3d502c04030411105c0e42da000281e0449842c101e00e2248901c0c141100d1109a002d550b80d41d40c81070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 816804118 1250 816802868 816802879
    0x40e0307152d0203010e06010c030e1909110406110a0507031112030d0c09140a1701110c010c1b12030903032408011404020604030b0c041220010e130b 66
    0x142140319620070425038604040c0c40342d5010004001211b0000c8550341c000c60b0a080006c03103d201602c004000090795031400d030041207640c2098842c60300c0d9094440c010310038100d0400c81c10202c240d0210346603000b4800c1da0006507141c070281c454514040b4001c00c0041e40300340101a524030f03640e507000713498407800f0410754405200007c920819105100034013031020000c42c005524000010080d000ca455078110a0050b0302c000b03120485500d66100e03d00c142c0b166440c0030810541d0050020340034052420088240220103d50710f10403010542003410981400c2d01c404000781500c04c50340800540da00e00140500c0c1c3d0316041202a01c0c00b99111250700c40c0646404940d14004a0403d040c011280d21a5481c02d203041e041000610740a11413042c0503211221982c4141c01c00390006030040c025808040c0507483d00102040102c442201150028038100c000d00004030701030f0400c0c10240300452010b030460203000001c80f056611404c031908078034200407c080c0c82c154a031001c44000304242203070641c008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 816805368 1250 816804118 816804161
    0x17100b0301061d0406090b09011a2203021002240f040803100807080f01110307050415110601032003070e160201060321140901020a02090601170405030405040e030715 73
    0x2900e03640124000341c1400280401c050007d8000c3c001d44110582c003040041c1e0507c0c500c000b09070810001c0303031400b404540da01d00d00c0c82c4400780c0d015250b150990000791b1160315074541c1d20709550081000e100a00a4180c50b5010210610084c41010301c1103c0203801c80580034001000101003002550300028002c0b00c0c000e4498031014094900a49030b00301542c1680401c07201305400c0000d0290036181a9504509401c504082a002d0141d000f10300a41620b100081088a0420b1003428410054040308040303810700e59490400d84403c045038054500b103002d40c0c22202d4400c0c00d00049690031210070702c000450680d1041680c8842c1001d80d1068421135480d8100040416a9280d201e5007050380b010000b80550200903020b0030800e00c6020201000b2420b100e41941aa0081940c04013035030143da0f0403001d9034400c00106c901004520501400040030400c0c4000e2040c001b02410039500203a43c200716000ba0003c250b65a400f601c0d0000b01140f40b02c6491584200321508105266008003002c6004c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 816806618 1250 816805368 816805427
    0x7020706090b031909060615020a02030d08061801090603060e0c0123070f200904030504120c0806040f1b0b030604020d23040b01051002061501090f0617100b030106 72
    0x517641c0d44d4130180c8103107032280004c0c081c2412500d010301c1c003c041800202001c0040741e000c00c0c1c0382c1003122088424419230340c0c00142d80d0b80f5104100301c20003901501701c0542d0340c1c5419a240040080c1d01056078101d2400707030004070304503000840d583d12810503121041343c000d9524190300d14441404082d50200004d02950000900c5d2281c4020b5a62251341080750507055a412410394028140b0220301c1104003500780704c0031a070031900302c0302650b100e8107415500590034245100036544550124446104d070000b0172042c0a0403407031b0b2030b01480c894009120a1081011500b4483e4820700805091085c20008140d0a1905c2d42c014610700c070110300042103090070b403408010b8845402e4440c100c02010340040004000041080502411049940035000b034004a03000f50f5a0354020000f0102925801c51213046030f007c0c0c0042d800805481041c489283c2c0c461310b00038a48080c04490318400c004400c046183c00840300c2c182002c0eaa6034a4100b030940c0c1ca0000204d0380191000c0d502d480c450b0308500b52180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 816807868 1250 816806618 816806621
    0x110409030e0a0f170c010504030f050a02101808010b030c1201140408070c06020a0b041218080706140a022a1c0308070f0210091505011d07020706090b0319 68
    0xc00b407000e4000e25152404c80000c6000c0c2e415607040c0c60a81021083e100c0d241c3c0c1010035181501d402c212414002d120306d00e400d524181c84410040c0d4880940308200140d541d000f007035103024080e4010310710f12542c5d503584000c0c01d0354224142d455164210a4401c65182170014070155104180c0d40080350030000c402e25a41c0107182910296a4500b00094110a0041c104900b03c0100320510040c445881c00340c0f5107000c2c203c0701810060480c7d5001925420092140d00c0e150000c40101c12841001503590321002d503107860760b20604e070100740c0d0310141c085400840c5e03040c0c1700d103000183c01405040c5500383c1c190100d8003013401d01c0316500c04800e0030700119407241e124850300c94040442d00d420703c0300d035030a0142000c40700610b400100030304a40030544065011a2070b040c40c18000703030080382d003140074a45031110320160380203016031030315250001030100ac01024640703600048003010030507600c3c1c41c0000c036107910481c0194400309541c2c2c0c900b0070104456a0082d43d0240c00708454215101c11941c4080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 816809118 1250 816807868 816807889
    0x31e170708062d01031a0406060201050a150803040308030c0f07030e01030f0510142704170c060114060c0a03080a320405010b060a1707080103110409030e 68
    0x800140c408002c00000b070503d094090785a0000d40395120409002a40c0181041c10246503241055241c0d0610464801d52130340c4030009110050052100c0364032200020300900007242c0e020849400c4c500210801c2d03240201040a481240014501d40b03401c1d0341f030740040c950000c5c02c001c03040b20080059420b82c0d00550040c1c50690702c81e40c1d030070803409141030004082c1c41402100300c058038a004103100003034480002100480750710f01c0c8141b030f005500c28005012112034000807444e04000103407050100006001d11441544101c8079254858003c4454441c41d001d40e006200382c41c0d00910050002c0a11894140b64055006180300c0c03500f60010049418004940d004070085983c072414041000d4450203005442240d5403d503142c1701918850401d1400300c03110b08404140341075804282400340a4018451050018154035039503002e4460003004101c3c2080c02001130300c03c500c003251420348a0750f840e604032908089510884280901044002d0001800441c02c1c8010f10300141655164000c808 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 816810368 1250 816809118 816809131
    0x4050c120103080702031519240329060d03050304051f0504050c2403090a08130603050105010206070503040b09070e0702010209040e0f2e1107060b0a03031e17 70
    0x89841341c585106251800400b61110842e01c052201005143c21500094a4003104081c0000c18003a446000d844812003526445000c800e0558402009004144030740000150303500500c40c41c000c0c80c55144180d807500aa82180d4000c1b51320300800042446940a5034006004600343d480d070140a0b00080303840803140d9124a00b140e01e075070030002402014422000c6140b000d44502d0700b5000c1c484d410f1188282c40ca4080c240c00b000c0031010076a02c0400b00495425142c0c0b183c100355880b9071400018545031998410741c2c001a04102c00480d4651012600318026034050306d8543c15a22250b444010304c2000a01120052003800800030301260700c1c900080c00b950303543d0001642d414800d0b040c00280c3d4000c403c2041558400d03902c90001c1d07040003e680c643c800c918554141001c0000030354416400c4004214800941002c040d990251142002400303120f00c202c40400032041c038141440390f418240c4c031019010a1480705198094403001c03c5c1c2e9050071009140a40d40b0700014003000550002c251400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 816811618 1250 816810368 816810383
    0x6051209030906040e0402180121060f050a020403120f1b0807060f062c010312021002130e010617010b09010c02091807050105130b091c0605040b010504021804050c120103 75
    0x1b40401d40c2008214484d04080d9110041180d40c10310701c203034240f0f4004010819003815091501c00a104965000b80360a001c8010103200d58101591041e010750402d02056461401c4a01c15003240750141c0c104d1040c00c1c40d1500c84003217000349900c10514141c801d980c10f413010041040a00e000952620440c20350180b5041c0c005030032801c06141104e03504d07206d28040e011042b840c040080f4031104204a504590b444207070421081c0e0800401c030700700580030750381015080c00401d00c0d240c4841000358410a4800000301008541c2e40d0f200b003120405d10100d10030070090340356401802003889000c002c0001c0355041c1400076145025901185040504031030302d451030380c2c210714042c1c44400d0611505008200034a40182449499189514401b59500c217010318228000b0703900c04a61120055201c46c1020001c003e86004c019040c084041e003003ca80803112140c191001103090320f0240709031140005201d0180b1400011502488024440600b41410010051018902c11035400e010940614480d828 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 816812868 1250 816811618 816811621
    0xf0a052404020d27170901050306040b04061502010c1e0f030e070b0c0a060b0108040b01060f02120301330504030f0213020403050d08090c090c1b0303010b0715050106051209030906040e 81
    0x100040c8900b505c02442040350400c003c03180e084daa0010540360040e0040b40c2c0090710024100c0050000e0181d0b5001a13440790840701c00e07a00350b5030103602c40f41c251100c0e6199090f82c0c2100920950589040300001000700c0c0e050989020f071940701c8e13071003a040c89421004603240d19031544070310307410b0b50810098400f15600111810080224a0103034100070b10081c02e1069050620360341d03204a1800500809d82044821b02d1480d284500c200501442d10408107110766132135071510318098034a0460603125617010248080e40c1550306450040c1140d0b012550360b464141821652008003640704074005990100c0055001510401c0c42c2c4010002135208100401c6d03c5041c5d0f400240000c5001880068584c1001c0209001c51300c50160311a40300d01c4002480f036070740590181d00f80f58031000f94003152652102000100e415808080200174441c040c00600e40040c4c14944e8a00644800b4013400340011700a0041c03181c1c80c000400125001801201987d04107003284001c1070f5030317810503401000850084030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 816814118 1250 816812868 816812873
    0x2107030309110909010b120d0801170c0d0804140f06220b0c0102040302031501030506063f0f010225030504030512030103020a0b0a020d1110050f0a052404020d27 71
    0x21318019142441e10042c0c4841d223940d21001c0d080d104140304800070f40910117181801082d007404080c0744c2840040440200c0415801d10107421342150154089030341d41202402240d01d0000c416005540340107020720b00e04108401c2401028801540505100e003220360b0204100a44602038001c0300010000140c94030310f1401010300d407001c0920b1003061001500010b0003c1540410500d03440706c019150310b24a8005031118480c1d8170340345881120810100203440e46040b28694290541d007146500301c800315010940d515080340f08000c041206511208282000845501500b002d441e00a0800c81d0416680e501da45082c00394001c104900050004018811071601d101060044c01c07050180908107403400001968841c2c003048071034140091002151480c4000b0842200b00003074038401441582401c2140000064080c1c958080250402c0c000503000301d0700c20710000d0103188040755007002550711400e00009501a20002541580311544143c0b000003501d40d00106015404002d02c41d80301c40d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 816815368 1250 816814118 816814129
    0xa18020d1209050a300804050105030403050906030f040c0603020903060402040b0a0b0301090606180b2a120304110102010b0d0f0203011b0f020c03030306060706050a0e0715022107030309110909010b 87
    0x10304443da8a13051a10922010a003141300742c82c1550420302b40381c3d1b540d071502d0034140c1e03250107011030045d0700c070303100100300180d0100000c0468001d40c03081d0703e0004020b0721050241c05a003e500401c0c5e416a0100b00018050324040c0c000710703904100689000d51b030b251140c031000110740c000d80014070015200c02003008166440100440d29410351030941d11450b081540001146c461030b02ca814001000010400b15803c0c1516641c1140505030220b48445201c4507441c84260811202607503c1854030380c0000080d4018000c0324200c5100810a4140b0300942c2e0780d18140035048142a40c0540d610400748505c881e1091100104070150703100c560303c1c3d48109400918003c10300f01d40b580260010302c103000094031144107481046500640206179a56074429a6004040c484c1d41d1603482d00c182940024003421456911104a25039400d483d5110ba1004604040998142002601d2038080003080007180c0701c1d42c061300303115102d00310019401d40320381c0006000510a51705102c00382d6451000d6041072900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 816816618 1250 816815368 816815429
    0x12190302120406050f0325020d080604060503070315090803014e0203030c1002042409030b040303020c07060e1003061203052206080a18020d1209050a 66
    0x6201461a242c1002c00040c103074020515060f090581c081b011405100d003400c1c440d070144026503054403804003086002940d90824400400c0464084c601049643c05c1c40c0c02a403084d02c4024008141e020f00c4c6a075600c1140c100400d02e040e400e40d440400c0350002e0750020043d402461000d1803000d00b00840060b210318503906034a0003400c10b9000701032000c3e400100b6900c0c0c0e0380705000d001a12105842c5e002290840c428540d0a5089004410840d1782c00d24a540c0a00141c0322881c0041004001c2060012007154580f41040c020403410035003007001580314404035610601c2841c000d81041c80401d882407900340d00d0b4022401140320f5901180326810a15120740100480e4039003030019500e80040316000b920010b10103400c00000050750040014100800ca88141c0e401044400803580c4000041850b0703400da41400c00e650a00c15030410b003030400c400d400c01e4290010212451640150384522100b602c2c4043e403070070701803802c3c8005120f86e11607503460002d00c0b10b01914034400e0051300303105012508 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 816817868 1250 816816618 816816643
    0x30c0d112a010e04050603060a1d101406150d0f0b06031806221416060e040b0a271b0c060f0501030c09090510020a03021e03220212190302 61
    0x9045c04000c0155400580903400c0650701384001503080010389008040f02d02503411035440e21499041004c070130348030350110b6200512480e10700307c940c840800700040c015614104071044201402004150b0400703502103021319400801c000741410281010910b6901304466403071401b40c208101310015841805066808002005402c042d03013801c005002c4800740c4540050160000006400c100a60801c0095200f90940d800b0b4100c00350740301c0c1c00800710f001c40b0400038003660911030081a1820306003181001c0d80d40c5111400e000703036030307031061a030070703081403000c0320465a0f00e404449284006d0951051b02c1100c1e55595420181c100382070441c2512054424000f04918140040000c83d008259000594000a42c04610209142403803446e000da4805000980b9200081a41201e80c060f03000f08091a09200c1d10411882481d91300302d0386000c00c17554540d840d9a4499824543d0a00c44965405244001c051030f880010f080394062500500e6600c0340800c0303070303070018500c141901042440e0500d603 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 816819118 1250 816817868 816817871
    0x4110a1502100c0e0a031104020706020c0a0507080a080405060a0c0c1203111203071d151b0105010b0421050102031305070909081603020f060c0a0908030c0d112a010e04 74
    0x300360007080d4444c1740c512002d0110540c45050f0070303007580c558040314001034008074195118a40d90f810b03642c480e03d102400319214400d41d42e000840c0c020124004501135084001e4500781032801d07080c00802c0d0f00c03400000040110000200c00003481d41c080342d10103409607054290883c1e195140241070500124a201ea441d48a02000d4501c40031850887e42d1001c240c2c0b8000c9103a04251a085141078110700c1c5640d0700801d521012400c040801c00070f0400c01c078038200ca1a00000f0a180128202c0d0801c0c082c26020b8030040000303000b120001c445401d020760030072609944000c01c0d074480c5c508a8105881c084a011036030244031060010400a5002400d01c1500401480d070899890420520031403200c0d00700400f01c0d6050b0804e041c000e02005603641340c82002c0d50620b140455035841070381d2195400c00003046034204046100e240c00805e1780c0c0750345660340040895146021081d9412a40c00c0181115482410781c1d00c20750381008216030300c401c550444061040c2103400c0000d003044800e180402d001ea03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 816820368 1250 816819118 816819137
    0x9010f14090d02011e02030315010e0f0f0a0b180a051e040b0d0b16110a080f180a0603020c01111c0b0105041a0409050c0702030604110a1502100c 64
    0x4401408680c01040c040b00c0d880741e45500703807005840c840c1c8031488950440001c01580e220320303a0048010344c8180303c0b10900243e0702071500c005445954029080c0da800400003400903002d42080e118010304454001c00035a0683c0d6034a070b070040d0680c04a90410462585500340c2e02d018103180c5400d90103400c0480b4400c401c0c0222100d003070301800095100310b1195881d101c03461016128001140e01c1107401000600c2240740c1411410b0b0451a0840f110000440440e03160507410004114040701c0c50340310046038a4401000f0002d01140c20450440b41c00340c0010312941d0f415640c180b2644010041503e0140c0c0301d85484410740e086070041048680c03025020010095000540e090210b00a00300f407200084022411300101d031980102d03004441511a100340c441c110701001409001120b9022006001995a00c0c01c0c54200303015025000350540d00c00404500001c840c40c451124660018100600d06641c032a1751507085151030700988056001038025000341851401108140b004604003807c21 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 816821618 1250 816820368 816820397
    0xc111b0102030f0a180e1608130b0405010207020111061b0c010b0d0b0a050c2a0c03010612060e010b0d031112070803070f020703051c020307060504120923042d0209010f 74
    0x3182c0700787d0311b90040064103400100e19810350050004034942101c80041585024609a4000e502c60a016404030b541100300160108000450701e2140080840001541003400c02c0c3d030a00c1e400030500c2e44071079500d4070700920710303522040c0d1082070142c05501c20241c0303400c11446500483d040541510103d81c810070101d061014204a0903000748203a510324040740400a05240c1005840360541e5415400e03e040007070304258401901d0b101d64001c0750704000d481480c07005076088901762014240c1200c9a1468440442d014a10103184032103e0000d65903103660140a200309035100f101c0403545150080280306d10b5550204515811102c00c2c00100141400c54851580d14108200d2864007002002d55a000442c42807043c1c41681d44d02070014846411303d0300d0900f050958005030400040c0f86550009190090142481310b00400a8a4803104c8841941800090071880e011042c80395203a1a040750051065403007210000e843c200016111655100010032581e00074055804020340c06008240 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 816822868 1250 816821618 816821641
    0xc0b0903121e0c1b0601090b0a0501020109020a05061e04030f14060601120e01140903090405090a0f021003140906100b04030507170c0a060f030c111b0102030f0a180e 73
    0x2004641d0312242c5131605a14461055015003034280302000e4020395000040c3c00281e50005140a40c0407510280d6036a02c0e10012802c841002c01d000e0f62268408000304540c1c200200284900714203211810b01d0303284400100314035a44182d00848581c042000803005105c0f90f0360490f01c1c80000c100140c025810300e4000240000d0106c0305010704150b8400442ca07501744258400c20031a1508103103c0c00d54074006442e0790b00d9811080d49240600e06100c0010b010030700c08104045800d030b1003141c80d40702c00425024400c51150207604c4005041d07881d25540c200b4000c4558a42c803034905507004107840c0c40d1507440c1c640070502950040001100501041c40059804100c1000380c5a10011b5074140038455400280b410000e801c41d290031030032420003c50425404026042c107500c03281c5061114100524044660340c0b200d40ca00c2000f0b0304040d94a2404071040c8040444140e014411a403d01c0b502c528482c40d9a4442e50001f004940c481d018403981445c0c964072a4000d2207214038170b03c01e62074030020540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 816824118 1250 816822868 816822871
    0x10e040308040b060a0512070f0f0e01090b0f04090f11060c0d0516081201030b1024030f0f062d061b05060708061c0809010e010c0b0903121e 62
    0x203003e9180c65000800d41d44540542d4030042500400301203a02c0745244034030b13841318900e000d0400d01c0c42c41d80c200410f49101c0003090204460b020b90300000e013030386003040501c010681c40413015400407000750542d00c1c690b1103000c4c100c40e080c011001030002c61410300e00014215448510f25004134014003084400444c0410040809001414602d80d164041c0c481d0204000305200014003103800420551944102d841800d810b8910030304443c69036407540300c013045030b100c100d100368240d40d03c0403841d01000b00c038a5003141a441e00d031410082110741940c1c40040903201350101c0e449650b40d4074101003015107140d2000c030358000008450801b40da800d54440603030801c05030040b5030502600704c444045250310303000c0d1540341c03071303084010f0303468900707001c840181420800c0d03403040d00c181304100e20460400c80e0b203d1145042d41d4807281240c641142c807070040da00a0810301b6858180000921800041020b80c00007d2289604034080c50340c441602218003e0b080c0081c01c206403103144a0b000480180300c907213985 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 816825368 1250 816824118 816824123
    0xa110d081305030d0c08160c0203030a142a0c0609060d051803071a0708070206070305060102210403020117010b090d1e0c0302031c0e090406090b040c060305010e04030804 75
    0x10500009400c10610750300c02c0c40720340e036100b900d4102c6070450317140d002600b20b0003924061010082402c54620071620384804a1000c0d40c10340080210986142c0282c44100652810856681c00d202054600110401e050161210b06c40e05000c1507030303d04041817005403070041080f01d0031802c0c04880700102d000da0150340c50851304541d80c0c2c00030442040b465a124811144240e0440c1d5132008549084010090218080c8140550010201b818603000e4280e03a803151032107500505040d030711804120041c08020741041d055020341403141400f1103043d5014100308950880a80d500c91842c8001801800c0b44400f41001540040041c04010121001c40300703000412511004566a6404c00c4c00d12444500040f5005581882c05c048c2000f0311620400e04032402101a1280e46640380314110990845050030400203400c402d12204a19250f0b04541e046400b880000400400340d6440003902e03003055405441142e0054001c210007980360041c28050501c13800380c540c182c109590f01422240d00900b00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 816826618 1250 816825368 816825391
    0x40e01030602090103140408190309030203071b0512010e0607180e0a0b06040e0a06080102180103110403080a090e0606040302060a0302030612120d0b0d020f01180308030c0a110d08 79
    0x10803c00c1da110f500f21181ca001c0c026402c000b5800c0c41c4c41c5c640189e9016151000c12141030b80c6241078007038002e1140d0b40801d0b07096005189400140e07611400c090210b1490f00b2541c2c50301b11004034440d21003907003010004460300300003d11000094034580c82c00c1d038001d0000c0100700500014840c0081c10301002404c841e0120700b8404651a070000311409050001042078008102050008103a44c00780034181c040d058801c0200600354441034414280d105d0710300303000c01080e055050000c06511941c002100e0354030b100e03821402c03d922a40c1d00c01c0d807684510412800503030b01c00c0081c40079008411b00c06800103021514940382c03a28560109034a8050080200149540400020600c0e22107089a00d4400d00c200261100c444444076100750300d81150b40441c2c522460302594841c281441b1036040b01460300180701d00304140c50040115609084e0b03c021030307002418120004000358460001e580502d545100c01c58541886010080c0000191b01070400380d82d01000c4060601c5800513074160f049804941e2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 816827868 1250 816826618 816826627
    0x5010c29041a0603070e13050705030a0302060603070e070c030e03030903070e1b070507030b1306140f0c0a3f050f06120705040f1b0c1205040e01030602 67
    0x10802100c244014140c54045020030810040240e4005003a181510440c58040181c4030310b41031680d105414012030224005210100c0d400180054080700c42ca4030038400c0790f51264850000c42d007004c2540c1c1084002d41e000c24144102450203010020280441e105010851314000a00071320040868101506202d144c85001c5595242401180c605604c090200c0f00703036940c3c07034005840c00e4104a4030210341000c104c11101e400003001c8211181180c1101c003e10a0354159250b02103010000780020f981101002d09010000d151401760180008000541024503e070003000d0201ca0040249550300b09002040740e100c10a41061148000410b25080b040c4801e41850ba400450f0070724404aa8880001c0304407050380d227910b600320070300c078145c0051204441d4a5040600c8681c010b0708440075405e07000b0075400d10003800d26900c00119407185882c0401d45600601171081c0b4404030302600c0000501d204950414041140303000394500700309280c0240b030503141c40c801111040041c000140900d40018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 816829118 1250 816827868 816827903
    0xd050f071502092d010f201c020d02030d0506040204030b090a0c0b0c0d0815030109050c12010e10200a1d10021e100c0f020706080403090504020c1006080114010f05010c 74
    0x89551003030301c00401a010810919920956882c6108d582200d82280e1412550110510108004241040d07540095091101000da01405841c0080c50550880d40c20b001c00004100051440b600406801c809802480d040341415500038409400403003010b2003c2000308080b050014000a04c0316030352074140420b80720044042040925580d0b290342c03640c00c24030a0002c3c00030102c0c0d036000c0000210390a94a24201c0607a140c20b982c8841c0d419100d42d080004007940c010481d8100c00020a2980181a4103642c1022803a4064202c41400070000b0703091244c4000841507000d038506001002c847c1e032080d002500600a69400c2c0d808500e000f81c010750901c0703135031012003001a0700a508220388103001e00e41d60413400400041e011040c0400500c21034800080240c01904806c1c081c5070165904804a8204001e11010703500c010707465609442500f4404080c1407071840b8600203003160200201d0001c0c40d0481080d00307294182c000d0711840c15842c1c020000caa8003c4540990030394054002407030f20340380b030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 816830368 1250 816829118 816829127
    0xa0504140f070e1303050406120e0a06050106030507030b2d0d1b0e01030b0a1a040f0209010e0a08030a3506090901020c0d050f071502092d010f 63
    0x4400c094034031461249080e011000308081081e50880341440c15182c0e24211280101040d50700041d0115404200074060b8901c030b01c00b4003060092152020841043d50926946005462541075405a590b034005000c143d506024403a0070031700500e414001c0404900000e04a208006801108070380840c641f0403e0b1020600c0c03c01401900400345103100c045818241e070050030143d403070790003102c450350042040030103510002d068036081140300303400d50b5403411740400500c0e4816003c1401051110303ca042a543e40c0240321031030160041c05038a5007000b130000b508405079500741900c528101d10091102420000945000020300c0c9004400342001e4050381c81d118540400c180b48800c0812048039126120b401c003207001351030648032008156507180c3c08600b02c0c0202c0c10f0214803074004039840c800c0e03540b14602424107500a110180e29100a50b516031034a680b0b80301082ca4019000304030001245000300700d04640e406400021030300b040481d16060030740d0080307404c0303d41482041d128580041d03218 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 816831618 1250 816830368 816830393
    0x1020a020a091a06040824070f0c02060c1b0108060d1502090103020c0f0102220608060f03071d01050f010212030705030901020d0507021b03012c031e07150b01080a0504 74
    0x1d400c1300d5441d5121128161201058482c1e0f041d68280c0c04140302840201040301ea200c2c2c15190781c0d0003d00740380c5170000c5444416440c1c040c0e81c40701d0300b0f020000301340c2d03010312004100b91100f030f81c0605003403544800505850317001007202c3d1150081e0b041300d0010609001d258030550107814001071303a604030040160000e00499070703110749501c503070f442440701e82c00158000c08100c100e829040b01e44165281d2501d03504407040c082d1000140c40f18000c034015040008400c1800c44c401400e03642d445455001c03e4484426001c05c8042c41c0010754010403031810825400e040d03509080c8058015203410010703801c2944009003d08081000000000302150070a5068843c414407000090100c1d0610501c029940c020039a40b00010030302c844481000351605105410034004803c0090f1080c4140d030015100002605c481082a40020000f81d10f0f8400c0100001005244223a2443e4841c141414609100402d0800c9012482d01d00314484400740c1e002864180d0000d4030038400328941c0c0e1503180000c00b4940 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 816832868 1250 816831618 816831671
    0x230d02070813050a0b0405012610030311070f23060a030b040b180a020918090307141203040f210822150e0a0804180b01020a020a09 58
    0x40030414508101c540c0004001011050119248160300d500400911304090300c0f1300c04840800300000c002c1075014450b1404422000c8000c0c02407800a00c5116021120451b030100c40b0700a103003401d20400d0341000c944c0d042806008c004000c81414040404d00300542402004000328a1f00560030445072801c03000107034054081d02882d140e01030850080c01030b10103840403520807030910540c421182840307100907450207400c184010043d00e508035864029804000650303040024000581c803000d000c0c503020b50044141c20000c42d5281890304110400500052015105800c80c06501e07425000503c260b981094002c4d2500704c040000b458000450303411011140412800071504541d0300790000c08241c8682c2c5080307403001202d0802900381d21949003079000200740e00c041c5041540340340640c2c0d01c010342c40c140ba40c0841e02100c00365100d104480d0040c0d40810400100180f10241100c442c0c0100c038002c080c00e000400582040758001001e8135464015070781450f544003848403100d40300500100800340e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 816834118 1250 816832868 816832871
    0x20906120a120806030a030906122d18050705060d06080d08010501030f0b1c0501060e0405010b040b011119110607050f010c0507020a0b0f0702100c120f230d 69
    0x3a061030320b085041101d4000c0d4022460000000c1c205080100d45c4201c6075a240c5d880f26034850a14001b501e21104410324031714603d179074503a400504040340c030302d240101e0300358010074092914059a030016510316102d08015000d001300c503080051400960701e029148200c80302c1e91600b0011042c00700505640d80f28181601c50010a84141a000f00388641641c1d020f9909005050124802000359640c000030309070400866003c0005840540850414152143c1d0000c5400c0340e4480309c1000030841a1f4040c0c400e40d55601a8034001e280601c40e0b00078000081c20561501e0904101e01c949070b46041d420310326030614001e05007003008541e05440103941c0c00140360507103c005909100f96246003d080d1400d140d0702e040304926005020310181c40c15594001d11000c407480c1030015071035440d004000b00700d041c1d0030140501001070b46c590507020705119a40d40e0b0981c03581b009060841d44060601e090780c090291031800030301d140c3c1d031110150000392a02e40803401d8400d0142c0c6519410b10035022942d00c0035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 816835368 1250 816834118 816834133
    0x515130507090b4c120b0f0d122c04090f020a0b090910050a1a1c02091807050a0e0f1201020415110a06110706050c0a090b120402090612 60
    0x503918410880c4e03d800440c6216152062149080c484030b02c104007107000720301019090307090011a90451925108042c0c0708000c45109075001c079200c500040002c4030343c00a442105450a039200c0c88082000c0340b2004207600110644004280300519212000d0169480e80b509409118450000c031305401d901a1122004035550603a103406904200082489110701c0f401050a49004652800540b800101a00d50303051500600e0000400e00d08010345118000740b01c3c0190040c91441034100142c4c0307149000d42c0d1b5900c40e20400c0b0050442001e0050051800c9052205141d44641503071964030130303400e000140040c01400601e01c0c0f4030303078080c00794403c5040f105004030900c10b40241007201c007589540380d110f9569250566070381d4510004000305c1e50005201801082c1c864000303000450703d0700410761070b0030701d2070b10740c4000d071102114800c030300c400005500c0b00c0c5076031b200c4002401008501d030300c24100445001408994400a00007a200f13001940204029903500e0103060341d080022030446820 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 816836618 1250 816835368 816835429
    0x7061815030c0516200406260f10051611060a0f0e0102280801080309150409020a02070f2907020a0509240913140c030a0515130507090b 60
    0x20503044205c942124071110100804600300380c09204140d8078040c45400c9008406440c490b180c2941301c1c02410280300d02040714260f078206101c4070280030306011000c2024640640e01130440300c503440c2c15900f0416040c860f855100c1d80803441070340120105402103010f014607030360000a06015040c1030f000e544002800e0042000070b50821030a10306024030714203107424900d01543d442109125442a42c0c204203c40710092602d1404056030314600e04d0f00034203040d20380074001d0481e001402c0020142e400302d170741404070803603480034a401400b10146010003c15a403a1806034280c0e4040040740036800801e4903011035551300d4048020303102c050328241c07051400304094012307044041a43d001403038000d9940c80342d9007001060385204014008440c0c060000590310a00040c020701c501791214040d411401080d030394248100c0040c3d9000740d00a011811010801350f21008028240c20010b01d072902e9075400080c0046494403c95000d0a030000d000c44051010940b60914201c1c400e601c00c240e80c0c4407026 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 816837868 1250 816836618 816836633
    0x30b1c0b061e15090f030c09010308090604090c0e2e0e030709090f111806011101240f080d020c060a0c0f2003011e0b0a0305010203070207061815030c0516 68
    0x1003200c00c80f5001d010241700024103458070031842c030498105020350014000300300c800d8018000c1035000340c00a40380c95075992058044602c44160071001031100100c8181d945072080c40000c032803040001210078004418003c91f860528a1444000d01800ea2405800750b0b03070602c851802000d18100031710404d141303441c0c2245a000c05ea60112070610403101c6465840c146800030a25040c03400303904450f0383d280c1000544040c1c1c404207003510b0b42e648501d0b001ca0405c5551902c0c178007280411f0351018005052042c03503000d02c099904040665440030b024841c00507800654030300e15200980750180d071351101d41070459803d80310301e10241c040c004460f14401000442110502280e81045401144c60360140405080c0c074410005010810340750b90350500e40d1a007a602c00100020010074465550380d0326661030b400da8004841c0c0c0c1002d600300c107004000c1940c01c0b4081d4004040406910070110b8145280d1004015000d211081007542e282c54004e1a140a80e0072a15040ea90342003c5171171481501c2d01e0070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 816839118 1250 816837868 816837877
    0x5250f05070b0a091202030c0703170d06090e071a0d020307110a08090916230705100b01020c031207110d1b030c0f0e040b04050a0b07030b1c0b061e15 66
    0x440051140501007174952010045e15110f020b000c01034001141383d91141c100d40e03456900208001c103410441c03030b03281c0380c0a48512802030170b01e01c40c04500c090011610394284900c941c44200c0d00c10002d4080c0a405121104a030a048152440141c0341d44460744121070711050702d1050b43c00e622071406540141701c1307454054014448100d504103601c1e59295010403440344d980c003032100407030046070801017401ca840401801d40c3ca486103403141412825156540303822011158101115611035800d1001e59040c8007a2960840642c003d0030002c0c00004843c8203480b0f40c42c005050740c0711030308202da40c80d6603090500203a1a00300748100401c2c80485443c43d0303507200ca4842220203208003540001d0310180350820000700c904200c003c0040356116242c901312440014070032103181c040c1c1d0100200040410000c9030013145241d80c001901510750052219000320300c02c201105c90703095004007002500050200303604c024240c40d1103006620300d0951482e035810010000340c1c4241d4807050003c0001c841400703403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 816840368 1250 816839118 816839123
    0x9030e10020a060c050c0d0f12020a081503060603060c030901060f0b030f0601020106080a17120c070309060e0901030f0512030c0a1211090d080c03180405250f05070b0a09 75
    0x2001403044c546400e0300d4a1103050288411a04684602200140100c03060a02002141003ca14803074007038145108036800164448007240c01e01050210756492004030000c40d400035030061402d414004000ba035925001082c101c8500380000000342401d0080d08030100030300700840801481d640f40c09500100c3d800c04c5819000010160002170000d42c030502a0318101e9020780b015242210a40e01d4482e20214500c0d40e41e8442c060400c2184035550b0000000c1c0c0c0f086c5000c030f03000341d22403400345001440216190b100d501000080840340485698510429044940c80101054442d070700d403400d60f00340039008903c0710072003c021080001c030208900040c4150180d55842e2540e003aa05c1d02644221001c40c0c1b40c18822000030301c494040c0d07080607664080c0c154060010541003001c1602d01629650102e503000309000fa40712511191400e140c004c040c1c100103c0d444602d9858003074a043d80001074840c14080400c10b18081001415000b0b4045441c06a00940070312907900d0b10100ea00c014041d0742404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 816841618 1250 816840368 816840371
    0x2061b06010b091f0e010c0501020f0c0102070c0b040b04150c060e010605100219061508010608010f11090d1e060203010f170d080c0a1101020720030102040803040909030e10020a06 79
    0x302419070402c0c481c80c12904004d80c5580300b24200c2c1c100110b07850b02040c9400c5a544d90300b00400360340d0f129500041c240001d071140015980d160a450700a035003444030350020304258414441409401866001c4d50165000440c0c1048a0846030408a88011420002502c9907190502840d81604190040d030103940341602e11403e02d00d02c0c0d440c102d0350740c1083c00140580310704024101d030005105400c20328441000b20001020a0345815100d802c58205610400c0302da0b558406801100780c4502528030398800c0054030034142101e400c0443c00e0b10044440c01490160024000c03a2400c1c00045801d40035604105c04540300c0da140c3c410215444001d014401083c000c12900082d101c10000d442200301c0443d03542e03400c0d40c2e00c640e515003050390403503500d40003403041160f104101c0311003d01c0a0194140680103a1420001003080030300004250714006000e0b0740104014003031003a00104440840c0e882001c001b61102050030101c41e10024415200c0e84581a038a665050950010b043d004045c001c400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 816842868 1250 816841618 816841639
    0x40f1802040501350a0515150906060a080604020d0f02070b010803030601050d0908090909100615171504060b0318030403030c0b0709180f0b09040506010302061b06010b09 75
    0x240e4151401000000440200303e0388889040c0c0e05011203219203076000e84d4215883d000c420354a440c14025035004c41d0402500da44200600b556410501490f03d0740261145000c2d81020004549240305950350f034010705c050300010070803a888540c1251100c0ca001340d070400c552510301007948065132200703a0560781a000d07540080b81c03094002c01141e00448050310744e503103452490400d8001410034a5400c0c1d078464018441c965141e151140305601c10724000b4043c114400005408204403089500305103406202c094110a01da5000301c2c0c4101d160b850300c641c5980319514011007100c410545400585c10030709060740003070812200c1019501480c58460031a00282840040d60398030301a0384400740002c0c10509803900402ea01e40c000d103400c01000e180c40038005440e032549038a0701903018600d004440d030b142c00b5403003407030418071901252180464071005170b810301e0b840b1a56a000c06010283c460702001440300e0100c0d100740603070300022644106590040d0f1350b07602259065002440c100703014414001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 816844118 1250 816842868 816842879
    0xc260a120e060705120a0f0219030e0609100f0b1e0319020d060207030e0405040b07090e09071e1502030a0e030105040b0103030e010509120c03010e030f0306010e040f1802040501 78
    0x10702c50b00c155101d6441d5420004003500d02071072402c0140070b4000c0c6541d1800b0704403050450303000400395003642441d0384441c08543d407001811107010080c410407603000f0005105540c0c1002c070b0301001414148c0c0010415444a0303100704018101000680d60248100010101c5c0d1005000b81001c286030031010745000c94006003003080090300a0074000c0d408040d8100e020006981c0744e02910085000b41703402149082e2040c08170741110b034242c500759407540c207070002c120340250b004060601800000707112122a0400d0380380242e460b600c6020701d260010351249800942c003910301c0100010901d1042480103185004800307074803503000d00412000601080f0181045080c140030f841c0c00741d9031114a03204c1983ca140c9084400c650728a8005041003810084e482c1103950342d440300300c0241030080c0904503094900041608441039000c3c0f5151541050181d003050010f504141da85c400020300705140e2641100740094000c007806040351700320f1468458605240d920400782410118802d59040003141d817280c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 816845368 1250 816844118 816844123
    0x90b070b0114060c19030905090a09110409050307022b03122a080a0608030a032c0706050703050f0a0806030c09011a09030a02030d02030307030f0605010c260a120e 72
    0x1001c014403142d1041a005c20f0303800000c1e80e00c118640c0240f404406040d240e0000403064001560880a21501c403080c030000c2c01040344207200e80180444080140e402c140c0e580503164091880d01a2040d03140400c0940c41e041c8505800b1450802c0c1d0030440d001c0c405624003d4945d01c1603120541c0c920345403100b003140740c1815042d1102800c20080300078801d9814800d040b20184d00042c100c4220760707180c4100140442e400c101030104041c10307881c0409d1820741e1080c80c0d0f4844281c1da18003000900c1c8410700c90300f5043c01061810035203100d4945a5910304240c1000e4815208108a0030a070420000341a0b40440e0b1022481c3e00548044081d1101a1140c01c01c00801c0c00080c0150107015910800d015615200040201290800130b0240e80d4110035680000741846e29101c03044001d60400020021902e82c107100700b07418020950002c00c02c2c54100070009000c0110550002c0401c035203995141d60b6080740d0000c4514141c00982001c0c0d840810000003000328170010f04403602a42070242c2c071140c542c0302 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 816846618 1250 816845368 816845377
    0x10210249080706200c07050310060b071725050607031a0f190308031801021602040c03140709080106060806030c10140f1305041e0b01090b070b011406 66
    0x20150980c24400183c840f003005254481c1110960074030070070125001c500c600c016024290850001e400041d00d814113040c200341c0e801100900184c81e000060100c40081000d94105641108100f010198030742c2900d2038612566805008076132801441c2e6010810fa000d4900d5103e20500568070b1644070414180c064500c19401148844c4200320140c1c00b5040002002c20f89090040500d11485040d413042b091072299500117a03000e002c000100b01c8004a10000c058010301e07000000c52410007060b082c0b440140c0c034004001d04c01c617211440001c10f14860381142030f05801c591100040c81c10000800340082075248500300c00c40d42400720015280b4010307281c0c98810309000d0041d0440d00304040c100301154440307240c1c1c0320910040201d540200408200905070f1415089111a81ca402200050711012480c2d0702652082c3e00b400c0711030030426001c1c0d10f8448100003211001c06d1085900c40165180455a040b0038182d61001c1000000e0010704050541202c1d40d449141d800c41c0f0301c600c1440b91501c507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 816847868 1250 816846618 816846623
    0x13060f0207230a0311091006050708090d0b07030b010311121915080721110d0602160b04060507020105070804080f09210610210249 58
    0x401c0300c080203205040020000342600e01e98841c0d1074074509800281c00325196400950383c1e18004000b200030b90070301403442a04040700d52100c0340141c0c54860300030014803031164010082a4042041405500c6200041c485150b2054001d1118507010030300030002c2280d184000d00007400d104a480000c04400102c1e55940c0340103a9104c05a55040b00007800803800418202c0407030341c2e6140da0006505501101d801400741d03880604030b07481c80d203a0440e006080c1001000700c6444111200d60000b0103125030144040b4003a00d2084c11080d02c1d04101d4024010b5503030103085041d00000d1078040100c5042128420b51088001704550b484440c0120308071502103c155010500074400300d8045003804000e001011210b4201d81d2400c48032401040c1e081d442c600c003803000060b078420b402110440a014003030780311503860750801e681e501d4145900700c1100a80d101041041c0c802c9880300a40d281e0300c44440c4079107860400e4103840d0700500c0d0380051401041c1100f05020b009855075034159200c040a1142994 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 816849118 1250 816847868 816847873
    0x81305061e300912120a05040c08070807031e030806090c040f2417010510030e1e15061305060103180c0f0f03050312042613060f02 58
    0x285030464142440e0b1250340b014490700745100740e880d0501c0c0e80d02c100c40401511100c8001140c200079011a1030300003a111540f018003014001c1c81128141003185a51002111202055644032803c2524000081d60040d0315240903c0c2004071f0105800a01441124030456903180e5000307103a0f52410048494000050005a036035020a0091800c0800241c2180d075921030f481c5000d80c2c601c0b40d1402000c140d440a41e54991f05c000072041c610011407d0510400f06003086524034901056074401c0f05014041c20b8801d0103010800d080640c401c1c1d210500a0610008444a103a8003c0300c0104090f030041100e1083d105501c11030840f03040120f441401160091b03c40310300d420703082040300c1c0689002010310741003594400c0c1000030700900d03c0c041d491150180d04080380107420400034848442c12900020502042d181c8100005400001243c60b4010421490551070f1501c0c900090090000c2e085260b0095074180b40c1c41c5014102001005001e01101c940c801d0f05507511001e13115450181d07042c20158 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 816850368 1250 816849118 816849157
    0x1803030f030106031d1b180f010510051201080307020a081903030f0b1011010506010c150f0b0603160e10050d090c1d01080d020601080a110d06020708130506 69
    0xf2030081d00602030700040b401104c00784104083d2818944200340d440030210b1070041c02a4103e50403d20604001511841e41902161030803258101c2c144030103200e80c0c0d024a5006101c09103883c81102551200145002582a1035070340b0355600e0340d41d801c4490b0691049900e1000000c0d55a00010103030540c0ea10045ca0411408594038281c1c02130103501685107410347c8070b002002041d524410711100500307040e211820240840106c6a00b107a200421341c0341440300c242031041c0441c0c2c004000c0580c0c1c10300d120010a965042c510700034050071210b00d0080d0003020100500c41b40d400700d40b2021240000e95540e17000ca04540328200b08440c41320311500001b042c0200301000c02501a82c0101c905e150113010800d50340c3d952070880b144484c03032100b00c000b1200780c1c03080141700341c0d03030140805401420b01d84018841541840c40164a8070a601402410614800107415050322004403034100513400036801c5440b1045800e0546290b4010074202c0c0703280d40c15400c00718044c038180040c0c4042681c1400c0450f000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 816851618 1250 816850368 816850379
    0xf191e0f18090f0f03050d060e090712050705030712030323010b1b060a06090e01050601050f0304300806030a080906070203010b0406030f0c140d03030c11070603021803030f0301 78
    0x18644001d083d140701e4448501d200101d40e01d5040c00681c00d210750781d100d80d2910780c1d14844089070415046030307141034030401c107005499800180660555a425400d41072039403841c84c00514004095008a170075004103c0001025100307003007141a0140261414884046240c514276209490b401d08407000820000c01071060045442c0030740807418289100307442d880740d916070080c40c0102c1150049581d03038884c802401542550b019a500c02c4030980c00900c0a8140440003078011b000b01c0c144090144400303c0024244410080d00c1400d115100c01820304403040300821110300a00c0c412020041440304000c01c1c124100000d0040c6000d0300b011102d41041c10b01403c0000c56032000f002641e2540d26000404059a518482d440040d0f100e0b88c070a040342e40d030524101c118003110b94400070704641420041103407a140e1301e1001441a81c5031600180402c0449000d4614050703041d114410ba12801c1c0b03000c10210b030980d005101100520021580e111441810565240b01d0100000503a14080c00100705 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 816852868 1250 816851618 816851621
    0x90c011b02090103030f0c2102010b03061e0c070f03050306010917060a05071205150414070912060f1b090b0702180a09080a090501090e150f191e0f18 66
    0x100b031b4030901c1d0084d500c00d46510b50840054681c09102380590181d00003000081c0c091013958034406080c1c0241040c1d20303004400542c51030204138a02d85c032103101400102c00c00c80417002c032018198050314030521154076080003019600f04a9455002c142084004114134500d150303180300f40f03503104c4001e28460340c40701104006410081d11003818170000340369408035109030b801b4086c0f10366954111600f42c130381900300700425a100c1e42d140d600960000404d0006c1c40343d002c0c20403010748074480e0251003813180310316002004250030306464a1103441c14600c02210b5460030307008111255180e5642071040e440d081004d8051185410095200784603008500134401d034016071a0303100744480030000e0040825160a0041c1d070000203401d00217904060103109942e00100c071200a407411000c90407007483d008880c0c048140c20348801e244121002c10307021101e591112003400346400011008599582e41c0c41b00a10022010f0452080c0c1c1000c80c40d010400041c101c504604039000145280c68640360200c4000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 816854118 1250 816852868 816852887
    0xe120307110f1008100e06090a0908160605060405070503090a030c050106051039060923010f1b09060f0c050703080c19050718020909090c011b0209010303 68
    0x7508801c2c000200040303a03440b00e00181c20315a55480d1a801c0e40391800d900d8040071902d4001840700040700e000d000c000d4640002c541c0e400809080005288000744c2841c0060340036518001c0041c843c02d540d01030810160390440360107244240e9040c40039881d14601604c041c041118564900e900011802001ca84101e4003e88100c0c000d800010700651682d004c106a180c0c03069113a00800d1050003c042e0050b0354004089c018001a19031410041034101034082c0c00d0210034020303181030b881d2400079007403085030910448402144c0740c4c4411081e1a080c0b099010307084071b403004220715180035003840c1502900c000c0c414891702c940d80e60802c480c1c104041542e180f8454030303421040100c904030315030005d07904010741c80203140282e054a8a0f0312050b0306071450061740003001d21440ca69402c181c0005000000c82c28251074855130072031a411b041d0421500280a0501ca00358090740700428018851008144008000310a070307102009064407030481420105000c00080d084400039004202003031041c032804 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 816855368 1250 816854118 816854153
    0x6030302060c09060903190c060e0d12030216030e010221160507081014060621070e150304050d18151b0c050909010606021209210d0e120307 62
    0x185c2401c00358004a890700c540c4e010710f83c0c81901220201000d010070381c079046004104a152280d01440042e000c0b0b01e5401c020000105004502d80141200038000e4059940d4403240c2d40089102420b581002020168108903160160190702c0686a00610a03001c0c48000c80c5541042c0d0b140607600003442d00850f8a00d4400e0780c82c0c0c0241a404035612406100d40d01421428440119030050003600510001c1005090584201c5040115640c902005070310714811105d45250240541d444050644a12010b0203241e50b0140c6840e2200c405418130710003540c000c034004c1088424074408094181c80070001845214000ca00703040040201210581d00c10340c1c05030481c9001c5100b40c80d04007099110020052086a08101400062001c0e003040000241d22802c280d0080c089d00340351120207510b40007078060201a84400107015402900c1d81c420840710740c03015090547d80108180d5146440c0c0e41da810b14100061a5020310050781d2408032143c0c0c4885000034055403410784c2030b650701502c001c0c0c0411a03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 816856618 1250 816855368 816855379
    0x10050f151608030115090806040201030f0e0d0309050c0d0201050d020715020c030a0206070315140a0f0303050301150302070b0609040c0b0a05070302060a060e0c0c030408030d061806030302060c09 86
    0x188030010301c4035054060910710070b8850b1500c039410300c42c4038600c2c0c203550302803030302000344001c020400c607034001076840c2c1c22540a007800650304030b1900440e40644002c11100e04903200d90600c030320849a0541c400e08040340944141c031503800b28803080010441081401900082041c070410301844150350040c510588030395020250104209890310581c1c010098048941e000800c10260072a01808200d5010301d980c54100200e094010340480541cac0b103405406000e0700360110329500d85d00c806021001070512010200c3c0a076a8034a03000700380d50300074090ba201010320b03110400c401900034020303140303000c0d400540c2540741d81d280c0051050001004105503203440c2e1501300051421520350082075118a01d9179104d0341d84c0c0c05410b0180c0b5162001d404180d040b45028803c10140703440c02c08040c1c00049429070703543d07110300c0701c4d5000e03286016580008100b40000034070701440940b1139008404803104000440070341c5034200c880f02e04035074103440060003507001030002803c22900743c0000c000000d0000d02 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 816857868 1250 816856618 816856627
    0x3040210180902071b0b0f07050c03031201061b0b070e010e1305092a150d0507090f0905070f0f2a06052401082d0f10050f15 55
    0x8082070030715407070380120209a40058404180315003c40c0440ea140305001c101d070120751614012282c50f2107020b0079014a02d601090190410a080c080740c0803506004080b2a00d074194502c80413044802841003402003454900c2e0801008030300745080b41c9150b00000081720300d40d40c03c0000d903030411700511018101b012101403666559645003600e4001062550000ba00e4a400390342c413468600404103840f100c100701c0072032612194469078012003c450035a0107a9200508003540d001c107024240205aa00f424401008041a417251403201103d01842c0e40b401e0b001e6440c0030003801c80c0c4003901c2403c0002e01e000c841881d005d0242035046a102082e2074152250090028100920303299000c00c0f02014184002060a0021a004840d00812040c2c3c16440c155422a05500c140c210307007564070b0501c03d0800001e0f54618164421045a542501562074a42c10145410110030422a0000b001c07182175070124000d0780c50107230114181d4002400c001d100c111000104001d414040d4494103c0d04410807 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 816859118 1250 816857868 816857897
    0x30305060409120201050702061b0403080a0201060f030516060e0603070305040203071706100602030f04030b0627040b180c190906060c060b030105060901121b150306090e0303040210 80
    0x20400f0040248070b07400001c1d0380c1400e0000900b00700019040b44803409010034032048103c0140200d07400c403980100307030550703804000d00140d02400c0554001049421500c500106000c03021812400c40e122000c45600f81a071101c600740c501203070031800650408014000505028004e0f402550464001403c0703d51099440ca01100400c2c0e11003804201d90304000b013884003104000d05040d014041c1800035600f0141400440200c41c015848054080d01c4041c02281d5a80c84d061a0301040c95483d1607a803204004001150201030015a0100c60150002c40060055042c031041c99500080780c401501000c03070003008000000440720241d0401441c6000c00003203030006d611440004041c03035103c0c0382c2c0c0c503113081c01c2c448221256602418040e0f41800d0803c2a6641d0b903003c164192840a40d105e070300e4801d14100002031340d420f2084004c88201c452004120100c0e001100000c5c990745070741c01d01286460700f00308000e0361090300c3d02d46400e92041c0702060040c41c1464000210007036500c1e1074035001003c003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 816860368 1250 816859118 816859133
    0x10121b0c140106031514010b0309030708131d0412090812180402210a140105101215050f0a03050607110a0605010f05120c030709020c0114340c030305060409 69
    0x1910080340595183e1410381583d1b49904070600400b404c5c0b50150852802e50541a1a44542003009014103400070b00c00e2441202808410050030418140031401c0090030280e26202c1d906540580b00404811200d10301e451280c054001a11125805041c000200c0d514104083e0088030003e42600c40b50030f05114076031140d2005d40314001d00580da40341d00100e00c00d080c50220001a280080803402e0176200d001010300380c0c1c0e56504650081c0c1305140d00c982045c80c22181e10f103a40342d8000041d41082003508070b4400f20014103040e40c03821901c5441600958081040100c0c01c0d00c001480d6070880350018525034051000c0c019000c0d035600540f01c0b80001540c604044075002d80254000d14200d00082c01a41004482a10707540c41040003841c40c1c40001002a070740701c2c9035100d0003041300e40000342c8110108080d01b0020882070740c07903c020401d0400700c060380c0c0040c031600c140018801c8502c1c8244840000f62108000070405500c54044010716610700700c2c0540401403a06401c181c8075400e100000d50780 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 816861618 1250 816860368 816860393
    0xc020402031905070f080f070903080d0609110703140702010c0b0f011401050c0a110105040b270102010912030b150409020a030e0606060f1810121b0c14010603 70
    0x2076180030220340d99103102c04040340c030702a01c0e10303080056281d8081d0b1a990000b14140e00064105280040765594000403200c00d20307a500010500803010502640c81200da810000548254140501c52001440c2c000c28141c0030b004006400103192403031501d11190000024003034a8018505803500898680320400c14660540d04050210ba00400401c40406031403102c44440e082441e2491030140c0c41e242160f07032450009405440c60410b203280c0307283c1c1e0b8002c1044400501c0b000da90356031504e000040e44540b589800c41c950414104441002031298411310134000c3c03450b0b00034070040100381c2e03010040380209061070300d20b0740040c69201c0f40c0c2d44c0426a0301c00340004020114002d0390b1002c0b101c9008060304d044006504541d80400d00b0300401e66207803000e54507980ca001706040d4946081c50304130601410560091908103070384100d0003414641c000e40014600140200034002030780004220b41140c000d61886c6000120740480b4000040c5000c9134450341d0140220000ca0101e44a0701d0b2500c1c503800c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 816862868 1250 816861618 816861631
    0x3170c040e220c03060f09020f120a1514010e010e07050705030f1611042009041401060e032b110a02031002091002030301030b130f12020a2f0103020a0c02040203 71
    0x10f41c0040040050600580881403004c900601c6034021035404901000b400d036080d60b1103446143c4034a02c604a007001144515900300b03007195440c1349488584c0c80184040440e00740901441000070030382045e4020654100c0300019406c03030403641c400b40c00300c42d640c0100b4821141d602007004131140710b81c6e17098068000024064460f481c075099a141204c1c200c400c86e00d0141c010390402c42d82446c00c44c1d000d0f0807d0b20344506001d90996a140c07000c00200100141d400c8802200fa9000021402a50100e884003c1503004c1d001c03200003c1c940c02d40c1d81401207118244410680020b11540d140c24810221003400c01c414800321401016a580000d041c103555443c4c4160f811303400305d1a412035103002450180d04024a001440c80d40d415030b140c100b85944d008144070810242c000321002006400e0900498032a084400c1c6010070361a60700080d120380848005035002c440081d0300c90515094080802030589400c07100203500380d034500054010390000808801030001d0f200443e80540c07181d0000b58030bd401d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 816864118 1250 816862868 816862883
    0x2193608010606080603151e010e07120c081501141809092e1b11010c090e0c180d0b040201030f0b062a01060801090c0b210c0717030403170c040e22 65
    0x2e48070400604045145602c4041740e3705052007000c001d50080e14094000c2040b0360301580e0121858010384940c80000402c04100c00c0000303010000c2a030700448010106011115050203450703404403a80e58ad44514900c44051a08901814807180c003c150b00240c080a0b4901003403040c031307140c403040e41451a0822840811850303442c0240c408428401ea801d40e0b005810040306445c1020451451140c0040002c603592000042d605019200324822803d081130040c00303075964203503510b8a519072000c203840413404a4280200c80310f14005501828103600d00150610b4280815000300c211442960400310700c0c15240c040c03085418036070030700031400074103090000452100164500030401308261703404400000410310841d41c1481c218507019028a018140e031000ba611400c080e00968403441c0401080c100c00341805141681403c400b5510079802600c13041c3c595000e8a030361105c05d02c411203030030320480c6e8100010322254015118030303900100c0c100c800c02801c503820385040e501c105030f802c2c080e0360350b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 816865368 1250 816864118 816864121
    0xa23010e160504061403040602070210020a0b0604051b221412030a0e130e010f0504050c030d0e040e0106051309051002193608010606080603151e010e 66
    0x400691109003010380764078100b482d19241600041c02c0249140c1c00b10310000001021505014258056900c05a0014800354070407440000c003941d28501c6c2d10703080704e1000b084000960507107010303c2220710030201e040c8800008441c40207202c3d115070008020f042c041080c6540c00503004040c0c8030713000282c100810003000c4082c09900b0003208015407680103101e40d10070800082001e90140c0300e201e0a100a442010700f1444030490b19029102641c0850080d600c1c00703440c0c041c4000745030000c6000d030740220b0076608505039400c1031546441081c0107080104407252921407031824541d00c214102c01c903010000402980740c500180c810300401054134241515020910140082800000300f803401ea01021807a240000c02054940d600308000c900038032400d105810032410041501d9030401d100c0340203140d042c0c01c40411418039501b46004d80d411039031900034042011030081d50120b025180c010001c05a01c00c62203c00e01c15050024603043d6081c041c2c040f00050010030b0308140340a044c110401503050b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 816866618 1250 816865368 816865381
    0x161103043b0a0b04150b0903030d0f020901120207020d1104110408010b011106090a0f060e0321070302160b0702030403021305010501181203121b020313050a03020303030a23010e 78
    0x15181110040e82c41103142034614240800001704200c1181d0610300d54580f603a03840070000c3e0071401203d80d4400e51034240f032005a00d80a088d4000d164600d000d0321448d11003c41c02820350128000e142000307410840b83c0c0d500c0f50105a5007088481616402000814148920140e950803a0800d034812000e980d140c418204156809c555001400c201901c0140b91502d40701e40d5140e40c0e024045005022006140706082c14800181c021440d0654640c003100e5507031800a0b41c3d0606100c41c1c1d9000403044178000f000c0b03030040b4440d000b01d541c103044880600071954440d0b22114038a02c00a8510790551200300300000c0181c481001a00d22040380c0311001070950301d40000540340f05260200300480140c4404c1c140b01c00305c111504240440d030140f40540480d83c4062181008001c20340c0da01b181ea20414a4901d581940000201a5010041c0580600c40d6441702440040445400002d516800c244002001c40250780e1000002c078007079150300d000740d8541002200411030b0030b81000004013155000c0080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 816867868 1250 816866618 816866621
    0x319020c04060e060a06032a0f020d050306101b06140f090304031211012a020712020a0e0a0207060f060302120c0108060d0201020f0312161103043b0a 66
    0x3482080100c01e0f00c0c2c50300100040408482d40580414540da649400e15090205800c05101d60714409401c0d5a001c200c0c103020700910030f00f07001c05005200d2203d44102c4a403140b000ea0340245d402905000c0030000d508019645c0c8040d00c4985604c1c01020703032115002c66624003480d81b080003d00f0306c1e441282003a41d50700340b42c004000d0000300660300800040000408480c60440b211100c2c1c945084003004580d480c0340500204c58650946400d486100740d41c0d4883da2011007800702e855022036925640d20040c81052695405001e94000c060780c0c0104114a00796111a51042850400628059040e91680100d520300c000401d00542d6600c805c1c0210b0606101d50303000d06000702c005061801904e00003e00c00c000c01803845c0d005624034240e50301164000c0000b02c15501c020001c0d280c407803104d6105801d50b410f080f11641010075240c0014207116000c0c9182000c07154480020f035207041d040003941050580b510a20208104aa148440715201001d00055694105031403042e21814071300c1c0d6460 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 816869118 1250 816867868 816867881
    0x5030402190302010c0206030a2318070e060603040c08160303080c07020922080706021e0a09090b130e0a030905040209030303010312032408060c04030b06040e0319020c04 75
    0x5aa001d4501400d00141c0e801c11020790a0f0340d81100e05944c2c9548940e8a10060480c1020350404a000314400b01c844a20114950f4440c0b02480f41c001610340c3c8043d2100d568114038410481450608004100c060a04034010b43e4000d000c3c1c02814102d5585207012807402c079240f40c0c1e6024129081d4010310406034414485a00021000052410103940b0740001c0d80b0b8035030160034050051900c012080503020000140b240321a000b8100c030b501d416550a16201a41c80074a03031241604055616000c020380c00011344400241580d140c0700350b60305000a91006140c002002039101c1c01a000c0504903050703500507032460703002d22000b8200307100451170f0103001c90354140c01c40f80c8107070700611202c0740e1600e0010542e03044035080300e100e065a90380a80e007940141001c103c4012050311350102105d1f140c4241c3c044000f2211038004544482e6201c41d42c020490045000040070469542c022810f0b40c513180c0c0007100710f4480b2800741e92402d070030ba400d03842c13803035118801120240c0c20014020056180520444 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 816870368 1250 816869118 816869149
    0xa1407050307170606042403030c050d0903050a1518051b04020412020103201603110a0c0608040c0e07090e10030215071e0b0610090f062d05030402 65
    0x1004110142c4441c2d030319000d00603e6a0b000300c5c7e8907040c40c004418600300310b20240c0b00d21200c03070750215202e0800a100305d050b0708082e5050b00c03420006000c051320600024040b0f9401401910191525964965914a0701544503842589a40040407090080101c103402d0600c00d50041200705000f4148001d0003ca1108440c8a50b10500040040c0c0442c1c41004a200782d0910f00041c407800b0704902e038030325020400300107881c00ca00814803280c0510344c803044038900760298846400e512041d00b802a9600034480e0018112070700080104102e9002d8120260450b02c01d000202d54691143d280c0014403100300c820710001000003408000d2908110f40454200807a482030181c00d42c195008240e0800c1d070001500c203d224005400c400340b14401040c0d00d0750106d166404000503026041c000310007030003a140c60b0f10510814100c2c40d012802041500f0403103218400c51000e0741e02d0a034041e10210245c449104061240030300384880706000d500b001d00e000b101904c0c0c075a00e0b0301300b03801402092454440c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 816871618 1250 816870368 816870389
    0x6090a26120d0506092203090806011715060a03060209180a0510050f03060c0a09091103060108070c02150a020c060d0510050105041d04030309060f270b04140a1407050307 75
    0xe118002da40881e00c0503c10010410600542d1b00341e14045a01443d5907010100e203000301c0001050391000264501007008030003003124460300c103034442d0190b0f0140c26100f15038050b81c1140c1c00c2000a405802901703044d20000c0c20140000308640300340030400c0d8116041c0002503554810020503610084461002d0042642c50002243c200400300344e440720040e000350071500002c50740c0b00d08184a030f202240034200d4100300b0322a000b080110b03405550001e442250102c0d15103030004040c1c0c1d118422078142180c00501000c1d000080c0070300c914466201051510850040300c61103025903c2c2c0f88024020003c14210000d802e1a020075007a0301503203690403041c10007400b003008000c41030703001800d10075090004000444603151031800f680105411180103042500b00701296045034580e52022101e400e051806540c03c082500d0f48d02006000704100902111082011802081e252241c1060101c29071040ba155681c4d161070b2240a09803000744806039500c003070f1080c811400c060242900800c5e0a540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 816872868 1250 816871618 816871621
    0x40501020c060904060503030705061012021315120b010f0e07020607180509150301060b0901171f08060a180b010510090306020a050d0b06090a26120d050609 69
    0xd4490a000e5070041c0b1030b078004501d02c140d556456110780001c10b030040c00c4030307510302991a0082e00c0b0300c0205c603070341205114840300252281846504495040e4010103000503560140c130030071300400c10a4040e0030784000c24031021031045625044040c1160045e070911490350302d4440802c0321810160404c048102c0c01a0521000d990009401074202141d424031000e1019000608a03428020758071459211030220140164003000c080241d2044e803040d0000e02840b91245142001b40c450001c0c00c0e40081c54001c40d00c2001c10789a1000c030b030018801e044c030102130804818094004092908090030b80d1700f200d41400051100c511400351016071900ca5508001d5650311480f040410510850340290400070706003200622850601c006107034481011074a8201c1c098000303205400c82e8500e40009498000303c900940340075019a40c5c0800000e08500c0b02030300308640b4051451003a102010300c0400c400100000d05810f121101d502140d8001d203d407281c001142010644e00043c2501e802a0780c0c1a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 816874118 1250 816872868 816872879
    0x150601081540050105190e070210020a0807030c081006110c0d0302030a080f0103082704060e090d030908090f01021203070203070b010909030f0807020709330b2d18100504 75
    0x24201022a809010174900c107503640802a82081003102b8118a95031000030101d04083d0040e001c81d00424240e07a04011a12001500341c2c3c42441c103803890343c90610601820003295100c0c0601200d40240c180a40f034850911001188001002010840168002184c0711098039030055003150320106002d40352849500d5625040350500c20b4070320381618440400c802e84184007020958200d1003071302070b104001c2503a072940d0031204040152942002d42c014124081c01561090088000203900003080324a80300b900410041d8110100c81c00394154000c0003a407421400240018521500040e0081c6540d01401d1030b00e4400128141c0100610394a01507044001c203600000c0d10840603898103201c6642e440311441030345010b40136400345840da403c0220700d80000c8400b05020009109114072000303107002010000311080001d02954980010a1080c1140042e41e071100d03031101004030700598076074004000c03194869030002c070300100f07189049040b2140c5820516001394100302d1074030b0f1807802d280c2480c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 816875368 1250 816874118 816874159
    0x1502010b03030316350f06010e18100806040302030a0216230109080304080a06050a0b03280b010e060f0406060f03020d061502150601081540050105 65
    0x10b10101e0820654510500141030440c224205d1004201200005130403600003014189108640b40c04070340c0703041404903c0c03a50217000412078604004040680b05c400c80f4941d51410240103180890070071141900254a5100303200d114040d5000b035001d0360340d80880c060060f28240112802c4c2d01800c102e10010440c3c142c40480726266040700801442c01c000034100121000c0b00340d034204042c24000003800140b0f100001481a00f0988208030600031643c403c1c2490046900f030b00d0b42141c26030400c1c181e40d0715200e0206d0001c5001c002c1c00350903800c4069075440e04031554000340c0110345002035040510149180c00341864000c480210340501019080c00802440d101481410b00241600030400b880110855004940602082c0010040303070a0b48410096580d640440d5100c81203c0c20750100d00350f5442071011a200d2a58002c58140d841004d0091040c4900001e10b41302c0020020310069804a03d061000c1c0c000c440c03420383c209181c1007442c0101c1c08403101a4801c512074000e800048800d003121 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 816876618 1250 816875368 816875401
    0x100210061a180409060e010b19080706052b051f03080d150306110a110106050a05060705010f090803100602072d0b03041b08063d1502010b030303 64
    0x8002c01000c000241c003c01c02501044d940280340da42851220a21030307a05600c8a02d500302d04995499208080303001c1c043e4201101e00072210650006017045c40314034091002400400209044c104005d4000300f00320010088952440f400315807100240805580d240c8500194000052000c5035800d1556075514001e20580c0000b0001c9520790f40c400000c20030b015150001550800f80074405500302d811802e02a500004c46003010516045000c45520414469401070f20303006031203001c01c0c078101400c10107241c0001e0b8040b46c556403509080c014904543c004c1154891151200617100e0030460705040802c0d10680000e800c6602040b800c024401c025095a0211004004540c1341804140b041d448200d1894104106014000043c041003260130305181d100e4244401c40403196548840c0c0541c1c55036030030f8421010b480c840e1a11010a05000003112050300c13210f40c035003d5a18031140384580481d4940c0d004025085010040780391282d028003990400c12002c5014500d186040c100c0010360300751 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 816877868 1250 816876618 816876637
    0x6030b060306100327060c0809160302090a0b130509011b170c041509090b1002030a2a06020306090601030c0f050c031209010903110c0a030803090c100210061a 70
    0x111082d0030741000c2c0c2c040300c0f401c40f4101c5c40550804480883d0401e50050300810718110005002c140000b00c41580102c0e100700c5d8500600d01c4004001d18540070004502c04c050000c81400346d0740c401488096882e1815603030083c900c030001269520740008160308407501c502c01464400300110382e2400f41640584c8020410f254821400a50340710498a25080d006640008241c400c036000d10005450300542c4400c1218126a0103000c9403403440288000e12692a40440c00350380280480f1050328056900c524040c907010480c0b4280e0f0501c0961400035140051056a486e9400001e200c018141000c900b41d010200f0300b82840f0201c0503a0f0010440f03800301c48075100700f05000c14244000102841290404c204040c41d28206042c0704520034000c11000d6802c80100702c102d00b8800007030f80c1c04100642c0c42000200490080c7c3c1c65070302c1d01d0b41103600c010002000e40c022400f003a14251355900803034025200690042c1204154031100d4030803111540c004a00c5c0c14a8404150000c501c0101101c0403001c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 816879118 1250 816877868 816877871
    0x11090a0830070312020904020408060417040b090907030e10090b15092e060f0f09060f050c0c03030301091401060c120309021f050d0b0a030804030b0712050a020406030b0603061003 79
    0x4c01103079160000d000b800e02ca02d51080c000200000c0a140014805001d1030048841983c2c3c0701c3c0b0380c00c1c0202144694840c0e0807844100740f225a076540750002c00658004120304000c241a425038a4881c10020308a402e4030b00b103541c40c280c480038060048542c5a20929148964602944e00000600104c000510300803080e400403560350b003006044488440558140d60107c1c55440c2c8a06000c0c102402d030b0b0f1001400900c0f0a03c1030745465200c0e81144c01260410340310024200445d031001c0f22950300c96101c01c409440f90b641841c0158034200021030083c207520000041084c104440380c1018401a4840000c0202141d005408100106d0742051085460b040001d0200e805201142848510088160000e400342120b140d000d0b81080041001c03c03850719007040b040790503100300600002c0500015082305000d10013880040c100080c095003040003807c103502d6030f001420041c020f031002110002d51264011500704072142d0140230300c1003a4042190814294503090010680c0c0002901c082810035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 816880368 1250 816879118 816879137
    0x5031b1603080918040c1805100e100e0f01060306061706091003050109050607030c0207030b06041104120c030c1401051204080903011a030f030306090a11090a08300703 74
    0x35904c1d103a03404c0541550b41c851012914082c01c2400d085d80052142c0d801800b880c4d02402401121803041c54421074004000c01c600900b42151260750351f00007400c9036500021458081140141694418400c00c0000301c1540306604058004040d554164404c0c010b200030f180c035115580608020240d03000b00c065030100d04d0340e59180e500c1d03140e08209600c0540340d54a40038000092140100e20140700f0451900d01340461104034104a90ba02820311000e040300c88090081105480c1640044500207160b0302818107254680c41010141d91540382c0454000c014400d08004025802c65044010704880e400000c1c0448542c0000c0c215100d83c07030070a40e500000c0d10000d0100088081501d800200c0903008000807406c41c0441d4155140c49500548240705001c944115030100004403031141c8000b60042c0920740751240e0400c098103400d080b2407401c54040c081880c05480360850355000f0f00c0590006e025030b20200b0786400c44200401d209040d0203411403038001c0151850011240200c1d814507145001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 816881618 1250 816880368 816880387
    0x70504091a06062106090921030901090c0b0403060e0616121e06080601091a06031003052d0604080f07110a261b010819060305031b160308 61
    0x182e202d0b070315110b1070801902085094080036811090b1040c84240d4512000ba00c1f0b10120340d03500c0c4c4d110081214450b00c00c503c040316819030312000c0c6800021103400483c142245540c5d4440d540041d03004041ca52802003002c00600c070300345c0a5190f00200407005800c07039060600344c00410031100242402440308190fa03d4240d51040c2d2700808920f0340401c0002200c40d0150b080201820051264420f203105890006ca1048120702c0741c4001c0000c10454101c48503003603800c0c020603400c0140220603110400c50000003040b020b00c507081a480d401d4021481d0041030080c80031084c860740150003c181c2c401410400011131000440b510410a40c1120b51901282d00e00ba080000d0042c0459400440251001688545200401000343c2c407018426072021f14289442d90350302005d81d0350306505100d010310b4440c254050945107030008a10130403076024500401c000d600303075103c1d039100301e465038000101d809020030001c800d40f10008509000d001c1c411403084200a05071001d01020b0810640015066071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 816882868 1250 816881618 816881629
    0x10f0807021501090c09050a0e060f06120a090b010914010519080a050a0218041511040e1501110304050307030b0c09030703030801050f06070b07201e070504091a06 72
    0x300c00c16107641d121a90384504e00b030405041100b015101083e035200001c80c032441c01215a5054034864114030001765240c0082169481620000d0354106108010550300e032410a00c80507c11101024081010840c903c0c01c200703207100c140e0100151501e01000d90b511003070a001d845045070412601310400200b200c1402031205a580d0050a06121340d280820812401086c02a2114001c0360007841d1001c424a10328080b81d02114000c01c00c030310444a1980650003a40814213080b41d265a8a04041c0c440543d1010030b00c0680b2103005090246030f0446e042c1d0303406000c0f00582d807400809917080c2032034a030101c0c1d514a034902000f040c44981d03000140500d603040080e00c4000c00c0c014219181d19660f41005841800c00b03000d0907000340d48103180300845040c40d40854484e940d014604c8985035480d8035049600c4040605225640e60a024003200b542c0c0c002c0080048442c1d9400c50003204035000326066141c00c401b80d1085000d2030822940760049426462a4204016440c45203840c80c2c3c1d80000041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 816884118 1250 816882868 816882883
    0x605031602032a0d02010e0307330b040b04020412110301090516080f0607090311010c02041d0c0f0105070f0305090402180f040e21040302030a12140405010f080702 72
    0x2c0c030140400f582030889140005803124110000e00c00c0c2c0b1202c3c020384d2400c0b401d80d6070844401d0f10f190f004000780800140d480400e200d00c125411617010002280d03401d0213000c0c0c0b0712005c1041c8542e80f030302500200b910340f034420300d00943c200b150210310f0715103040c80500800d100c005e4041e000c82c41451454800d41c07401c0d04a85085075104007552101c0000304a2010501c5160150314168821a40010500100000d56501034802510340418150ad5aa1020501300c80d140202e410000407006840c0103803118040c1a840c1c0c5103503c00e01440c0d40b01c601c1524034100c40e0b151030610450618030051440d076041021140055044041030041c002c0c0c1d07040039112441802a4250400c1c80080c0d41c3d900705143c64407401045004a5103401100b500b4000c02c41a076001c00d0041c54a500514503450440780b054041900083e000a0030b981000d5032a00040d0a0040790082540c02022404c40d01c8001e0303601c10891106c507646030007200d084c942810002030403055502002824402d44134082000e0900802400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 816885368 1250 816884118 816884137
    0x3020c2d15030a02031008070311060304050118050f0d09030c050f03190c2112110a080d06030b0c0301030809100c06052a2104020d02190f0b04060503160203 69
    0x580d500e0400300c0e401d0f0000c1d13200b190b2803052030b01103001c0454000303000705600045a400510924101080100300225548043e10440d47e0350b45c0c030940c0c0f04128800001d08800c090040c0d028042d203000d0b05480c14140750900400342d081104941c0148006480c107110203041d140113590b44511441642c4c08207281c4540100601021088083c8141c10020303440741e01401c1d0b514043e40c8410707104d600c5000c14484d52441c0c10062880402c0e0540921ba180700d50842200da5040c4070480f00e03614410744507002d00380c1c803640040b04215242d400900922214054964201b107441140d40c4c51989503031a0b020300c9000307413001d080c0300d00c4880b114095018400c900e00e184442d0001c00802513400d0440d0034460032128940b504400404020402045000600945108502102d04503c1080386a113a81d50728650060040385e001005d010f01e100542c031810034400407859000d04031100d0504140078040c0100300e6030b011251101c3c00300401c0c800a90301030162600110403070005c54038880c038500705078110300401c5a00c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 816886618 1250 816885368 816885409
    0xe100c020a050a0b1006080c090d030e060408030315090415020c0313080a03030501150905040e1908030f06040216062f0a171b031806010e0403020c2d 66
    0x10344140189135811901640100041c0049241e44040581b100f100445030300c402010140100082400e00841683e107141c404d180c820043d88074a00043d1150f0400e4100c0c1185034008410402542046204034021032002c071118249403030a55521492916034184074001d0540200d80341c12810020810760700d04ca800b08821040c0303a034a5860141e9141c504110030380c0000c8c14074000241d20683e0f21440c4200c19450340e0307908a52070400302800301419418007d03030150f01c94007640d00400b18141c58495001489010020b1b5a810611039034090070300041d140b60b106a10401000205000c2e1209400103a50701c0301010030304a00340b401116407034685d494081d140080c0d680b0380f1040d0030540c500404111003c0d0325a04040301055001c2100d600048a04010000100580d5800c85100d1400756601100703c20b0803501c4141d0b408801410098203900242202224a051004154041c0301c900102d4000707442222903010b400e040c1a0319101d03c02c440040742c281d1181c82d610540c036a00e0803407083c0e0700860300c0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 816887868 1250 816886618 816886633
    0xc100606050a031a130e070b030c09030d080903070b07021009061e05040f020f060c01020703020d260f070903020603040f06060807180513050a0f0c0602010e100c020a05 74
    0x1805030442d030220342500700103441c1503003058510200e012218032058024141c0001d0300d01c403400c000002c060051a01e500c2d8400c4520000b001c041410047d8400c0d0101741046442d00000400d1519181a401c0e00805000e404d00800c41000e00000c10b450b04141c218084580030348504a082c1d05103108000d00d6502542485898018892580c20042200b0740c2180c400d04101c00c954600d41c02c40340103490060140f0f80600c0e40c9009840e000407180180b0303c00800041ca0034413601003d80c220303442140110003580107820b4400143e03800ca4180c2881c0290003542074110049054030f85111400186200301d8a5001c2e8042100c480c842d520410107994007820565481c1843c1c104030441041ea100f080b603001d41080d001040c6003034041211000c840707100511860084400c3c0c91403026003c010030b0520f00848080b603141c0416010411001700502610b2150354815036130624070304031012900000b0940e0304003845003c1d00c07500060620b0850380141d80c0052504801d207000c07410700041e036601070041e204264 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 816889118 1250 816887868 816887879
    0xc060908030709180c020a1103120d1e1109100210091a0105011b06020703120c0305090c041512170a110706031a01081f06050903010b0a0503060402060c1006 69
    0x18260700513560300e8194240802d483c0000001503885103181c81e40141c010300c65031400100c4819203a20202c2008081e40c07400302d05076070100350700d812174403a40040d680c0390030b9078031012070882c0046200880b4400090000c1c01201c2d41e0900940309440f007444c00351501d403505141c0d05100b40020102e5158446003803240b03450358203010004442000c1080d1448201c0c6000140a6002e2802d0380c1c0e824420b550001c1c10340c10180c1b01d00c40290030944064043c01085810403841280c01c4c41841d00c001c2681c3c03000140d6090000d8a0751900ca181c0008a0140d4588164034041d076110080080c1129409803180642644070f1400c0a08a80175a50070700e110744d804502c0034445030300f0180e071a0041941e507045442c0a940d942d411002e1b600c01e03103c1e101d03100056005982003548500e02080d0b1045803405018415411843d41d0440f072115a40400f00040c400f1807145682d24081c018034107480001c03507003565000d00380b400190b241c04018000a202c1c1000240c51108d10b00140500d1621841c91351007080040d9444 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 816890368 1250 816889118 816889127
    0xe010507230712080a020904060f0801050601030902090a0e1912081014010c03020c090906011a041409071707050d050906192409020c12190c0609080307 67
    0x510765030724842120050400c84084000352402075410004100802801ca40192100c202c040c00402c8516000c01007400f15444038003e101c010f00b19803450483d941c0c0b80c80c03034240c00c6030070190595042508200240c03003d42e40300040c00b60008250b00c1d0002e1000c04c0c080032a071800460500d00c4903210b00b132456a90038081c0c440c40c20b04000d00b8580301c55a0701d503121042d004607a003845c05410341d0328010b075a4501349548250403a0b16228880e004803100845000005050050200c840e0003940d8000c1d0010711440c070807007440c00d1004000a03001420542426010095941a112514080d100d040001142c80780324084007800000324005240c030750700303000100900962104640007162030608010801c2c180d400201c443c40360a21594003e00d50042c016410094041001404059081d40780705014604403103051000504021310f0069450384194139541c10060001214515080281712a4800e94050380749590100b0807440c164591200130304d800d2004000460f0050300314400401040f50303c9802 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 816891618 1250 816890368 816890387
    0x17010c0234030804330e0a030b090c1201020a1e0513030c08061e04030c020427020307060c030c06050408071406060a141507050709110a09150504030b04060e010507 72
    0x50890390b041035003000790318644504144070b4403c2d8807951031042c48040e4411b440601072118024441602140c0c0c07910750036200b02e001c0e210480ca58020301e0318030355646045104001d404294030025420720342c1500025040c0701215050404000c01403908099040c0b151040740c5803039805d0350005a48648a0903c01d01c250b9083c003440a117442000040303454130107125014502025808660704250342c0301e60b0308413481888c10108136042900d030001103018824a04442840d003c0c0c4a1003045419814010586010707441d9010070f0520100c00d00d240042030f032020201c2c030b40c20f400c10004602d035101c500c0c00e80400e01c0b800303001428010b002041c0b80901040841c986000314012150b201e440b0744c83c1c1e410040d200008090503a84050f41c1800809005030f4403001d40304140c000e10035107400350390f103d0050040d076550f0000c14104c1140044d48135071040d0818080006884158030305428040c2c0808050150711550001070550410b14001074108483d0307030803a0302d200820400034406070900c9c079405000d4280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 816892868 1250 816891618 816891629
    0xb250f0b07031104060f030b0931050303010506070f020303070b061201060501020d030c0912141e0a060e01020706060b041712071101140a080117010c0234030804 71
    0x2000d001080304603100b8001e01101c4600e0704522880c2500d40081900c03c01111030a090a240c0c49040c400101d0b40d50400d9144039244802d0070301c101303851031140e410030044007180c401c03407100400f0844030102c1c0000003074a042d0f810a840325a5100380c1401c1c103203000f400d888c10083d0725110004840080181c4c5403400390140f5800d0700c1007040200240c9881d42a01d90f1401031a005034004030711003044501c80e40120410340b2040c28009816500c0e24200134034004904407d54040301c03080c07411070124004000464200c00c14a400c1c8407003000c0e50740042e0b00d404084c44041c0400351601074040c0424400c2d0304a83c0a540c0c0306104000711640d07150503105942152003001c00d0301c14140004c83d02c010002c124050042d040c4441d42c0c0c03034203c542da24603c2c02070005c08070340d0410070b50a6070382c1e01c2c03191000000c144004040d100c0341d10540c500416951280002161001164149100003141a400080041041c904101d4020f8100c0c6d41c8084404401590b1041201c0072070860400820702140718010006da0b41c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 816894118 1250 816892868 816892883
    0x20301090b0c19020a050c0906120109031805010f020604060506150301091a03070807050607060e15041103030f162d110a06020c1311040603090b0f04030c0b13020d23070b040b250f 79
    0xfc0d42c0708015a00300400001102c0540c10580000e80041d01e958009a40800b00404120003540c6101c00aa035582090b048802350b15984c1b110400560003941d125441c12204900803e80107007030450301c6441b81b80314807880f8040c0c480400c4c1c3d0001c01401b5008840007800460441c1d00c440d0942c0809900c1d08400d86080e6a444030000000e2000d05000c0121981c3d0124030700507500e02480d0f14003050145c0008441030340c0e05003c4022980b160300440f2021450b8030301e84141140301416504011201c071400380c420302d104014220013085826004581420380d034108584414600e5140c00c400c00c0580040b80c142c6003031407030016000ca9510f401d40d00002c0114041c3c801810241d0311000d02d03551070702d030a99014020580c91401c2000203054103451a86c042c0c0b0503000d07950b490300c0301d41c0499500a04940110b03010810080e03203100855100c14000640ca030148010183c4601d81004034550740704030300071002402000546801101c0c8101092141c0e00582081150442800c1c140340e8100040e11004840b440c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 816895368 1250 816894118 816894167
    0x13030803091f0c170903090d080405040504030f031103160c0c0f060f090f0803030118021309020304050c04060302060901050c0a1a0405070605070305040909020301090b0c19020a050c090612010903 86
    0x2132400004079205101c990000c1d03242144000403c5528807500100b1241d82030100300c00324540d100c07400b035a8040c910070344840c0f4200103002c5002c0c1c280c4c1d40e6100b0600241c0b17010b000300714624a2040e120031801c14142490b0440d50400d040c2100d480c40745410480d021140e02c0380c00141c1d2030307202010545080c200da6440c552180c80d01c00107a12030005120f6580030703500a10040c4070301d0f69806080650b8110308400140343c20010251089405442d52241c01d0041d400701c01c00003880000d00c01c110f00b02000311001c0003c18190740c009101c40c0903142055042020108001ca6040703400c000300c0015540010151024081c196207840c8480002c54040300d582c029100005517207030140b401c0da000690f00d52180e5051a08002e40c4a000303000d203403001d0743e0540d01e0b925000007088031084024001c1e41443d065940c2e0b40312000d10342852070301a441e0003085600c9444080d01242c0081005048000d04032080c8807151540070002d450215170ba91032001c2035103402d11810070144c1140b20390001f140350781038130a00b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 816896618 1250 816895368 816895397
    0x20d030e06011202100203070b1f090c080415060503030c0f0127240203071d011d090601030615090e06100f0e1f0903150213030803091f0c 61
    0x2180340a100b0f445050b40c8a128a900611303018102c0f0510040b6841240c2c18000c0b0368a800710340d00c030f00303a4005000030000058800d810702d0300c80301c050282038545428409540a060010400b91000744042c000805c0341800040c030428507000b5a00500c0001c0031692121a000d10b955110fa164074841c10b1139600c3d02183c103207209400400c070300d1003130443d5601c02010f00840e03c40e027588071f000b404103080c50002a0340d5085000e00500c0550302a100503580d205038601d100718030142e0155400c12641c148016042040d40c900b00707190340d990549609552911707250b03c5000040e006091550030402c0c5204445424031143c541c002e940008580c1507003034000d003540b240ca0502814400120030030000403102c80c03a00354072900450480040c01d070064a1000780803003c0303101d001105004c18140c0e0004000480030010f001d00e00c0d0000e000f000700700710300314a802848100003103803580d41d1100601918000c80091811707481405100801800b50b03441c2042d1101c0505c01303030000c000c8040d0940204e254002d00a09 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 816897868 1250 816896618 816896623
    0x302060f09010b1008100e010308030f010806060303070215040b030c0c07050d022b0209130302011401211502071a070e0a0611030409060e07080c070302030a030507030b040c020d030e 80
    0x901c14080c10b0b128413180200c10841e00040d00801c0e65101052108000500c1d411601c02140250b004000b0076440e8101981002c1035558182e20140442d48040c1c148401c654020080b01c110a5045030026404010030212804c5c501480d40f2404034400e0201c1000f144000c20701c01042400c8070320054551260700c0b481041905800401d010707401c00780c0c0c402c039050540000070007150003005100b00391840d201940d000070840c85088415591201c2c036050003504140e024001e00300804082c00303034a40590306000600d03e443c4500360288000101119548040c040451613124942c616550195a0ba02060a102000032108540100c0145107140003d422a2040c400e050b20400f005080010f0340e80740101c01c43c1c4405451070320000c2070000b00300c0010031503924420b0b0030042c601d02c2103161403445c04400c0601542c00051554201200402080001960100031200d4120b02410005803644480500328003c0c500c808071160080d207000d040351721007600014504450b11403580d00303100120303a05000d0764 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 816899118 1250 816897868 816897881
    0x1c050c01050918010807030c09110702091503010903031b02060f060907111605011e091a12090c15120406050703061d04050d03060e0105120a0b181009030503060f030f0a0302060f0901 80
    0x522031180bc1c01b5100061502034000c90f0017520401084150176800c80000c0e0861340c00d003200f100420750b42c014500015a00c0c8085201ca0003550010303116a29183d4958a2070300f40007410075100703500d040b0001c0e1800d030140c100030240c42c03041d00441d8006000c40d10901c13803210042c0640d5002c070b00e20540d07c0a15a00710180d1003000d004507503400078414540809010f05121000c0c1c26108510240990741030380c105101141d10070301c60440108044511402401294040d8a1100c5400e0030104240401d04a91f2040c40b50050b500040000310b690f0b0b070740811001880c1030340100310383c10310502c40f004040c461840ca05004031300910584900344102e0300c0a070200c81c403a10840190300c01103001048a0301e0200c41c01103006a0700b009590350404999503e410396141207074800d01458030910380b94000c6100308040c1000008804040142c1d00031a00d001c0c2c51400010300302882400448010f0300c4548082c44142d001825400880c0c96030020340c6000394803075a01700d4444500135460400202039850501895 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 816900368 1250 816899118 816899141
    0x80609101b0522150903021306120308060307030c0b0c070b04051302030901180b010f0503190209190516030f02070f080304030e150403021c050c01050918010807030c09 74
    0x85240505425143c2052409101c408400740d14a100000301881c100c0d08451030f0000c103689201d00182103204008440304001480c042042c0b4004050004001810313001e540356401d0308008400c1e558040000e031030082d10f40c00060400d9028080011410000000381c01c4030b14220701594000d42e2100204503840c040e9102c0c042d0b001c505a600c1001e8001c1e42d03401507411042400000c034210707c1c2c510b00780000055014003241d44611501c01000354000c42041440949000c4014101059042d8a0b40001c240c0300c1402900c174200c4080420014041301c00751070841c4035031010602c041e01c3c01c10310012044078030035164004030781441c8a4000d01705041c4200c0b044154010b10b564050041c0752104900c4e9000108100d09004000c000a042036071582c0d030340203040307184180644e61746055105008607801700000d11058403203e0510200000d0380403803003000410080c42c2080d22200c2c0c0c140011110311b1103112203071304011400c0002c0b4180001240a1059900950241040716560700510701120303e0040c46 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 816901618 1250 816900368 816900377
    0xb0a0b070c080304080c0a0e01060503040206090f040507110c0d0c1a0c0109050a060c050c0c060a030b0d050708120309030a03020307091e0603050916120804080609101b 74
    0x502095118801400503103006481c0349030025112400b103032455100e604401c0490780300d01151101c41c0b40090a55001d02000800d2009652403c00003030540c2c080500001e220b1071010a612403a5220055115a021030040c41803109040ca424084c000480000c5180202d004e8034106041905194016106241c2c3c450b40e8818680e18101c9410480d98941d100c010715010200000d4020342400d000d40250503001d01d000d030031211702070702d0f015046941c9103940300103114080c42003004001e800314140441d40020341740240d544400e02070440003002c40c21007161340500c05504680078020000360600940e4a080d00b1100b0000b5101300883c0d40340000c0b140224980c0c001c01c00c001035079200c0e8002d1078005101d07003014568a5202c105c140070144540200c411005c50040702001559894050690400c0e01d80018000a001354440080c0d00074081c0a4201c60380e802c1c080d184204180202110000d18003482900c2c514144591410740302c609404030780140394102140d403050190317401c00030300e15203145448 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 816902868 1250 816901618 816901639
    0x5150906091302060c010f1823030d0f0504110402161101090e15031605030712020d0b070f11030909040b090f0d0905190f030f1e0f05100b 61
    0x1c21072001c1004012824806501d2402001070303d401c0d01420016150200215800c521701c4004c204403034014031240c034441000c9010740301003643c904c0a14005000080621029844004000d02d10721030b080b070308000d06141010405040c1c07150390001d409140302c1d420342c0481c0040a070800040e030040e1196650b80410301e40030800055071880d10131140d124107041240001c2c1e80d038051001c41203c111000d008880140003c0e51580c0390900050080d2944480c1010b8900d080401007648c0310f0f07080c0920f00d50415001010000d6541c2c1001615440780c0c0400104230b9840d00201c01000140103450040c080f0303000c015605000340c4080b003541c041c020b000c0d150703452940c1e858803000b410300400303400041700340900c7d03034110008441408450340c40046622131600d598500010300000d103007040303c2c8642d00e0100d0385040c080b0301805000039040305c0c4c010090001e2240c0c1410842c1f40700b056240e00741d845c24a002ca1100411154048a4103580c2c0664180c80d80f80d280041c0361010b0f6007081d980e9a40c070518028 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 816904118 1250 816902868 816902881
    0x5010f05061b061e1605180301020403050d0216060306150309060f09122709020f0c10050417090306011e08010510170d050a0f050c010f090501051509 66
    0xd44040c80b0030215200b6202510701d00d203800c2450a80f14040d45081010f0800c1c403483c03000284e6600020020982e481000c2903040007011801a0075145025007a402c0345040c49950940607503001c0e5400006032594010900ca0103942c1b1904480c103400c0469281d000061020701030710500080711480d1041191040c1060303000c8004125204084070a95a2488080190384043c81000c10a0b0301c2500d06d00044102c8590180002d82c08008200103440d00401d4041610603c000c0c02e41140c400000250301c580d240351030340340140100c001224441c490710110a8000c8065000075000794042c0e040141c1c1e125041d0b03107020051040030251500344d4024401001004c4844482802d55000b21040d40810303602c81d41001d080d5002520a042d840440d42401c0c494809006154042600d03590002c000a4a5005010740240078500005c42072150f017213400194a80900101c2c1d80c072542000c000c00c1035012103100100104034028007502c141d880e00e000112014007240c40050300c544000d1202e40c0d140d8800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 816905368 1250 816904118 816904129
    0xf090a0b060d14010b090109020a0903020d0f0f081909050303180a0503030406020604050633010302040f08030a03110a020c1302040f08100c030b09070f020f24060405010f05 76
    0x984420740281e036945401020030000050700308103c400800108450741100c0801180c2e20f410703080708403010310400c107240381070307400c0302640040f643e0590340503030b40c40701c0d0b400c04010030b45c403101e0060f2003403140c52003100070400d0840041c49a844036000c04441901402c0b030440740b0000d41d02a140c0c00da4802c205080c2c2004080f84040c80c3e001c4c004015900098551001c07a041d60095800342000d0380c040c2041c0420004107002c00d55002080000401120103c0040301d4441000d85416181070b1400303400c180e0590344240c04640141a9041c000d032605503076004c8003a5603a21407440c81c0700291420807400c150114480c101d0f40d648066a0003050240c803010200075121601019031a03015034200720014840b5a6069500300400e6200007502303960080080c0c002c20f96150b82c0e0448201031610089001035650300e882160800d41c98589521200c0224000f40e1420301b640540c80d00c1d03481500070b1203941e020301298001060b214030a85602c03d85a040c244002d90f10203014890308451402814891800d02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 816906474 1106 816905368 816905371
    0x20301050c160210020c0603131b0b030601030e071a07020a09020a1b050f0105010e1b1e130b0409060311030c0f04020904060b041d0f090a0b 62
    0x3051410381c003906010002403044d410805034504952007005202c0c0c80c4040a04010369034205825840300642c2c0904d011136a40c1030030018601c104440c5003080c412520075811031760454807501c005401401c01c0802d55881881b802d00c0c0003d04454943c140707a0a0030f202005142c0d1060a4010300080401c16080071381c0c210700401280b84800da00a01c0146001c1000c207604100e2002850030703038280741c400320603610a0342c2400300100b9003048155402e402060309050199408545140d40f07100c074058040d21590540040b61842800d45000006207604910003041d003041c0c43d21180d030300c10290086d800030800070b5030b00c690a01c1004420110010320310000c40040c02a24041c8001130140e0300084101d50207a500414102d1140d2070701d8100034040c03c0d070325801700d46441e21040c0c24120311100840080c151409130010800c440c164440140c091074035000030382103661541d217421812400 = true := by decide +kernel

theorem cover : BRFrame.Cov 816726618 816906474 := by
  have h0 := BRFrame.cov_init 816726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 816726618 ≤ n) (h2 : n < 816906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
