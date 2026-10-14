-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1761
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:34:59.461968+00:00
-- url     : https://prove2.me/submissions/5a053111-d881-47e9-b580-3b8c75cf1a24

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 316546762 ≤ n < 316726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 316548012 1250 316546762 316546801
    0x3020906010216090515030f031c0b060706060302030d30020403051507020706030e1005060a0f0b0306040e1c050a031d16050103111806071a04060b090f 67
    0x1101c034082c0c0d081c4802100c10b507054100003103540e2a20240140396603814030300c1010b01c6d0100c018010101d001d101c0295280689a280401c00009074504201d1118a07804600458801707094165503a9440c01d101c00a00000d120881c0284112540b010100d4890b030440ca50600b0080d0701b540c01c020310b102100089000041e180c030125a400c001c0040004c03410015001380001140560807145440080682050020b91180041c0b60804039944000d0f040400d1b043c0c16000303c02000038558a075100800c031040c02a03001281c400102c00e9004c07502000e56400746102d04c000b15414010044048100d0303450300c0d1000341d0004100b0500e00d0006446000701c0182610b03040515001944001400311000480c003e8116aa4550031a4000c00c00c1e003d0a0400800030b000282000d0200d12050503401c005440f8a080e02c02c030104203090000b4141e0b544c101284c2c2c8150b08018510302c00c803840c9040914402c02a9401c6806602d0523560100c42d00700b6480580c030501200103149601c3c2d95514074115003010189 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 316549262 1250 316548012 316548017
    0x5150d11100801031205180603070c05060c09120109030905011214010b04081c05030114010c050106030b06090901060b0702060307110607020708150103150b0d08040305100c050a090302090601 84
    0x1411034400c1d1103074242034191074941c0d510b2004552550400c07450100c8090700140030080104070450700b40b41100e0000422442c262882540ca40c0c5041c401c4400d680c00240c000c000d8060a0288510000c803880984903100007103071401d0014251030042130803203608003c0200071074407a080030001503004440c0040c80b80740f0202c0206100300403603440203030b46100360048040b02601082c2405600410003503845410255030724900c4403240000050140d000c14842d011803c2d00c80c0c41e0180043c4d1044148012003540b0000a100290b00c1e03251140e0000c03401c40d40140190110700000d501d001050083c0000c40f119654080c1c13410943c0c0c0c082c482d543c2c0c40280766100340000f0350703440710b40000100300b918170900d0540d000d421002e007042090350030800003502c00204001030034010300201300b030303e41d0340a801150304000050104078400801c502c55101c49014000c01000b003000001d0100c04516040030700c5901404000380c1011030000d030760b103010b100c58201c0000d480035020700040c180903010726000365050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 316550512 1250 316549262 316549283
    0xc0f040b0120010207060e15010312090305030c0304060212040e0a1112070c03020615130509011812030c09061d0111120904060b2706090a0b090f0405150d 68
    0x5900c00034101c00590342d200c0d503a6002902e1014040d0745c1c0f21f1141510080c802501c010346a200d00d41c1c06031030301030001504644c0300004000d40640220390b2840210ba015042e40e40b2a4601c0480c03903140d0300a0300c543d0016001e83c0d601000d0300e210820894060360002e0583c1101900ca203075030000140161940747c18000030401045e045008180c2c03080c4d101d0f1019540b4910a8401441c0080c01c00a000d00134000340c40261001e94000e40e11048002d621300058000017942d030b42d551010324090031032840c004240c00c1b4100c10070300c10700201c10071091030200c941c2c401340300044100d1f0f41100d1500207807142100290104040d0644052900f40e040c880e004140340100248060200c25418064005452540c00000042c0441c61382814040c0000402c0c100d1200303400c09480490000c2403080c81403014409401010203000702c1ea55440c16074103c400007408849900d500e48002030102e40c01320705018404d031101c01d01c00c5180d28050089922640030f24065400e186011820f0140c50000d0080440e020400c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 316551762 1250 316550512 316550537
    0x20901050d080d090f0f060b011404050f0d021807050a02010c0206220f150b0f03030a050a0f03060e040c031103120a26091f0c0207140607050106080d0207080c0f040b01 74
    0x20f00b00c0c0c46d400d4902034140080c1c6031244000261092940c14403c00408509100400056481194107a03041c1016542e07543c403910144001240741c0910083c0503400f41555060200082e4440040c00002c845500204040c00401e2420390366080c046071580520706040c00d1809140d45100e140e46603d42c03084d4005043e814540c1e0341c914482040f4004614101e5079041200c0c0c05240c00c2006000c071807003d4001d54038040c0c600000400521641405405001d841642c172035100d8400d600010080000030856032041c1400d240404c07003180d0358407040d07940c0075200c08aa030745441d02048114103000300c495500e19010f030800703003503409003440750700b60705416004030000c207003250605510703840361002102a01403c050300e0840d8583c2c543c034a0b0448042c0f842c03c40500c111640000305007080e1241c40002250411021002809074851400020041c0d4244031b0000390326a80040c010b00711808540a40310250f8407858001d50b00e000e40c42003690701401031000c00125082a5103d44664a4185000703500e9801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 316553012 1250 316551762 316551773
    0x717071401050c030601091a160c080a06050a06060f090e150901090e060c040308070611090607030c050715080117120f07110f0d02130f0606030504020901050d080d090f 74
    0x600300d8160f00303c21000801c01c040756030b0101d05080075050036000c6000d00d1110070b174107104502903403502044004d101c800a10510400e200c0d0035000786403090446082c0d084615110024003415505d00c1c144904200c40850030a024042c6852140b1242ea02c6820081c90b00315200703600e01000d0039485c0e0a008051070f405503500c4440030180604184a0007140004440c00c81614000c401041980c01d0301040c0414000102408221204540c02ca18080752004c2544001c41d01403003220750041d1f1200c00002c81c1001c0640140c4000c40090144094075001565140c1400744400488001000507448a0040c40b0301f2080604c0c00c00380b00302d40011103e041c0c40c00800c6820070792000c000c60024803c0482d00d00c0c1000300001c0308c007641c490152090711070ba85924000c5900400c843d04000c1c440d50380c2503c1c00320b5030f04169210040d143c410b04018440302c2d0756460003400404080e134080e4065444a000440e050130174004070106140c0c801801850940341c0c2030103000500e034200080b600000030911b00c002149 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 316554262 1250 316553012 316553021
    0x80309040f200310090203010e04060b0402251b08030909090f07181b2a150603020405150a030b040c030609030f030e010c0906120608030a030204060f050717071401 72
    0x10b0154040c41d6039051250144030015156801550510b004000500010200d08206034000390b10000c0030592035070210008010340200d00d20500c40742000c000c20f54a01600745007491859005000010b40e080e2031004603401a4200c1c0a1055070303510400002c02a410f01c10346042e40100f10009441a1002103000b00d810720704a40d000a180390803041c0c824000c508140300d03076a9280342508503551580038401e40541511180031111040300180001280d15100c11014540300c00d0303200e00c10301002c100310301d1810b0042c5440e0000ba8080c500d00350006801155000c0341c0790f410100105802c004a1440d5980b10200f80001c0040380c0a03804c00d81c000000a900c0d000c0c603c03080c0c4c480d0302c6126081c500860f004088940070700c0b0700e038510382c18020f90b640351580049800d8281d400610301003103290070310009000608160740c0080054400041c00c40d541d40c1d4545d0251050300c0c075a6981560440419800f1034003405070001c00381421b40e00e000f41c400840e03144001810081c0c8290460200c04980c091160300b1117 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 316555512 1250 316554262 316554311
    0x61606020909070519090806061e09072001051b03060109080307051507020c01090306270b16080f07050307030902030d081b040303120903110307050a02150301080309040f 75
    0x500108405032a0280101d0405c4408601e203400e000891030036200c00c2c2d40301400b42a00c0c1c090703207070101c645040070b500000c45940303517401401c600010300380048020020314072440d0380040744d41c0d040303091403600d10103010300e5006119400c0810221510030030800720341d80c80642001d0510420344e0000411150520103404024010405020192417412125020000040c140c8007190406060b03200c0c60b80e001403100d002c1d642c01900008408082d4003080403650204403008085035107c00c107000c20400c500040718451129100621506200c0d000160340b820015115010500c52940010f20050311410145034406414035001c0f030346040c1e5070082411b000c42e0360301c00c0f0001030500e001c1000d540100500d95000d80c0140070079614040c41d6483c000e2120380c0500c204002c1945404041e01070511134007036002040310304020340b6a00d0840380303055555a412582c0c124014030700c0b402406030110a00081d603049603800c001461800d454001004014141d80d170300d64019a03610342080360b100c2608940c81846 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 316556762 1250 316555512 316555517
    0x40803040203070f030b150102010b0d05010e07080105040206071103100204080309101b0f0206040e091005070e01080a0902041506020d0816090501080c040b0a21060506160602090907 80
    0x99080900605007000041c0e00020320019408104000052091940c42d074000c40007882c18001003a1040100d000d03004124845901102481040c001c2c80010b507c0340c030051140d00c0c01c44e4201d42d42c401145007a60011940070b94003007024840c0034007050032128601e02c070010090030346000e5103501281c001240c020b0740110f01158030126007505242072050b91140508082d040008201c1c100d5030842c02685220300d0005d0110514140400842d11444296009007008500d10340e441e280606074195100c10b5011a100303c2420200800c0c10b00d4004c8600310f8802c14180d491b090340f590340307025007400707403541c034404a811540c0d4900e0f400f10552020701820242502d5805031007000d00620f030042c5030b0500601040d00a003101240d2561043e084810710089403802c1c2050b11060741c407010f0701021401140e00100c480840000c041101e40e0b40014044038021184131060300d000c01d5011600110f400901810703803c03a83c100306d0381c01c50003c8100b51a42d041d120b032802502d00507504002c5107a0302400d40c0c58502 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 316558012 1250 316556762 316556767
    0x60305060c0318030f0909060f0901090209010203041508091506030715021009030905040605040510062102070606180e100218030a11010e1804030f032310140303090f04020c060408 79
    0x1480c074000c00c0b141d4121802710f50b03041c04107840b0b40002c1c90350601031003202000b0750300182900880e402402942c0061072114046403002c60404000b402d03000d030842d0000341a015004209101c402c1d4450f46074001c550140003000c450b03081c04103c01449040b0000c000940c80b07203007240a108012801411807052295948040f804d190906102c103444154000e079124a09020400c04800101c0146804440c0e079880c1410043c10300c600960488071080164000150000401c04180b09664000b241210280070080509181041071081214035850360031615421005a540d420034182e0043d0540a000100000742c03050b603000000e00c0d100256208449508044900003030540c0c0002e072448404400b42e03a4036003005601d140038644610028401014400c03805200300c880e078030035440700d44034001c0394030040d00a03021002c0d81d81a2030701c110b0f0000d00c00800100081580c01c510622000c0c0c64030050b00035030500903824100000d82407501a101d820903802e02c441c6074a2001009001e00981c06444c400c0c0d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 316559262 1250 316558012 316558027
    0x14090a120c080c030109032102041206090c050d030e150c010207060608010c020d1e0c060603080309010e07050d0b180319090e06090105040213030b1e0a060305060c0318030f 76
    0x303060403004030f9020b210344d141c1186800030a800031644400d004141650306049190181508000c5c0525080601c8891801c004042042003a0b440f00c1c0030103006155294900d90341d44104052220055002000900422181f40a40c01d01210b03600d500001282c0c8203040200c150219422a00440350540707546486407000c000c0c880c828441c44403d01032a20251030562150f181c060b08000070055080e52060800041c000a030b44500c1d070402030b0b6988020148281a03690912005030382003a94102c885510b098141c0710403a200040300c0f42158001340040e40b442115490300000350b2401008800c42441140b245c441120080c40140b2030011900008500e602c07407c1070062040c59940c010942d500c105005000c00d950b12516481c2c1194001c03900986e031051507214050040303d00381d00091403502ca1005008485588111000c03400e120340070741c030301a03640342d8001600351a0b042c88050621f03000603004c40e8581f45440300444c0d1190310785103145041c40c500c1946d549503038002c142080c91040045a02d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 316560512 1250 316559262 316559279
    0x90406180903080c03010308070803090309130501030b130b010b070602070204020a020a1703040812090a050a05011d010204180c051603080f0a0b090604150b04090608071514090a120c 80
    0x60700704c020030300d10500350b60650390758004521038194003601c80302010000682c540700810886903081d001a01014604043c09c1251014042c280030032540756078140b00041d40300d8180c0c001d240c0041d4021013022201d13440c0c60b2020b8107a62041000b541c215808211060168441d4001030a5198031a0b000b40100c242d2801d103071908410542034514417480c104180000f03e02d80034251841102000d0303a084035912404081460003082810042c00742c0641c204070024030406510100ea00f0394180004403512004d4a00d640c07c0340f24502861012451101e014690301c000d540c09480b0030f4440d800e04920b4103581e801d140d503107040074a00c2103000542200400855031114085d0365040f401100c004d0060705444000214041d100030040e40c045c1c2e64515404490000c0c0b0840b2400401a1444542d5501e441d01c03101c102a000da400b03814141e00c22403200045108032210390245006c41c50380c1d030a021450300ca0940352658092442c056000f011038401160079001c0400c2019501d00c034170542201d2902d00700c80c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 316561762 1250 316560512 316560527
    0x41a01030e0a0b06040b0a05130c08161b020105130b0c101404030e0105040b0c0303090714130b041b020a05060108010b100302030903160c0603060503030f0906090406180903 76
    0x40d60442d00480e40240004040b40c04198004200304c501107050900c43e004121500e402d44d00a0b0780c411a04029050083c11551140b0031409081e610548030381c3d9502d0462640780d00102c00d072000900000c1a00b0522a400a001c1c03050501c149006490140c114450602052003900001d044035800203001d9041c0c0b0040000c0e14030781c0d0349020144540d850a24450061030780043c805010701010341c0c000c20082e8031030780899024158225015031103051150b02c5c3e55403600220380305100348c80b0703140700455000c9004207100c00d90200102000f03421082c006901c00505a012205038200c0c0d2910134080c3d6200600c4107006010100b90300030820074a103414030302c1c034110060780112244c1c4d1400440349825282c41c0382940c440340c0541005662601d803400c41c0d902d0361045507010080c0790007100c100350400c416460088216a0780d980d050051548500800d0348070300c04d1009520003160704011608260602c4409041102c40080000038015591400010648136000342c0e500300c15075840e015400c06800245 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 316563012 1250 316561762 316561781
    0x9060c0303240d1113050907060e030a0b010b0726030a18030203090114130303090503070b0406080415090611030615030402182703030106030605060a020c0907030209041a0103 77
    0x400c42c0151200410803007844030f072002d040b9109456150700c043c0c8810148800911343d41000f0030541c0f408207071280c1c6a0510f40175035000038000300c90668580c9000508401ca081d00b00d42403c445901c1c00c55a001c00754810041218503000c0f0340001d2080c000c0003810140c0f40484808001c2e900d00c0c00845520407100300305d0700b510303500e80c100c8410340c0442c0d800000d488090000703003080b40041440344100509409200603514406505030301c040105a404002e0f00100e500590440381070540300c042540f003a0080d03006400010b5074240024010034441280c8484074008041c000440c080c89841b41015a904400700025065000041c86164100311401c0740347c2c2918401c4d4241981407550004050300c8c81c243d407502559030041c001c5400c3c1c240342721901d4080c1011084840702100c801502d10380b29002413003540f000c0f0345400d100180c0c07400c0110407144e5000655001d00092100d5030200058800041e10b1b0500b0946e082c490261561524450b605445002c00310040036500000001003e0740c070540c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 316564262 1250 316563012 316563061
    0x30b0a1a01020d0207090203130206030c090f060316080711060708010f0602071208030c1b0a020f091911040503010608030706050a1107080a0e10050703030b1207060809010209060c0303 81
    0x100c10403034007a4082145c01c280c0304c003e200940c3e20b45901507000c034202e0980a004e94800d400000784440821002c00402029506403410560158688108032440c0008c5038150b2906065050707081a0b01d1041005a41c040d60a003020307615206a140c5603440c19000300c952001140c5020014000314003039081c00340091460740300511403203082024038407021b0300c0550000d1000101102091145003040181c880515040801c169182052211a076942450610980c0070f0394445084080504140f1000e030b01c90940303003a850b005181c0182c00880240540d14000070040070910010034107681c00e0048400900101000319240c001906248044810142c0708000c00340c0f8040700b11200d614020103035190aa00312100b940c175513000d880280c0b0200c04030701401d03078020b00ca0f81007074030a40d41280282c16418000c1d60108003148000302800740050004034014a541c0c0043c008109d4148180e212651260010303001500700000140407174100c1d000340d5103941c215000072040008041d54120504151817001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 316565512 1250 316564262 316564273
    0x4050f01060623040305060f011a030708150307091113080309030d0513030b010e01030b07020601061e030603171e041805070e090a0b04060e2509030b0a1a0102 70
    0x10201a04100b4480d400010350100d900f10b01c280c0c600f0400a89000355000b03010344419162401d20908404024060f04011070081c10340540c03040d07030700c1c003c4e60302c070343d006803200281170303e40c0e16600f000c0055000e248d42d4144940c90012480c0d064a0003840d000c5c0000c03111a6466040341d05605807410740c0c5810542d0350340d200303200d0f09910b5940098104180f041070b0500c5a600e041390010320210000b0380d00050442d050305400001d20800702c00c0d80b507040b24003030b503d81c40d07070741c0c68205049885007070a00c1a4000100798580c0020703841040066104109018140007a0b016642d580d6560140c0358210303170201200001c01c2e41c200340058403410b44404800056a540340c2414810400c9950040c89015000c00d0b0342c03080002c1c4628080c2c9418501c12400a010807400c0c038261034904042c007205401c60f070041d0304082001400044041c209400b40d400d28211048010003403482400c400c24400b401010030811120000201390400304c0700c0e0007806ea500010903084101c40716007114211002650b811588030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 316566762 1250 316565512 316565519
    0x2070209010302060715060e0a06080f060a0506130e011a010801080604030c0303060503010f0b10030207020d0803070c0f05030c01050c03010501170a15081b060301081002070305160b04050f0106 85
    0x42400c0c8506483c2d04030351507602c0c0c60880c20505e9040110f020480000c6103425800703d90009907503c05445088018010b2000700d8541e20710355101d10140340030341195400f05010900c00b031213a81266601c588040d018000d01300301243c0d0781c001c1c1e480c52940b4580700e0b5520341658800001e4a00204d11440c001c0c200400345502d0606114ae8520f4000c001808101e5201c0d15102050b03c030340c011030700402000300207004144405003078a00034002d075428188188000042101883e0080c020f030340b01643c0090000a220300107071035000d941d80c4010078030010013484864010000d5040b4544e620b07540d0240b0b00854940418584003401c40304094100071101c03d080c001000b0076030b80304545c40c4400c40d00c0e81ca60130003030703c40402007009411145418040304890350800300b251000050b41124800949107a0303016480000e05006252000b8001ca03103c0f0303040100c40308804044c60700280402ca100e403600c18507100140e0b0b444505c1c0d0314500c208841001d244030500c000d110b0104007a00f41e5a030010000c2016624 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 316568012 1250 316566762 316566769
    0x3060d1103101d010213210b15040615020c01051b120705070905220615080102370804080f03010f030203010e0d050301060e060c0a0318060f0504030602300105040c03020702 76
    0x251441600403040c96002a01c000d1f5088140701a40154045005d030100e042c0056081070484a11180901031032400d2000620541001040300c05480281c02501500150000444050388010345903120800900c01e0000c0c0d40c0070800c02030241008866045031118424a40a410030345540e104803000c9051005100052117903140b443d10401c0451051a40340440f407410101401340da49001c0d180310116540001d42c0c0106400815a42c200300d0b08010b55a4403045502c44204240b01d0000e0b41640d010300c202c07804074041c100d01c64005c0d00584a079420600201200c40c8958004d82144810401c040c00400071414240075829180d103260000d490003050854008255000500c1610208010300410030003d40302e900c2103c000d19800300940b10100d1a030b04004d000e4400d02100303110014141c0c031000071001d200302d6a00000c070303142d80e480c0c61030103241d40c486002a4101d814131070084150158040e500c0c40300119801080000d40358100d103290302d04810002203400c40c003290f4080c18010460840140e5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 316569262 1250 316568012 316568047
    0x180e06210601260d050a0306050108040b010e0c040b030717090a03080f0a060902030907061b080f09010504171f0b0a0509040302030c06090708061b03060d1103101d0102 74
    0x51082c0c0e00420524480403c141e16020225510f854a02800b6041d039284e07940403000f4520350391103440074854680c0e18001102c2a001c1101c015081c08242c000500800b4a090846a0055400c03040c003070405031200b8200d00c0b03503481500c2d41e50104240d60689400d4240100310705a0110300880a403100312050344000c0c080580041c030507510407071030500280c600c4a85902600181c003105108545070f10305000e007160746800500540c401f1440c1c10032903864054040600081d110f5000b80703600e090140d40300c01c1059980080d06640d0600400b804040356100503020034030981c5a2840c0207205200001c042100d0f505d0245030201d8009060801c0c6003041d48a00e08450304485056a410300113690b03e0604a0541c000c03044d0b03180d00390082e0300900110141c0000c0950540d408442959500e8680c50624400402404050f2100780d00900004000e8035001e041c001d4058003604c510702c0c0c14010840000d040519104840c1030b415a02e03443d00c5419100d444800c00b501c0e00c04c2d4021464015041c542600e0903 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 316570512 1250 316569262 316569269
    0x80121020d020616080304110a060c0f050c060c060a060501030c020a020f13090b07020d02010b1f120f021305041a06030c04030807030806010807020a0c0b0a180e06210601 75
    0x100d0700c0180100071900e40030304450a0100c904410801c143d11454001c40a51050381d042d5070402d016003943c1340c0c624000d10b01c0700494605848400c492007040e80d80486c1401c03aa242074030b1074002c1007820483c944a50000b0041d002203030002e07041d90316000c40c0100817140a900040d04051070401c2900d5560f40014251032210780440303a007a0703541041000600700b18200c03001c0119181c10040007004018550702d00b00e001e0003080c0c080c1c81d008507181108908866440b0720040e403003196034080c0c4043c8503844070006070b0840540b40c5440b00c0c60700c0c07504c410705070ba480c401c031302091690014164003507101c51300020001d490304690900c59850040c80300340e00d441030702440ca1701c00d43c400008500900341c890210b50081d54000f40242d01d07883c960401408200b012541203001c0340f0810005484203101180780072045500c0080c01191501f014a1031495070404000c09003409881e0b190500000c0c4450101c800a00c81c0f244526642c1c074152046c070269800802e80303016510344100204004450100c1c100d0b056 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 316571762 1250 316570512 316570519
    0x3050a11160501030908040f0b071505060d0b04021f1107050904050a06020c1c0305060a0b03100303050903010e060a05040c0503060103120813060e06040201110a1509030e190608012102 81
    0xa45c2581015811442a640f0070749008200e010000355040c1210301038192a4082c5e543c0003070712944901002c007600d0044807459484142c200740000003c09608419030801e00107400c6c3c010520882502400b000d010454200100301a1204194542c07070400025024180c20340d01040c150600355180303a03071680c80303010040ca415004108a4492801000291700da04114240700760085c3d1f00c80c4015000b04401d6803524064144801c2c0850070f2680c41c012070b0b000e1500f5000b008582c6107540c4049038180c1125406c558155201d030303403041803100100b08250184583c003600080c00d007481d01d00030020340030300e9009a00903000200100040703210301000841004c03540c10104090760722800c8010345d0b041c10ba64001c1c00b0f0740c5070030b0310040202c1c00011901c0c841e07817003a2203441442024a90503565007414620040c4501e850102c0480b21208a0f0440321b4418403a0810b0081030100c0d000160050300c139507600700b152030038290301040410740c00f00e9010b0041030007444039504010414101d40011f086520040d01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 316573012 1250 316571762 316571771
    0x106090b012c03100e3304020a050607060204050f010c0203030a2a051c030612020d170301080a0b0c0a1d031e0f0705100e1c06050403050a1116050103 66
    0xd20302d0040b030710840703106004080d241e00800d140f60b42c100074241c42c82045003d11990b04d100000410600c00721107641c1c1c1040c001b00203288803211000400d08010b000726007000c545000042c1e16141d030f40141001c4d51048030050303155410315092000b03000302003c001c0e041207510301022000d601c02004a6852000c4d51801c0505482040203000340c0102030300380005001c210b18808001d01402142042e00ea00c00340c11051042003100c1002c031f043d1030081c0140c02100c90180c007188010b1404a0341e043c5030718070862071a55407a102c15100d80711600264407207211500901109d2081245004500364050380102006041892900000380060121440c408420f00044854801a45d00b0484c6c10b030030070f1000d5603459861402c5485180c48081040700700c18940314814010480f0702d041000f5445482031541c540022150707000070081d0100055040e1240d0f100b100e1080c4000c02c030b032406a54402c50103074a510f50394011005e0018102c42c86184030300c1c1990040494800d81a2910304610200d074000d280104d0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 316574262 1250 316573012 316573067
    0x2040f12030e1504060e090405060a0b010c0609050c1008010315020d0209101d2707050c010204030602030415050f0f0c0c06040c03020a1502060c07080910030e0106090b01 75
    0x1d9400b14050300241d80103101100f62014242c00500a1041e0b8500d0b5441c03d400807444400d0000d615803d8600a10941001c0c00280302101c4035801400341100503d00711303405614640710081200d03445981a120745d008281c0075201030400c5001d5201507541c500d4180555890342d00c400211702540034021480e160006426600c0c211180c040d2003418000030f086034100d14903124068001c45881c00003a0016015086038802d6150240d0064507001c0c190402d00306400c20b105030114807102c0100340d1001d00c4401e11040c0e40702e41c824030281024500c602ca005a0346e0500d8100a001c0b01a0882806640d40c2420b0401903070410050741c0b81d03003041c41d49400d20981d480c0c0c00c8400750103000d00d03903030784645101d45c00801003800342e002d4003541241d000740c440c01031980d10b40080c112001142c0c803408015a03c80380c085110b0783e1188008002e454000c3c3c449030308010907800008e101c0144460a0070000f615140c1c1110304110038400d41e0300404c0a00801c1049100740350001c0d01040b0040c0c80c0d413101031142041c15 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 316575512 1250 316574262 316574267
    0x30315090a06050402030a0501062613170f13090c0c0b06210705120307050d110102040308180310050601120f0b04060305030a09050d02151c020301060c1502040f1203 73
    0x2c00142000030401d640340d1610f00304d1803006110074031a6030005000241491031141004414184142c0c0070407107504a079071050a41034101c2c0000d0b40480b5014031151020b400300e4045000713000080300105429907155030a010000c42419a80c0143c1e0308103142408900d0100e4201c241c10810542c0318000320300c1c41d5540030000d00f160f03200103e1284508002005180c0c0d151002c035480050b80e0003180c1b414558410704203034943c0e0f4065002e0040003540311100c45094103004000a480001142001616141e1281d0740c1d084160031105282c240540b005000f000f40c0d10b4244040c110009076000104202c0c542880000c01c19100d2000a40181c3e5a90720401e5584441d80c00031582540d0240042c003241c0e60301e1078400d42d07a42c8642130071800079140d000041560314000b481000c815400030441080c000b01440320703c85541c440031030300344051025000403c0c40007690000e1130007410651150310f00701825050241e41e55000c8034000ca00d645c4100803d12000c00c0e4031422100383c81e582c00042d0903842d2507103400e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 316576762 1250 316575512 316575521
    0x60d03030c030b060d290612090a0f030c020f0411030109020d0b040203040326040231050114030d08130609020d06020f070204060602030a020a20131d030315090a 71
    0x8003a00f02d5800101104d1150301e91b00300c0c1101c00591002c5200404c020403c3c0350f031ba003010610750342c0d104108120b07801d0403100c0000a50381003042c1c1000e0f603042c1425580d500d200a508107008034081645581342800f03519140088207884001500c041c0000c1d44c09a08442075888140250000d090780420854a0081164003200e1655400340c011542d900309030030003801800d1501ca00d0313540c0d080c81e590b60140020011070040e0046501a1401c3d500e15201e1081c2584220258114080e820354200720844440060041c1c9008228601c00c000d402c0508005041c01d180c02c0200380c1c0e042c0308842d024800329030140c1c1c24034258941c1081d0005038410b0a4400503100c43c07150940600038a0010400c42c0d8902c002c00010a06d6505c2181e0400006541d00002d90b12801180c524401680100c00410040703600180214500102e4110016a08280b030001559042d084140a003801e46c0d03030f0112400030014184160905c44400c4029401c40c0790004184010070300e0640b1050040c5c41000218100f107031150403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 316578012 1250 316576762 316576781
    0x30c0103051e0c030f06060a0504030f0303020d1e051003050613030207030b0109022101080d0e0307090212090c030703050a03110312010909020a090b0a031b030b0907080114060d03030c03 82
    0x30790005074240356070a0f004540055410501405440f030101c0c80303620342074044405c00009a114207042c42d203551209480c080320004160240341d000c0080d10039038100c1e4811900841600512910303418648218081210f01c01803460780b00184000d03007800410000100b9a9110301c50300c6803007002540501c0c2c1207080404990006200074004000030414612a801600304500c550340f16503114510042071525044003032252003400d4201c9040303040301912480010304074140103005ca44800d40e88480c1c00c4120fa201e140e5040014507203000344403261905108cc0f20310b0400c124000c104003410b584609490f80032a280050600c03010005c1001000e000b0710985010300c24030400700100c1c0d80d45203110005841070394012441041e181c040492048003d103e01039459030080c2422a5050456550402c90105d16055808101100c0d2000000038440303401a071140031403030040c207842e03840c1002150030750300189048810300c0e046c0d2040082d2034440745510000c40740c040c03a01081110030f10b541600280b0300205c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 316579262 1250 316578012 316578061
    0x22020909070f020d0203031006120e0313030224040b0c0c0a060f030516231201060314010b070f02010806040e120307140306030c06091809240402030c010305 69
    0x10410880300c0d004003118207404902e40948242516842041b600c84c44100e80c2d00348180005002441240d104007035500300c49044640c00102e481009a2481c9140c000002c880740c0100340c5181801142840c840d03d01c100702d001442800c100303030040d45c260700b513005038001c0c0031001201242d0744000e5074040014035180c0c040a04200605070301c403c80200981c1c2d408410402190611020540d00310b00c0001c00f480105980c2d54282011180307074034412816488451090a4480c144500307004010318112240c001c003003a4900003103400500c000d060501805030b00520509409000c1e682c0030070502c41003404501e0382440c000a455545900060080c89840341010b81441582c4490441c00c0001000714041c2030203031182d002440d9182d00042c5079100490b0750f9605a003241111032564141781e0043c00d00b180780180205400c0d48501c0c4800d44490b0202c40100080e0f0203583c0021001422071011060351031200301c0041e06180517004070b40e8400104c0c10080c1095601d100091031065617490301e02c1c1503180728 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 316580512 1250 316579262 316579279
    0x100902180403020c1008270a05100615050304030503010b090d050a0302010f0614130515060d0605011707050316141b0706170406050c04030804120b07030b220209 71
    0x1420000d5680761941130444c01a074020301000a100e02400d80240f1882c403a8001c9a8042e0216112200f500302c18881c0c0c1525101f8601c10b0310014206201705e40c3c050301c84a1000581a01c0d14200d001c5100102c08103c0a10034200107000121354040308407030559038281880c580d22050600494900c0c010200c0140140c0a1140400200359040d0042114001044c2048c0141070701c88c124200000c90154800b98422410f0300b185400b1500381e041258803041d021403c030010120710020413610352103a500040280e40c1c504003486290f80100c100c480414806400030014641030001822500c0003904c0e07003040b60041030b08100002c0c8685d03143c0320711549401d84151a00c00c00c520380020f02440b9000750003d4000d250010441e81e01c41c5555041c0c8030003414003060340d034440380ca0380001014050804001e0f4001000003201248141000300000e114107041c26248400c2400e0454000384050081c0d81003508096154455542d110003c0044100b500c1c020140f8440c040e2042c402841590b0445801c8402c4c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 316581762 1250 316580512 316580521
    0x90717030315120a03080a02070c03080417010506010c06090f0503040609050901081203071124041e030225091d0d020d052517090a0501030b0310090218 67
    0x403014501500c09003400b8800700d2102d004101541c10352103446070166100d6804c00021a1107100010b03040f048881c001803a04065841e042141590394100780e46055000070100954003400704181481141c1c2002009503003880000244181c0445c90301404891f16042e2000610901e146003441040e40300f03040b2540d990b5501d0010b004020244a15841802400c000084002c03000c2040040280f414001c5071a640d2900700a4840f451190060949403184950b4010280d491009100741c405041d000da0542d89028a03101100d000b052054542c00c046580b030100000f41c0001c1e150110140d407076000050102030b0840d84500c800540d1085100d07500f800a0b290601c81390050244002c101b16040d01c1480c80302c024141d0743d5526500c8600001030080116000f40800c100d100c3c00b0b0600014503460040109403242003036038040c0380f90381c1740d035180004500c042840e10b031045070000c220a00301802410007040000f510303100d00d048559081130b2146000c42c1103560350824034000030f500300b40805050a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 316583012 1250 316581762 316581809
    0x1505041e0203101518060b040306020f0408030409270203060403140906160c0605040f12030306030605090d020f07060c1209030f140c04090b0406200a080f18150907 72
    0x2a05c02c1c01301d10580d4041c2009111124000c0b4030583d80640450391a10349156900c4000750302410b032072080140144008951130b4801e00c0108010056a0320104510900c05a1400352901018414014031032211241c401601d010035496405501820120035248002050780c181c0e20031186940d03400744000034015203a501e800013020b40180542002c09490b42c6501060700c0c81d01c140c0c000c6001001c6030380d20801c05a036071040d8000720a442480c0c0400d085a90780d40e180300381d6400351074080c500d4010081034500190304114003200043c07a80010050b85d0310301100034011580d0060040d04200d1805200b00519006075400002546c0c8400048420082d0317051003e200e01c0200640c1201d409004100b107881e03d054025a0034090304050120f00350f4880380d544100a004100c1411404032490512080c4010f0350409410070b0103031511030061500d00007180c510081e1f40103182c100108104451165550b10000b030007648950200c02c640311304d498000d84680707040160f6000b01400100000224016072 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 316584262 1250 316583012 316583051
    0x30807050708010e03030c07020a03170903060a020a2a02090106090906091b110109020a1701052d1003080a0e010f030e19030905120601031505041e020310 68
    0x140240c0507501c1458403203500c1c909807500c43d064101c1a078414404140b940c00e803180105152440240f0440780550b59544420110700c80c100032015500002c2801c0700f480c01c0910030a980030849007411880c21810680151280d000c040515111400549251050b54040c11500000a03002000b20030290303528500100104135902440011500b040c0c000218031100703010305d004d480321035583c54003100c2d0521011152420094101c581540d250142c02001d620f400b0340107800351990840090a25420703000141c00c0da54003402c1d10300841d9203064003040c068219110710389115004103d0114a4a03150026070090b07800d900007401c40800007a603204015008403e40d00306050030f8984ca402e00915004c180c040741c1c012110b09242ea08804000c0c1d02d03a42c0c03501c055040503031107420b00c031000d40e80721000b10324541c65004c11108254000302c01032080c010888030186005245038002d0015241a90700c2d882c14011500d011820150991300d440115501405206243c01c10b0300010484080001c0c04500d02c01c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 316585512 1250 316584262 316584277
    0x20304050d030b0102070902070305090a030302010f0e030423060d02120f0105030a02010807032d02070203011415010503060607050f0a0b0901060803041e0e0a09031e08060f01050d060308 82
    0x501c50350030100c4616000b8041c070b848000c03058014000240c5000f5a0070040e601489080701004003c00510303000360b848030700080c0598041d03070001a40d1201203210200300c54010070041d409038004e0004101070a10401609900c40c1e0503503864140341c0c49480418405d0091210101107980003141700c031907124642d00c0c6c1904c2100031640a44590740d03108203040c0c81d401c0b581000f034000382e400310005941c61f000344c1004030000503080300c411900c90b07070b84940c03020301b5031402d11400403c3c1c000071190194a824011001e1050982400c00d800303042131104418050310300c191460600c9000b0001a14903a0384e2803e60720010b0300700741911403c00780d29101c107480d2900c1364800c488640c0c10b9800b01e082d400b8148110800e4403245002546400e0504072214058950885001400480341002041d0401d018241e98010341c1c030041d0200f80400c040c9006020300c0092901c4820011150001d07103805a4040c2c0070030f1300070b00265643e04147c000c0f100100c070144166182d8142030303810079000208100c0b40400801b40e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 316586762 1250 316585512 316585523
    0x414010b010f0807200f060a06060905061b070906122d030806030f0a0308010e130b0408090a0f060e03010e032805130f182c0109060f020304 62
    0x100c00100c0054070751408040000000650090010790480e00880000d80003c130b00c581e50360490201102d9492418201e091210300303980040081c8038500c07400c1d00861003c1e24003401c0100d5241d01748070102c2c0c01070003182100403500e0000c1a40c00071f1014140504c9000c0c0010610a100f51501c8100200304c0464208003101d1045003000c40001030594502a01440205007602031000c40d0710782c800305d1f040d00c00035040c690b05010b0b85015034180300c3c0400c0620007043c03080d200da06496141c21500314071140c0062003000c0d1006c10840c8100050007204400e90700a5002024545800c1e0700008a4203601c25900325512400f00460040b48a9400211507043c0c907104500911600f800303481025240e0144a4001c948003001d0b9130400d4048105412000c8402d2692504504100c60742003140c08026007070b44581c0441440f0842403040c012024142c1c0e0910035002c8092000382c1c0000d0740410084101d9040e6400c01c03008141309d044810f029003150b440030350001402e1040701c4041c00200025802034504491 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 316588012 1250 316586762 316586771
    0x4060603120311030a20030a0b090f06011205090c0a031506060309020604090509030705070635060118030212060708090d0e130f0903020c040606050903030f0c03090603041401 77
    0x351248a4007441e50ba0480c0000c0e841e085440390301c2510050b000d202204120072805480208004800e4000b86101e0903500748c012980d03c84034000c0c0b041000c2c010349410203e240700404c00c556170b60001042e50100103004000906660f030b240496040c802d11545480e4410800030f4000140b05000000d83c3e42d0b00d40c1c1c1ca508102a5550340c00c183c08030390a98200941100c401d1200304442c0c3c1c03140d4801765100c881e61041d00d190801d60342c1d0707032414210a03821540119036500800d0b5400d950b18407281d02d9a02c000081107a0a035100381500d010810b0050100e410050710420766180390b02104420401554040d140407090744004a00075203c98084620782c0c00a8a8240003034030501001070400190030b01600c60940356070303e02c41072040042d010140da00182da2181d106415081c010320500b02100c2c020390261000c80c3d00e41c802c10050b81d040380e115608010303003400016503d070b0303010044800880c9400d0303905030b848072201d100505500641030b034643d01803004000c1105220b020036094603a000044001c00c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 316589262 1250 316588012 316588043
    0x10506120705060702030c0d06090c1205030d0c1e0203040e07090f0b09150c010507080603160506091906021c180b030415062c060d081e0304060603 65
    0x200365540d00154800a074440d4408000505000008110140c0041d098401140146022031120034450400300d42c1079035506a0542808161a0100040c0c1407690038a81a190380e80c480c150b40b40285c807028100203580e80d66150540303001c2e4080041c4034002281101c42e1000040c0c0103501c4c0d401c244102c017002a1140300050480348103440140035a9050058510001d050003800100c0750003aa11060f0019886070f20303490f01070b60341009021007960410000c10203161100000b0b00c50140900200e0180c2d120388071800c0e141c84c0e422052410f07500c0980d07440380c40b40c03981000185606010000e8210483e0810f80c0400c1841d40498030251203003143c0110001801101000c96403d1405018003d010901d900184a10141e032402141c0042c003440c0c1004800118000200868040c1d40c4080308101603403511704040e0742c001d80341000e894800c4402c010b031841c01d14041441030030030220060510300d001907004090f0390901006810004000880da44914081c90160010521781c042503403410071000080c0b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 316590512 1250 316589262 316589269
    0xf0a0819060b06030c1911190312050f16020109020405090114160e10050c1213050a03080412050a050a03020706030608011b030b0a05040504080711010503090303041b0302180405010506 81
    0x22070190400c05c40451400040c0c201000138072501440c21410420045152500810b0412001f01d1141c984044042c0a00d102e24002c1c00442e0001c0390982d4103401c2c407040041202d10380452a03400410f482d030660000e00f00420880c0101803000000f544a8900028064030000540c80f94010892003441d0300300c6a21582581c2010b44480802c02d00081c4044490f40140c3c20601001d010000d80360510318203145040c8440d600781000001d02080030702000c42c5007900201218400c6006100540c0e00c01f0186045403140c200031303c22405031035900e082c0f41415608011040003495040c5400c801520328850707061030025241e603035070b00c1004006400c00320042481d03501845100341c0300d00c40b4800c0d01c003c442c07500c1041d0082d140014005a10151031640055182c43d140030743d5201d03078480c8100580e905070300d140c200d40d00c260039154141004401d004101601100008076a00a80c2000f00401c4e000c0914003440800003e13030308000e41140003102c000c50020303030f8422011f0185104900912060b500c600a1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 316591762 1250 316590512 316590517
    0x3270804210c062303040b06090c12041101110303010603020a0e010e091801061e03050114010b07030503090a021011060f13030810050d030c1b0e060f0a0819060b06 72
    0x58468544032000f00b20290140404505024440e208080301006108842c0c6054100f103500f962511081d008118192600100d51584400c01c449250305285443e581d002c840c03480104018840e0003c2a4031406581c0149003c2044207110400c580d5a90b07111a030040280d0000140c40c008500000f2403a000c0798000e03500090b140d42c014150105903642c40c82d00b405403200c2c004520005560300d807008903070301001001b041a02000c07140a1008149145885821900000000038580881500520445131454210b0766080c0c2c06180031900ea480b01c0041c141090041c081c000c0d801000140356410281d00700803035104504031b03078068940d80d990b41421600c403401c0c1162107103164509110100c00203802044030a400100000019456544810100e100d50b140450142c1c045a00000030328204000c051103c1c803140c1c44628100350301864420303e0090140054030780c6101d40074604103a01c0070784030001d101d001850f503a4201da00004406080c281605010300c000d03101d550070300340903003c1d50401b80c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 316593012 1250 316591762 316591829
    0x308070b010e0f042003190c080303091207030e0a0e0f1302010e010f0203040510020a121e0f030e06012916030503040f0f061512030e0103270804 64
    0x766000c813656103548201d8070200c0202e00d54200d005903240c207174950710208180030b9200810050606030885a05144210542e1940510643d40c003c20402890322404540070f108145160455034407100343c0e1505803840424001c0c40da801010002001a10301094400c0500500d84200442c1c0a0748800f210030400a008460213804125608041a2554800d582081c0308070910b105490600f41c58000085607802da03070140c0350050340618205004d010841480d400d00c028036003000b0110a460401c0014521007103800441408110000b450781c240c061f03044122210740c60420f0314829a12070446990000c40d030a050707807030607122102c0d00d402031040d24101d550506e1190b0814010702c00ba554100c13800d0340b000b003003152405c1c411180000042c20348490090441e104140202e108044c0c0c003440064041e85030700c40b0354000c08100c04600425000000711130001c0c03083ca80810040f06100312400c4041144034601c020740c51a904003810b1110441c054800d80d000a955103081e00d080d0403600102c01140308 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 316594262 1250 316593012 316593031
    0xe0a0510020a0b060d06050f07200706050a0c080a09080c030a1106030619030809010e040603030f1101023a050118090203100c020618030c070612060504060308070b010e 74
    0x2d00301000f0541c02c05031998800700043c4401c0c50040c0c036a4a0f030007075034030644060b204030089205004180d6007056452501498901440e8508e140d255402c694500c0c50307104c0d01d024040001115042c0c02c0c0b1401034420040c0e00400c0d403d50314012034500400407412071081088a002e03055010655180c04640c0f04a59500a8556010b02071910100241c551016050a60150a1058a503094568900b41400550042c8203150b20351080704c0016201d6030302c20b04018800d83c80e14005100081d00449001c4500030180381c8031030b0050130460054028072a041a110000710115401440702c0d803101020b000308140e0506140c0212040e000f2842516428002c010030700d65441481d80496044d503010340c0303120f0b00080c129504124031485510489140c290900016041041000121034800004a60315410711000350f14156041854940b00c80d01c5000e10b1b010050303a000f0031030542c40545c0007080030f040000c2003008000c1c4d0328503083c0700ba40d1042c03030100c42c9005a0f0000013994032240c04468810400d01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 316595512 1250 316594262 316594273
    0x5212e091d010c0c1419080c010f0510080111280512010f170604120e120706020105040b07030204300b090709140c041202120109030e0a051002 63
    0x440000090884040c111030740421810310506221024000c003141d00344141c544034141d402d02d080101118400404943c0e8581c004844001042d44403446900d1607a000b00d40161070340600001140981036680340051a242041c0c144805000c00d40741c0c12048880f440000c00204940014100c0d15004014a800582200302807118901c0c20340108840c4014062511910744404648410700303038038080c2c009034001c245640040c0140c1c44621201d000b0303015070400501d500d11b025503a00d900b5038684c07140c101c00c1101015240c170381c1d40c9132403004c590100302c0c0109980c0c101c1c2c0c0300c6070000d00825044400b91041e42e070310303c041a0700e50301920840f41aa00c0d04000304c000c0c4035200d04001e043d04140305802015040e00315809000c41d5150140b1030250040d00094903009140c010790005543e0840d9810072481904418403080c0300000c0c0845040b616a0820344180700c2460002494007001010720202d60350904010404240d4083c0e208688d07064200c404045890301c1d4424445c017045007954003005070703120 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 316596762 1250 316595512 316595519
    0x30309251203050d050c0a0e0105090a1a0903100c020606100806060708040513090309091e0f020c030f0901031a10030528050a18020d0803040305212e 66
    0x90208401d8207806810100c0c03410400c015680110b600c101c40800b11380e4400300c3c20480c1e0075482100444044c00901e415400d100d070b041d0006000f2006c0f80702d80f04c5208006902400804d0a1205480960100609944802d005151180302070507009420000502075a0001201d62500c04408079001c1c4003070f03640e42d1540e503816080c032507242e1000c0c00c2550803200c00d010016550707683c1c6840c9440fa800110b40440e4107505441c005d090700e041c503081101d5032410b2030f00316040c40130314001210b0110301c1c0400c040742d881504003511009210b80090844140000104541c01908900007800c50000030b03601080060040c040280c50402d0702c505066210792210320180d106442500410742203240c40884e692411100c08080800307504c4425009040c42d10b607800c01c00751000304c1c4291391018458101070788010001350300003000c5d1010414002d02000010001c43c3c1414030030010394442465140600410364074240c07000e0030b0701c0401c40304001c0b103004954405200c00c0e1403803141e803d8550801d0005054504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 316598012 1250 316596762 316596779
    0xf020a0801030f050a061b020609033a150f080105010513020a0e100f020606031c180302040906061701090b01050d05150c120c070809010f0e030f03030925 68
    0x2501c020550b00c503c20700285c05c0201c4c200d4803c0340b0101d18041020606102c4902000c1c2c00d003500149901c515400c280070640000701c8040c10140d03124000c110755241030009400800c10303051403150250846203015038031005580400310801c1a14501d4052814040c2c2e94241a0f09a030030901566403c42440c0115039089540340c1c02902c8450081e003420001d40c103210000c9040000e040104500285001440d000031a406021440e040035054001d0a0212001540d41c449c034030300000b49004204200761401040300c40d40c8040c40107154014002e0000c6a01818908054070042c0103800102d0900c00c140500d0003014400ca00383c5641c40040c0650326881c04003006400c3c0a030700f400b900c4034050000c210b1400c41032000540c0c4250080120382d82c841408544c03c117900d00c0010180a10804200280d1000c17035924000e680f80714109107460542c00c07802d05070440380c0301a1046800d0b003510a207135000441031400700c051441003200380212212107911804801d032403425100792280241658000717108085 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 316599262 1250 316598012 316598033
    0x30504150506060a05030c092206120506042a0b070b060301150306020c070905160e0a030b010b030a020c0f280b1b22031506080d0e040b04020a050405040f020a080103 73
    0x171021000b032070414880c00085000c07005a071032703491001d0002940c0d510100185119000c00350011030750100c9001f00a60301c540d502e1201034000740c501e140c40b41280d141c3c45200b01442c0003166100110341d011550740d045040c0c2c0c41d00b040d0f0301120f64103c80c02c0028818201441009030401d0914890f074521490740d1a4a00254040d20341d0003454015200081120b5489000c0e15008200d80d009039000210950f0ac014407000c3d10070700840c40ba00509004102150003110310350306440c403041c1c0ba1a07407030f1500d90340f4100034407900001d49694012092146803000e40400c2400d2101c03083c40302d01c03c2c0c0c40301e0396100301184e00320048003c060100802c0480c1004145020400780314a4040215241c10401404029602000010042c042c00300180c240100302d854000c005502c4070115090100e981000e6000e034591140b148201c04020072925020015034031078014a00090003d8030855403003698141c02085540240a003500417410001b242c3c40003051b6108588c101c0819542d00b0f0720a0342150b41e11903215 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 316600512 1250 316599262 316599271
    0x1e070e0c190c030207150c0605070806090a0f090f230705030a03030f180c060e01020615040504020f1504061808070608250c14161404020d050106030504150506060a0503 74
    0x184110800490700503040c1c00c004c00110300301e88075840c2c4113807e8035208040d100c005203a50f0400c03540d0418042c042c1c41701300351650410f92a9401003054440c9004100050020000c081c0c021400f600341c8405008225038550780e40b0501c1118403d0004c000b0145d16942c401c584229038040e4014443da4021912a030b00031550000c129802003003040032001407100ca40425001520340b212a90810061280c20000d42e4100b001c080c00504041e2412921054103001038400c0a4003982d111400201199141284c1600e44100100b54120015481748101c0e03054019024070804203c1c0201020390700c00100441c80308461182c0300902481d828851700329581c2102034080102c148945441c011840d5000f003034500224440e56074601d1201030b5003020912109280c2e881000c5400802480c1d2511040e010103030151001480c100d4030301101c540200d802407042c0c03510043c0c26403410001260b0190b05401480c0a0345c042d110924020710280c00c9901198010390701180c0c880003c01800305a2401003001d554071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 316601762 1250 316600512 316600517
    0x105060f0f0d0327061b020a0b07110918010b060408060c2d1e090306061002122d0a05030609040201120f0b0a08030705030403141e070e0c190c03 64
    0x2201e13003d6195040300412145449085488442c0511071300c3d61024021000b04c0800c1d0040451480c2d1303801241044859000d4190401400500d00050045140d00c0c1c405c8024040d10450b124a0003055070304c00d019045045041d65420308181d80340f245003440650781a104d00c00080c001544408461246a5024400a9607403280c1c82a030a9070701a18042440d44081452103142d0303948405000d100d041901540301c41030310207001c0c80070b01307a1620009070003507000301c041e80d00d440c005c2105541a4601f001840e0510300310080042c47c9095110301159450030800d00e54501e0740c000c2d4580c00c0c4042e940c00b6604030400094002e00c00581d5600d4001c0d01c1d1a04140107041a0b040c000c5107048c05001d80d5414129103d070395844490f511801c0c100726000d6001004640047d42c20084940d40e081d45030f20988c800079020110048030b0f01e102860520003109070009400f6119000041e8451403925401d170761096110105088000601420001c003c8848a084c007166041c004461401d06070342c0c6503040c070000d504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 316603012 1250 316601762 316601777
    0x9010c020307060c0b010e010308070b0601023d0c0f08042103020a0815010203041e050405010806010305011b1e09090c03021c090825050106060e030105060f0f0d03 72
    0x580c03010720003107001c0d180f15035600302d0444184c00c007900c0091060f07005808404c0d00b500100081540b003015a820294440c0700c0c00035944034100102d00d401880c24910840b403000341450f100000c0d004107000c80340c082189041480c000b06141500c11100581c0c8a81c010420001041ca200b81c401c800e5241e105218101410a003206400d003000d51200340d100c00f402103507002854261840d04940d1755540403c0307101d1b0104041014400003500d901907813080d150146038030640540c44542609a41d0080c29026200300f1542d80e4601d99550350304001e101c15130721546081c894480844800441814101541c1c803485c08031841c0d000d5002c21099030454200070010240000318954005002d11700815030503035400358640d00e181c03004149580a001449065502d07143c200302c0050602c0060b10150002c00b1240d01c1c07203030100030b144ca240f00c9007410014242c0d480c2000102d1407507040014110094410380007040182d40300014084405403841585900c00c902c40c1c034080c103d2078409000a5204e200f468680d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 316604262 1250 316603012 316603037
    0x3050d020307030e1b030d1b02061602011b0b0411030f060a06150201020c12070c080607180b12060f0406230306071407032d0306030210020a0b06060901 67
    0x4003281c00c01d80c1e002c4002a01c0f8a000c89414000b000407080c0203001c000703420030304890040003c2d5104407114203141440031128000003003000820341c0d0034200750081e00c1c6694845100502c00c008204128049000c107119080100040030071205c8072410175030011182841c1c0e16161505854202070b0803590b175162240c50a02216170304180031140c012015030070003043c503a003003035040e0182d04c8203000c00804580c4180702c1c3c0402c01d440001d8007800d200324201080c1d600c14403800c01401140c4a030308042101d102d400f040c0000c060344220942c02d10180180703000c4180ba143c25008500f031046035440c40051481070b002c03c0140c40c15040c4001c0f424001000040c01e16551440012183c0361158415004400c084d60b922076810140002603100742c00e07240181601244126043e01030242c140050300308403400300c1d800c6085850741707220010800381892034011080c002e0402000303051640400c0340103036558480c2c1c0b48118000100440701c40d0344001ba0075600d95030401404056005030710024100107a245001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 316605512 1250 316604262 316604287
    0x10120206070f061e0c05070c090506030a170307120c020607120e07080109050d0e0a0308030408040f0b0918012706121a1b030708100e0c120906010614070305 69
    0x6941000c4c050560516800c1c104183d13a0480ba80d000c040024400200300c0e90000030340084c01101a50300c0c001c400256a1a02c034003003032811445400007408140320074100b840c82003210f800b13107101d0483d03039450040901e440d0100728165070f0501105400f5900040c04544c010b401000500a5117401040015800200108461034010f0540c0009001d0755500c641c0414841c003445042c403501545c2c144040581482d03c04039050701d00031310002e00702e1007001c000b1408004100b400c8400400e00f20485c07052003501e4502e2940640c0c040c658032442020300718006031803034405883c054101c40c100c101600c507100007244010b0b64500901d0b6054020b503507401c000314020b420030081c0c8080a000d4091400c0c1130b4031240f02080d45c05006001c9004c2d905a003e004580005481c0071a58000701ca854204866141c00051481d8000940c00c04902e000d6901c0130881d07442c1c0d80a0280207850988000c589460b2192460252904000e0043c040050000c54106240401810041000b280702c0e290a40c544404240d80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 316606762 1250 316605512 316605521
    0x6060c0314033417090601031707020306010906060e10120902041d030307110609060105010e0d0212030a030f0209060f0702030a080307090509090f1e010608030d050f10120206070f06 80
    0x10541c00c1010501070307403901c0754005440044640410704ca009541401a44c5542d20401484010300e420300c02e1031b103c0b421421080c00ea03210154090100c541e9541c5030b0030144068a4903001d04030000e0084040014203280040e074000c800302e00c80d00d581110143e401c810401070a0b425900366009515a000700c11004081e420b084030003605a0081c684030f08000000421100078a040d88104c2d6014030140301c00100c020a2482c11914242845030321508142d006c1200082c00002c06507019900c0581c02e07503c0b082c00701c024000084103030b40c2042040c8107030744404128041d50109641040080c0010540342c011070009203400c1f40002c044803408602a5075181301c2d07900480c0c0c4100050850a02008541040c803919034100401030007034000c2c115001c1c5070329922800c203022022904032200e81d0501f401c100394001d801420002050320b90742d80509491801034401a00d1070310315003107950005403545168040102c10760700320f0a14a108503105408001464106000c15545003100f0701c2d80b82c000800c10300c00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 316608012 1250 316606762 316606831
    0x1b0809070812090a170303011412030c0604110607030804021017180706050403110906040209060a030b0307061106070809012a02061b120a060e070c0606060c031403 72
    0x10316591140014140305880800703030300c42041740e400d00720f4641e0050300110580341075815030b60711a08070b140103400082202c060780b0306c410198040060600d00100c404140300e44210701426032034004030182c00a2280501c10284090005034507030f808100180303060f00c86522814000c2c0380a42000c0c100400020107001d00380e0302035502c00035621140031307450010300c040c000400ca05d09140782070914517125040104030f0b800e0041d11407410305c0005202c9503541d9060ba40c070008080c0096444118000024005000c05071610340300e407149100005400d44106501b8076040c0c03000f03001c2c05141e260341c0419682a900900000c12a540b80c18442c00081d46803003000000115108040b84810301006000e41400300140046101c1d070f0812081803000c4014030201c0e40217880d40001da19685d0740b01b6401100800c25604058071011071a002d1000c482d5103c03d802ca005409100c08110303071a91080c09950010044100401007070346204409a62000130000d9540030005424545a896062041c005c03190102d82 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 316609262 1250 316608012 316608043
    0x10935030406020a11030607050904020a090906140a0b0a090312090305011505210303070f12050103080714010b03060a0902040e070e07090605041802072f0906041b08090708 76
    0x204c0784061000c1520f03240044202a80584214140110014141e20130716540b42d000e9600041d012070f5045c82202440c0c02050766000c2004016219801c180c0102c0d80d42021501c603184000700411900c03008021071b529420349403100d0030610f2460b540c1e00010244440d8070024032210643c0000869401c1c087c0300800e519400d44036080c08d08103000c0003a5071403694801d64030b48070072003070a55010100200f226001040da00b8449000d200301e00c0220384010710100308584250074000000104030740076000d071035402d10400c9211241c0c84001516400c1360401e1719803940c194000c0c0085044030541780d0014121900117040882c0d800710804409182202070350110000c5c410300da0406c0b00b510b5010042001030b000320716156240c98603101100710441c403641b144c0f080086d400a0000c0410500e480c0f0b01c00d24000c224069503c110050301c6429032041511744140c0208440400551245043c2c410006080020200300c4c0343d0864414049502020040680302184121030010407102c00c2005031042810b04103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 316610512 1250 316609262 316609273
    0x10306020d0c0203210a15090912021c031a03011d060a0605060706020a050c0714090106211104090e07150f092106060e07030b01093503040602 63
    0x281c60031007291000300c052400c40d0020300800343c041010142103c41c4031060241d0000d952503000807080184444080840440c051400c0003a005c51150040000b19000e200d15019025940e0000d9071100001040000040801102c0b6019036000354480708950b55080008040c241c100004282161050080320458601c2d00a80aa070050100b168660010003000140a201d1401000c01c4041c054144020202d940100f00390140030f1086058a600120070402c82d40d371f041c0e07038900b0020102902c01d030040c0a0b040c1400041480350107050003544100c645044102480380e2440c002d00140040020100c15810401002501c415580100b5860003a0800a015202e14205c41c500801c02c446c220076060014801903004240d0b0060940011680800b60402c5110744111200030a2910003070f00a100301c4c81c100c00401c0e803007200d0765003070302c00c95042e1402c101c1d40160000564410700c1c0c51058048060700c4042100702070b01d1251515400e1510041c9411010104580250958200d501300700f0060707000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 316611762 1250 316610512 316610527
    0x3020909070e0909030c0d050714160e0705181003060305030a031508010e0a0210030b15030a050907150c020102010902060729070f0f20010501080c01020f070302010305061801030602 80
    0x500d550f550403600d0a0001c518240c40a00f040740c85015005401d030030301601003010818002100054400b5a55000603601c604640e0004421044824010b00c12041c00b0900050b0020340035104442030903d08085801c98202c8840402100102110b041c00806844074000000110104040d211140e401d4030702282d050000ca031900740c1100d007039010003556814801c0304e0450210108072200c03003a03015030b000214100044015405800c000c01c15076040081c0c5c0700340f040381014400c082c6016031500d8805002544403000030030703a240b00c5401640c0c0100b804410034014a4041c03022070480300c0c4180008103213070a154001031000d8100c142c09540042d00001c00c142001c1c0c2046040c0f00d82a038424240540f420803003070041420000f2003100c1706000e15041d0400c056030040c040c0d032a02032040054021000705e41c006142c0a44420301c43e4200303070710a0301001c0d00d2960010448041c3c4401701001080c050749190011405008042d0007541c01c2100c1691420110350a10800c6010314098400580d44c1c2c0d0701c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 316613012 1250 316611762 316611769
    0x30f1509050a2909061b0720060f0301030503091c110603150604181112060d0204061211120c0915010315090506031005041a0c0903010204081e01052503020909070e 72
    0x2100451480b110104110120002303401c05000d00e40b41c4030a0240d51002d40549002c0791061160340d030540e00c0c285c004800001001000001007002ca80140c801607208611220070042d40041900003c14078204104241118140783d40610ba100704121800e4000610081c0450001d90060300b014003101f100019413040c1c01581d000c1c483c241d4040c0c050b00c604d000d01c8400440a505805010107104092102c860b005555032500715174058009031440d51058102c0d8a0a44d030520005903186000b002c281888901611000c28007113640c0802605042c000e03500c4001403400c0180504005060603540c0c104400b800891648000c050448424002000d0412104042c600b1001801d00ea0415040104110020f1084600090411300603002c8800342d0f21201241c4c0c0a0b4050003501a07015032002c41d0002d6206000280300b40000c031401d055401000450a045003a1034044912030105010101400e03004009103202d00301041c8245801800c00b00001e000803000b28090f034050000840e1084410914034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 316614262 1250 316613012 316613041
    0x50d110910081e06030d05090a0510180506090f12070e04030903140303040c17010b1909050f070e010f093c0f21020a030f1509050a290906 61
    0x180b081041107400d01c0c4c0900083c2d960440950283d04005010031312088079140c1701260805010001c0008800740150314000b4188000e01d044807859250b00000003c4c503007070030720466160880160040d070050999106104410024035184603a80c89071100002e811071a002141c1d004900c40d80d12080d0807451800d04024144034200402d20540042061000003248415540111030218080c4012401030310b17012401410840300d21754019007407007001108010010443c0096805c20042003285845400b0034004d0388030102c1d003500110340d4032042c0c2030a9600a03072015804418905c0c9c1800341c940c6a4041d2003940c03440114a044003003c90b810591000c0b06440d15000003500881d03422469803800700c04440410b0703d40301c0d2003c14a244814101c00d03902030800d000c0b81907000303040703150620340d2880c05003000400c41800755140030187c3c122114815950140106664001005001c1c130380f640d0b03ca1810001007081c640f550b07607090790403200300000034040ea28824400b0390b003c1d0001d03140c0301e03000542c1c42 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 316615512 1250 316614262 316614301
    0x40c08070b0a0c031e020705120703110409023f0a0309140102070f120519050309130f09030f02060907081f02090312130e07050d11091008 61
    0x6400c0010288820314080068454900c01ca103840ca0705407609050a0b0340511194481d81306402d082d9079800c5003aa0000380b488100e80090f9407034584011004032180d01d400450000030001d004100e8071001c02e00d49038000e000800c0c0001c0c00c010703040c0404181070108015040140c01c00b0114801c41d4400d20700b407510201200c01c00c220241001c46480d40c0c009110300400e006a030100f407450000700d89582d108024a01c05051041d46424039503480b245410705200701c11100b19928442c0c4d17000042c40c800303d0100384446560050041d03040c40505403c001407410050b503000105956503010b030074507001500400f914030340a80c880000302205028007e060a400905100711b40c0e0251008100d800c03400640c031a0600c10032000c0d06650704844a02c03101922503408241d42c544154429a034803030071060000c0c41d8030034038407900361100742d61000000c68240c412500340000c1202071100524502164000407800a69903003030701c1c5400d020100050f0030070082d009020010383d610f01005090000208900b203003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 316616762 1250 316615512 316615529
    0xc0b070905030a060f06270f02070201051c0f050a020a02060105010305070c0308060a09060e15010e0a09150503160e09012a02010e010c0f12091502070804120308040c 73
    0x1803a080c200800daa4a011040044c0050b07525040d07000c88005581c0050050980c0700700144007510010940f40c01880603080d02c00040e80380118244404142e44200d03140300783d041e12402d080401c00d079055080001c003014143c84d000c1d02c9008090b000c0040340b042078842c1c2045240141c40d40e000c00002440c20005030400c3e81894a07040a108a403a01708012402045d450b14080300e035a03543c2c0d03011549991540e03001040c0e59090100115100301c850100e540300b0b021007265011b04540000c011a20954204000381d004a1490018000b01d050b607081100d030304590709004500c255490022034035102100d107004852030001e020900002c032120024641289860000303000702104c040000c1405904002c005d00c600c80d410340420810b074002c0d007258030500b00f034100030009024590800f4000c80041346082c0002030f01602e00c284949614828803005a40155806400080790182d8400139030110505442212040c031000503614000800c10f003060384a5030324114941050702e4049010100354000c20030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 316618012 1250 316616762 316616777
    0x50c1302190f091806120b0f0c030f010306020c0a20010e0103020c100b030f010203070903021807021b1c150b031f0902010306121115130308090a0e070c0b07 69
    0x9846034801e03400f006a89101240358012581d90541c50010510386c0d002d2180740f903d201442e4103019841000601c584400100844180c0d02c0f0942400c4c6407001b01e500c070b4426183c600042c00441c0f550f034068000440d0407421203038013242d291103070308014810300c5000041c1c2c11400c40240081d40d114420500008007805e095080884503d111904e5030b02412282c03034010783d2512650140c0d5020813158000140482c002c40d501d04003900000d046005600050f40140003c1c03601050580002e040d65208044560103410503500d285403101d51503d0403600c2551040060310585501190603844182991140b041c00081550101e9840c0503280300b44070141c031039003100c01d407000300750b403001d0030718800320b418040000350342002c1e10050f0014a5035801c03e0b44101c80152402d8200940b01c89416400d460448440540d101e11500ca0f204620511031b1940361500724280400000f040800504058030000f0050000103440310b9004084c050100c4081002880d03a0005030180107032044003e4010300700345400780 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 316619262 1250 316618012 316618037
    0x90a1a0f0102030f03130b0f09010c0507050c090411031203270d261603050603060601020a110d050d050414031501050d17030705091921050c130219 65
    0x3e40b01c0c00344c0d00003403900c0b800000000302030901d900300c400e0107658030801904050508407000400724400b15030341c0e52030303619207160322900a00650660340c89541c018000c0c1041641001440102c460150003207030304d0620b004021080b07030b8043c00300c410480400882c149e20f919018403510440c1c0c0d504141100a03140300e001c85c1419041c040b44800c0c8810880c1000304881240003005ea050100d0352401c6440e2801401c10f00c014441917054100e203200b0f69680a1006440d03031800c154403507006950325070140c1e019602420002d50000d4001180380780c020b00061541203652101824445040310000c00944002800d000b002003403118600c034954260001c10755005a2040d08805d4001806101e00c40c1a0710f102d0482000300d07004040784040e4030032802e04e07160309089101a00b0781c2c00c60b5081b180701e910861001e113030380c5051002d41c1080f6018a0040a960300204445035401812a0000c2e40d907401040b006101d0381d25028130054665202c000e0069a03200c030790218a40411030381c0d06502c10810b01c104c40340e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 316620512 1250 316619262 316619267
    0x20901020606102a06060612051b0328020c0105010e0108010903090e06040e0a030302130801050f071b0c08071d070c02011d090406060509090703120c030e090a1a0f01 73
    0xc40900d00d0301110080e8241c074141c91030355041131000c020405428507801140f401d83c001c2544540303100001e02070115440d00c8020315491b15400250280b062014800291034204252100043c5814005290b851540e051115000d81c0d1010381e945950769140d0340100001424544070368010f04090000b0804034610b59002443c14141d0703c190744a03480e00300c01041c10380d0303503e61110718082003190480360403410300c0c030f0045d0182d00040c10a000d034103001103002402c224103010344d900c655040400034000b0b03500c0d02e4080e28005080380c101054000340c440204000b5400001540140a03220300810805242090311303004c95110038481803500d0a160203000000da003100e0613203901c0358242000b83c101c3d4081010072401410f55504158081400d5090105001e03480d032001050712000c1da06c000f0380c0c1d035a0100f00f6075205803510006010340c04255400c04881e00c01e9910454940c0705c1e14103400766090b080006007583d203080c1c0b0003030441584c0d0110180294a440d0030064490030543d02e480e801071151001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 316621762 1250 316620512 316620527
    0x10b03041a0403051614060105010509091f050907030501030b06010e031c12020d02030402040e010c0219060209090c09030f1902061b1c1b0f02060c0c03010e0102090102060610 77
    0x25100d41d4140200442d08250040d419250340c09904416004040141e040440ca10703d66906010704601409002048d1544036000300c811103070010384203aa858440c01e00300c80c403074252141103511074510001d01181e10ba8801560501a5074995070205a039415814440c90381c610160041c1d041c084030b6035a01c6043d841c0454021001c404160811540340a041d0040d40d0708003031000c5901c0c407644000380a0580003404ea0145000740d0003134030100810300c0440b851600722841c0380c21200c056030102c520809140c80a00b07440c5e2405105440140c14143c01c940451175a81d410348030360b07450190100d40078119043c1080a03003a8003940710000c2c01ca080c44aa019450041403d0029001d1038000030031082400b034010a5220401c95401241c407440141031034100f400c510303520141d0000e0031103a403a02e1081015030601c45115041095518002c10584c200103145e0b1218040b02e006014007000b41006940a1140e280040d000d400096601c1c2142c2000a0030b140c1c0082500d0310504101c20014405c2c0d40c40541c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 316623012 1250 316621762 316621793
    0x50607080d180b060d2d170403030915052104031d06031617010e090609070602031812010510150201020f03060105090a0b0c030d0f0506010c02041104120c030308010b0304 75
    0xf15060552414100003084100c00042c01d00303002c6c03249000d01804d0400508224103940504000790040781c64080c4d030b08082c400c520010b0009421140140131304003142426a04030b038500c2c18014645030840b400c0071041c104000058208a0440080209141d0810f0005030000300e007040d44044035440800080316400003504100c5031142c0c1d036104400c01401144011074109400ea0700044c55a520700c0c4401403440304403801000360103010089995400d0010f094001e403130b02900074600b01900f4144040b00c0c107681c0048158011000d5000c6d000141d801e100d802d007c0c5024803014600d05050540906140403601c005d003045a104000d12203009501106486c0c10460901e045030303994200b00005180400d040d00f003070302c03005400038074940d010754004010207401940300740078404089444000c000329441103c1160100b005d0024080c01458071754401648403264018007801c0c5921000070040401c083c1c80110381f8811030300c0041c410f05402448960040c101da2608501e9860190343c0c00c0480741c8940e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 316624262 1250 316623012 316623019
    0x1f110a0c03080a0b030f07050102280807230c0f0607030203040e130b190f0b03030a1821050606030a02060415020a12020114060108010501021b0a050607080d180b06 72
    0x2004180c1d10940c6402034950044c0c010b080307409a280545801d030b141c1860b03110b101e001d0710949a8209a80181c1c02c0c2c191040c002610864604020035100d02c0300c168491502124076100c0340e8601034018036810b503d5910703450318500409146180308140000d0380c1400d080300e80301e210140031590000380c2c0041221300b900c1c07040341c0d8003a0070788460030603d640c1549114001c00b140700c1c81d000c2041c0c0c3d01d46800004c1000d40d0040c01400300500080b0a0710458051101c0c80d038064104000c19105103009984100c4030342d0709166122151a80c3e0031845281c04910644001900d890320003800601008000081e04490300314040c100310111640041c80c20312540c456003030380c454401034100350f05000744170410801307802540031486040c0c03a0000900030315580e07400358180c0d03400300045400c1d5407044142c41c1c16168182c0062228110064070203015200000c0a00da02105800e40400c031030701c0d1040a0030000744644c0060781c44000703503007800302942d146896101c0d51820890b0b0300c80200b154900143e0b001102507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 316625512 1250 316624262 316624277
    0xf090905030705010221150d11030705040507170903131509050616060e010b0f0105090a050a060503100e07120c1803051b01052703030c1f110a0c03 65
    0x500e8040d0035402012006000ca510104d0342e200340641500c824411510300c15480310b03143c1d642c0d5666042044060701c2a580104020914800240314190341c00d43d910b40050890b5070b170941e0386000070151601281c0c040000f904454003e203026110703c2c03500c0d8200e50100061402c10f10300010b8440e4182c1188100009900c0159061210a006002113406054060311440e035501c02a240b040d2200c1c11f0710b104950f91454002240150441842180d8048a00604c8121500c42d010300441c1c80e900980c075803941c40b06000e0743c000f074199911003a1000410780c50700c03250384a00d408840340303240000f182e02c4040c18222032020850715561210740180815625000040d2012822100b19070b25224403c81d441211036108001c000d0007000200c4105200c05208081401c4200350011200c600a032505800303803998014014041219a00c220114110090100c90401c12204100d81c0f41540a07a01d4449141c0c4800c824000030344680a44030840104980e010b140c41e0362250010320341158400c0280411489 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 316626762 1250 316625512 316625531
    0x40b0f090c2106010f11060c0d0f0203090a06060503060403020a1719020c040b10090e1503031201140901050619030f092d2d1523010f09 60
    0x50805442c26001c1d030402060b4054155800459500419902c09022450050b08503015900c5500340340090004240608a5a102c4110780803894005000e1401c00c44e032101c1a078a03103034900348007641c4140811401401c0f01c00da02e0820702c08849040c4c0045010340c00200800c40440d800140d410003035540040c1503180b00b100350341c1c00d41c02405070300d007500911070480015040407640090380704c007401401c9508200307608c0900100072640040c4509103000c259540380400200a2100c14141c1c0803007000590b8100012070800281154440302c0e0b8192002e90000060204011002c000b14807600245c805003015410b000014880c0e0043c064030b9041500354044143c3d02900c01d800ca40a10341090109000108161401943e440e11500d4028101c02c08030040c3c0c80041050f070201125542c2103a044461805681d0303001c04001c1000d0060041c903d0700311004400100105120740c0744544064001030807440108107401d100810007d030840d407500c418010300c40c40141115400484020190001d040f070300b03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 316628012 1250 316626762 316626781
    0x30509040f0c0c050106080106140112090615140a060509040e0f06130302010b03030316050f090a09060302040c1425061103160903051f0b12030405040b040b0f09 71
    0xc03262100781955040c2241003a20710f412074021010684184024464252280e500d24201e8800d4414040c062403c0034000846502900200c064408005004150b0000703940300c030000c2d1820302c00080c4002c81c140754100b002c0c8005101440c50000100e83c1c070b1440a14040001700140110404d0611441d5251140351400e1000c11403c0450400c0c1e800745c17510303440c0c40c1036102d00703655442200740c001d5402d180c521342d014503000c0b0481b442400c503034003010848040780c081159250061aa600c080d01000c028865843d0340d081c501d000180b03080040480c10328150710500c0b0a40710760036400c01c14130000d80c0700c80b180503556000361001a061180c42045140d58141d4602c0300c04050344010b000e980c40c0c61410241e016451000350320904400c4582c1d000380c51001d0301200c3e003900f0f5102c01b50458100e10000c101803002806030651b44040d01101041a103105030015001c000010000e4190798130005003001079007031600450070b011004590070440c0c00003030004a0840c00b0140c3c0c40364030440d224000554042e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 316629262 1250 316628012 316628021
    0x30b030a0b0f070201140105090423100204150206150402030703061a09040c020d120c09051305070807140d0b0303120f0708012c04080906070f1b030c0303050904 71
    0xd40003841d41020b81004088000300a4040d214400194280700d00488100e0b0445001030407501c029006121941c3c840d250422040e1036801d41c0c00d246c060f807100139042800b00704041801001101c4005035150714098070301a0341c04a5000b81c000799082042045000800140040c4000e1000d41d8050b1b5070356103c074421001007103640c203c0c651008000241090001803031024180081d0103840030820303850705800680e62184901841070020322402d180e080f403141141c00184100c01c00d41400b458280c3c80f4000100c04000351402450342540e42da0030054030641c042170598000c03078035003002c00c503038140f5060950207032082e1044494240e8039020002c0c00c90f00c0810444400c585960b004045a0500c0c0c083c1b148406d10943c0c0300740000d941c10b800485c0c3d96880c10041741c090303a0048090105000c0141301082410707002003044d5465401448015400d440300c8008021581c4240b4603803000d81007514244c581d07070060040408055030415001d0000070f42c180d00d07141c03c1d250107051040c0c844408000240140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 316630512 1250 316629262 316629283
    0x1e02031017151608060d150213090b22020c15010b0a030c0e0f1e09130b06180114120106080f010e03040602070e15030106031a1317090301020c060f0106090807030210030b03 76
    0x45d480068840400270700c08404100740d032030400c1c0038064000101d0800068001c0c0021410702d10300e8080316030289086030b81c010480c10231140c1c151a61032450342d042d0302d00c0b04005d034800881c1c80030001d403c0b0440380e0716100780c1040f1480d50400400040300f000104051104252809028900c580c40003280040b4400b440d481c56200188443e101d843c102c50030850711044a9012a203c4902001040c56443d01e54510070390f0700e100c41080121030b0302c1c14034001030707800c405e00c025500040c44110064450401f1302500e000707800d4140061003500003c5101c54216001c40050785010740051100b440403e50105070041150781c0c4920594194a402c1050024240e0f40c80341035605610f4200c0010400000c1895891350320715140c00e00c43c440e03031041c1340c0c03800d842d4010034020400140104108021042600544407240000d4001418542001100c900c2c2100c20366800c04841f440c5001080b003194171208102c00780510030040e107a217a02d140d0104c1c2103424240204414181c45004290f000d8404100f4800b42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 316631762 1250 316630512 316630553
    0xf010c0e120109121214010807030210170402130902031006061403060a06031515030f050a09120522030b010e100303080f130803040605010302131e02031017151608060d 74
    0x26175944203408c1e50b4407501403104074050305075022138070907083c081c00102208980c10407110f4100e0b41d17942d0804c00270100c5d844000e46041c0c1e507070009401603282040300e1403880110003030000301c1500f0718001a0104080d45a08000c06004004000213921041480c07421541641004201c50312000010300c011105900401280e20400b0310000d144c0b94160040c420701c0b07040e20004c200315102d41621405483c2c62a0015020b9012031400080b4a4407907001462900c80e84901c4c44003000b080300c458074403504507500641d0f03240f61400c01400300142081e00641c0201d400400710311400c2c076640d405001440011b0200b00210944e200203900542d15521001c1c0980d4010300c001d82e40d11b07040c503011000300b8083c00180d00522001540c0140090188101c400c0394407821a041e9602030704203808000f079400108038080f1b03e4595200007440c035110840c3c1d80000450200503041d5818040c960400240c001444181e407405610700d00d40419402c010590303041402075030043c40428160801803600580e8000c0d9551 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 316633012 1250 316631762 316631801
    0x6050f0d0201021f02120a050610180f3003020601140a030b0405030a031a03030f0d1401030311010506040b0a06080a09080d06180e19050f010c0e1201091212 69
    0x994038005d600811a074002880c0b0715031585c13245601d41040f194119041500140941070704c09001d801110310550180c2925a00001d060700c40d80201c0d4907001ca6070113034128194800150034400b000541003903045180c5209003141800545000399104010320640c003441441742200c034100c0e1a0f600e8020041d581020b03107120340c2e00f41468215600d501c95101c0d07400007882c00740d664036800080c1e43c4548580d00300a00560030800315010320f0300785038000c010840b0101e80d03842d9a88950342201c07440600841c02510f4588003c0207407414582034500c01014603124924009481d4496907403484c0103801d481003803600002d6980c501200000400040c6000303040a000032030040001c0581d50071001c1a03641c411080c0c01c3c0d55203808134010944040960303d407019041038060810b2241744071507072100c860149040380c081d000b80702202402c440010b80c480000522220b5442141d05000d10b070881c41c95400e40007044248125200d04031280c080c20111402c200f400020800e502c00d13203400460400812401400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 316634262 1250 316633012 316633063
    0x60f0219020d1407240f08010602030a030e010e01110304020a0614030703020304050a05010e06010810050c03060904020112020418050c0a020a020609010e15070210081009110d0c12050a06050f0d020102 88
    0x38a185c0351040c4000070803018804444501c2444041d040390f6207900110b0400040c00c1040e4050044110b19401c0e03503503598401c5030844401d005441c1e003500042d030401d55a041500500c030305644d00d07800c0001400016584240e10040d0041100c0d130004c0c00c0e181c01a1240c03100e151a030304103001c1e014050019030801c280c40d0001030000c01c4050403a04585c04903650485e0300620b600c01d603041241c0d45400f40d0820700010b50075040044000340d01910501d400c80c400203000b01d00008030303006034006d000030103114407035940107a405200707482c0c21034240c03c00a410500c0075400255507000684009001d00340100b81e1800c075034000c18400c0c41501d0700074140d03000c3c104940b0038544141c100310300aa200d446107803080000c0034055410940600640400c00c01c00d45e040c076076181d001d800300d101780351910303081009001f954200b1840b81004082d802c2c1c0e9020000311604499030161440030380501c0c0e07454a0a08200300f80d42c0c0702d1160810005080d40d001c60481d9943c00142e0601e405565620100002030700c0381c0c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 316635512 1250 316634262 316634309
    0xb060f072d06060e0603010b032a030607111b130c18170c04021611060d0c08100b03090a06050c13061e03050606041206060906060f0219020d1407 64
    0x5030a13103c464020140030f6130390000701400d9807003041c4601c0c1c042d005681c101d103e40c0010100c024001808982c0003a140800d480824545481101e0100002d045a10407003d0607000b03212030314805801407180040c3c802e02200084940c10001c3c80d00e4089580e03840c01e21411402421400c000243c44100904440d544a00401e5044039581c084103080c0168603400c10350745070034801d4907603001c405c00b0130500c4019150ba076020701e10415000207610884c14406001c10101b43c1c06079640c00b0207990303a10200d80c20110b41441c9212819040740202c0c1800317200b0800d10342c50003c2e41902c060303081180411a80c41c0c40c0001c1d0391500c51950305101d103054200f4007265041d003280058070440300305007e804a413004401c0480131204152010313540f240e0b041004000b5802c054882010041c00341800080c101d40d00d00c0100c0454a49a01040201d486c3c04980388000350140b080301144404e000b410321445049500103000c4041c022801007880c8a5101c1c01c202d00402040000040d041070000035a8081454814 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 316636762 1250 316635512 316635521
    0xa050c152e0306060f30020904060f0911011b0314090111060a050717070f080a0b10180602010509060a02280519030b010f110a0c090f0b060f072d06 65
    0xb00442c091030035001440312400c1921011402d0356501c81b0818000380303582080f400d000e02400c00d0b51415200c0200074151a441d100300c000d0a482040202d580d040380c02c00240c0158211310041414069140d11140401d4115800c000406d10720f1300720700c1e5500a0b02c4010703a800061804040c0e018072a0a080040f0015540d0009002d038400f03844006078524400300c0c0013880481110250700085825a150040710302a40c401a00100f0740c11000c03440c28100008030340041c100400c60400102d05404110a0080322035008015180c140f000380322614004091a9a03001d025210840c05640040c94848140c000d035010b01e1071014030341c1c44580da10002100100300f44c0080c1100018040f1035001b10108500a128000701440103031107001e540d5841807003d564103042158010494003d400c24100080c040c5903800c4054000c41900040035541500080101e5111a20a43c01901e08201c0e031394500485d40306440c1101e0340140c1c01151101e20000b6109010b101c008840030170340c6446006020090309030403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 316638012 1250 316636762 316636769
    0x61201060e222019080604020409020c0726070b030c0c1e0c0406050904030809031905031006020a020108010308130b031e060f13090c05060a050c152e0306060f 70
    0x5403c0d00e105401c04100034425a81c0d80b4240c00300a01c90305940740c1c000c001955001900620042c2040c3c0d9450304981a41d000d4500014903803c00c074418400ca00c2d4200180010921000d016001d100d0420101a0f07544d409000c3c00c1c4c12940007000107020113042e84129011032909100707540c00b2080e54003400070203541040c3c52124a00811030f0a03041805d1074803400d0110750008008070041c1d00c03552429102d410018000c0c2625010170032119130740f20740306144003440450f240e44c2d1035030784d103845400c030403000721150401021034220010407000350303078800c0c100781c1501e800c074900f161b5031403240200150425807a4030403005184048200308076801c424101e507500c001c03e00d41d60101c6946600c10400c500980e40803083e0f100c0d045804c440c0c00c400c4141d014411151242d098880102d1300c9100280d9903030840d8030000001140003c0058543c4c03030038400854107a85218004145041000700780c1d20307049603032124148070745485041c2c211042e2007824440095802c5002081065141c00003032211010902 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 316639262 1250 316638012 316638041
    0x90303090806070519140f04050f09011427040b0916081011090303070b091225030c020a15030b030a201315090b061201060e22 56
    0x600001e01400042a0903100f00c0c60356407518a04100d5042603810f032180003c641c010042c00308590f82183e100003008044030700f0601c041c2a00c9501e06020015180c1c0c2000000e03024018020042008484031201311031041c1e01100e030050b0f181780040f14401c2d4424001c0d01c542c0b100204100348014011501c2c0315500a10702c2c081521490720043ca07042d00480390a03c1001082e80c0182c82e000e0168940341c0c0602c0c0c0348000e1031079a0b4070300b40d5090002482d6401440c01a100d40d1130680c00d0180445041022001e40c0d8002c60b015400c0c41070a40e600101c017444411000080717001c119a000405228448101e50700d42d005105211941e01c5021b540c2c101e1041c482c602021a240c5042000d241c5400558541003d40c4050040b00d078000c0b40c41103100052000031070b20342100809100c0c1d008100780b400395000010004e1a0b55407141e140c482c820301030b02d500b034900c580606410807a80400c65400d114141c1501c50b20b0074640484019400030407040c007a80c0052002c00ca440d20480700c113142194128268010500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 316640512 1250 316639262 316639277
    0x40f03030e0d1a0a090501060e060103060e010e15150d05040b0711100e1f1406041e0504031e030204032603011e030c030503191407030309081306090303 67
    0x84050124002c42c0c084041c040c1101c405120b401c802035695100d900801c60040401c9440103a61118251000364211348002e8502804200107035905114010003072005025681e595403405c10520b80800010f007000e1105140250b00d9980c0b61900c01d00c204200440c00c0c802c5948200c44804030b4024503080da030071a8035095000200f40744910903601c0c6180900040302405100044071030344001003c141707201180500401a01e6140314100312801007504400c00c0c4082030420000e003030700d241c000004181902c40c40c0780003801d040401411000303024510f140480002e8944031400c0c1035945e001c24034007028802c85400185407040c0c0d4550041c00c2142c0c4514140c2d80034040004c50080c0410f01c030700612a914400b400100310601c46040ca401d10a2a1100440141d603100d440b0b01015012640007a241540005455000c1c0845000d820b05145400c0c43d00504080348080074602901c50600702804160f160141c0380103010700c9904a074107203a5072407000b03031034560790b443c0140948440e48400d5010403c0c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 316641762 1250 316640512 316640537
    0x1170403051e091c2108010e1e0105060c0f06010f0305070906033c061a04060501050d0209040b09040b010602060108030f07020d03121d0d090803090d0215040f0303 72
    0x103807066410f220310042002c1d039851081c40002c0722141000360107940e24515003507030b00468415260042c6014400e41d856031060f43c14400752010380b000141c0683c152042c58407030011f0765008060481d054800c1122041c0c2c3e1944003402d01d0303281c44051001400305010f06030000905510403001001103910035800d407140d10b580e580f441011180184070240030715030348c0a50b490189010b8180e1882008440c54040025000b00460950140f154041141c43d26505c81c122490300024648001d00030604480601006040c04002805809221443c140300c40c0c010855408581c0c80b6007102c541d0040180507944249003504041d20820400e10a00c07003d4018000003040180d40401110602c0180100c0140b8100c459424065094424901603040040d802c10703410852074540aa1407105054183c920300800da1500302d14182110300c1c0100c01840005902000f002101205680b0204000c8510800550b20360000c1040180b0350b99002c12843c5002601048105902d201641501d000381d0391340703c1021300d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 316643012 1250 316641762 316641817
    0x503121005041d030f1303050609060612010e210903062409070c0b070e12010e0d111b01050f071b091e09050c04150e0703060e0c090117040305 63
    0xc640d00346411a81081101045a4480c5d90040043d41d0030002c10500b0156030b038503218144a426160b80225410035000c3c4079052801790304441c0414201030003005046d074201d05d501c1d40c0c0c422001446114214140024010140c00e1040d100540406420f881f42c42c6000d000c0803e024040c9a400b01000302007040c04011411700b5900c080c41401039403204198450380703881d02003403100700500700c600304800ea04804880d0b48a000c0c82a8228070803000110f200202170b02014101511b4244e59000c007c80c1d4081c1c4c0c2c940c5c000010b5003641d103002040d00640358000d941d0040b24240724011340c210310340900064174010000e03c861030746181c00f10030301c40b425030300e444203980000e0b60100c148000c91400030240791004410a035104020312803041088403280751000020038241c44030b49602085000c0046010403010b29502149548590540b03410030495040103045e209280c030140000e48810804540344120f64041c0c0c0d5440132120742035500b03400600c1c0030700c1d0040130795200d40c0b8122000045483c2c503810389103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 316644262 1250 316643012 316643051
    0x19150c081006020d09032612061203030601020d1107150903030e0a24020c090c0403030815030601030f0f1a072c011202040b0c010e0f0f0c0607050312100504 69
    0x104581d281c5c910b0a01c0c60319061621030f540d241c00c10a00514905071b4401d48000c400070704451079900c2000000745454030420051a003441c05036001c42d00300b0070801c2056a400b040c001005281c0e420050440440c01c0203ca02e801080e07004807002d002d00500440010f13401240742821284031f035581151f440750910500c8468101481190002c01d030711403100c242c400118085e8500c1811610440c1c160915850005400305c000f50351028240000040a0040c91361280700f840d032110310002820080703050940843d03a11001444003604010848214104110f1071040c02c10f49190400180e9091245840240d1611501664414003003215448040f0390800501d20fa004000c0c03003112601040700b00c100064805046030010401019800c101c00700d005031920018102c0e900c5100c1c0001088502e60020070b19051007200d614050f83c0c00402c61209000c40020006842c00065501c1034548019140092650160400d81c1759030b021807a04000e01900b10901c08411103108503030030301948917139421590210 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 316645512 1250 316644262 316644283
    0x90702010606020a03050c03090907030c02010e07030b010e09100f060e01140904080c0f070902041d04120f120f090b0a020a05031302010509031006050103050a020c19150c08100602 79
    0x5070041da1101300801c0c001c901500c0c0c1c941d00401920301e491405800283c0400c4100c0e40c1e0f00100741c2c0d9405031031030341d64244613a403110089200202000b03030940d2600e9101c5c10b414443d00840c2c40d0048002210094240a00e0641c64a1310000388641d04510610070040d20b0140203159248428400009001e200040690700b40d141c003405c0c80c6019120340e25000303040c0c0c0c09036024841c0c920680c128058507900822402004000e1042c0040e20385c1d050241102045038020174502102c4108020700c40412026a10840008100d050100c032166a0301d40503034142004000642c1071034a07040340041d0185194100d9041241b0802d00c40c1019500c10704508101e0240c01003500000310284002540d03586419984100c55005046c81c500301030391040024903210000d0151002991105402c11041d41c143c000c0540000b5400419420300c5040310400d9601c040c02c020500803090085500d8080c40503140e2035904010000406004044000c9000741112405486c4100f42c02c460355800110700740b0200300b110b0348 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 316646762 1250 316645512 316645517
    0x5070903020d031107080d0309300309030c080301091b0f0203040e100807031211010c0c02061c0f02180a1a070311010203151f05090d05011806020306090702010606 72
    0x711038680c9040b1359886141003410514441c9550214030350383c2c100f02c001c401c02c0040e907000c2040241460301051142000200103e4080441982e091380902c003111071645003002d01e00054030508608044404200f5900090b100c100008004510141d8030741020030398440040b41c1c002d14a80c8424111b072010101954040141c000b44411f00000413400026a00038209441312844aa101c01d211810070f00617910490f02c56000c03107003410f481c1d038103d0106400020341038001c00003541c040e070000d0042110044000d100702d40003d6550502e4494810301c0c60f000b0b181e034008101048015500900a5102c21f0304e0030148401c0b507411101d50300c5d001c0444419950b0400408030b14018440001280c0c0d0046442102800400704120641030b1092000d548585421020f600586106400303010140136900c10b9210100312907015008143d400204407014411300317840c16481c1c420719045c8180109851500104001c07503080c161020f10000c0d4025500448045504880320345030f02c2e1050f802c0340d0813442504003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 316648012 1250 316646762 316646779
    0x15010b0903011d0a26072a031209090209030c0103020a02280308330301021b07060314090c0f0609040c0804030f0f0206150f03031b010507090302 64
    0x948100001404011001400101d8982c0c04107a0b109030000025103080000e030b10400200742805004800e80604241d000c612680811901c40e0f200700510810f10f02901c0f0a61800255007018000c0c0d5041d0035500c00c00764501001c540360f1030030f01e00750040200290005600d01101080104032031080710841400180100501c8030900b0040d000380d000b040c022401c0d4014880d1341c4044da00458200100c4070001c013070303000350020245000380c420a070151289000300a00c3c1c417008c07400e0f940804440c503100300701000229564401c100280c0640b15900f05c040d07028602c43c03092000038000003140e0042e1000d58a00740000c215a100d8041200c07011a02d03a0059404003080e1041418898050002d407003002e4403091400c0382034000f0a040e00d41088801c0c1c00280e04d241084185607110702c40c00d015900f6482d040540300203075400259101c0002d021107040140310107184440b590780540078400c08102806403510740507108058192040c0c0c03040648030b55400d0000050f03541d4420750110050366801010501c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 316649262 1250 316648012 316648019
    0x3130f0c091b1e0c02150304031e051e0415171503071a090a030b0714040609061b0615080c0406030b01090b1206010b070213090f030c0809040507030209030607021501 73
    0x400500c18010f01000c0c460188001d802588600700004490543c00040654a04240c0350003008900e1240081c0e809111400a80c5985940b03c02118008024124804c40c1d04020601149052285a00903100707040c6c0d501c094000960401c4a554100d004070601295075034030f03500b64000201c2071030050360741034004103018001c1d074003d5040c0204948042180710305260442c400f09032080002e800c15650120003404100b50780354019078107080010328607501e80c101860110f02a000a00358001c01c01440030a40c108062800f15041e21401e094000070240003840c0f80b6038983d13010549502034610705001c0ca8042e98810304090154404680d03120150f4007a5070703e040c070614000c01c0100c080e1a809500089140035884040084501134062448a00d40ea010980b04020300138401c4072101c6590303400e040d4070101051014200361025a01804c0001644555161481d501d10440e940c10703034030502d4070003848072455066000d04108401901165403d8541040c181da40b50307080b42542c40c0e00f4140701e0052 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 316650512 1250 316649262 316649297
    0x80301170309060d0603112b020102010207080415090906060503150103090f03260c040504020c160f030311010e100c030e07031104050601051204030503130f0c091b 72
    0x80d00c014034440680c2e003059400c4000540e55400101c4403000540c036500180248902101058490301040311003880003c04000ca213550030322118206001c00312540821000d40e4002e40485070710b00e80c440403d0b076580703448034442da540860f00059140054080e800c0801c25403014401c42c0156035494658605559030104050085604130724110f04050320f40000c00300081c1c1c585005a40144203881708000c02d81d000c07a014846c0321b0011401c40700300e4030030320a005100c580f840445007070710010781c0e0141c1e59240311440e0380d1805ea1440e07020030642c0036503800002d031202034011920035a40f2942c0c4445c000100c08080328262580d40c54a00440e80107808125a03c1d02c3c1903110400f060001d0034041841140036500314288411030340281d4480241100c240f62030311345442010341c445000d00b00b41341820210141004842401003008092002c000042400401301101d2140003907408000701300124060b00c0d180c2e0420100d8440c948056081c400c40c0d40c2ca861529201540080c02540c410010f0804403000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 316651762 1250 316650512 316650539
    0x1200f0306041a09040c052b0210030605060c0c010e06070209060d031e02010b0a0e1608040501090f050d0305060103110708030408043b06010c1b05041b02120403080301 74
    0x2031075000f40c814401011039444064507548a180110300c1d00300410720b0002408041405401c101d048030340100c0c0c29000c08082c4200510b003aa805450440e401c0c43c1d944001d800400c2d0b16049554004408031b0402516000090f40d050a003200303a0340d07065071110078070601c0682c0c0140800203602c502550b001528500b07207180c0340300046001e0b20388003039059140d461421500021075445001030351650700b000b0305410310b8410071004000c00b04070030003986031011400b207034094044003450401888201090601c0025004901c4ad00e0300320103811030780b55040c5400ca42d9568110300042c0030a040000003403456000c0d200e190082c45211070754a02c0d04246a5940b60b056000420440e41c0f010b05000104d58000c2050320b640d0802080080782070000042a50400202418811000515941ca08101959a0003d80c0020b0749901080070130300c3c1d407001007044007070101540049801518140c441103100501e281410010300c20750302034400e540740400c000503203440340d8040540078010400040200c226030340c92 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 316653012 1250 316651762 316651781
    0x70602010b06040e1501200705011103070305030105130b0a0902120a05100501050702031018021905030c040f021e0d060b16120c1e0b060f030a02040e010b04050901200f030604 77
    0x1001c1845164500c43d05899031004500c01f41c083c0c0c0000801c0c815560450740c3c120500da0140021410449185c1e0001c0c5507200501600e03004000f146814a01030326290841000503d00900814903151100381c50030083d00403805220640c1c281d48007007290110184030b42805917002c3c0e16009180760805005491991140b802244c062180341801c25440d007191041203211070744d4400d103000c0c1c010700c2d0040194207901c244021000e039010784010803050b6400078014110300020b550114072a5450807484d4001d020741d10950390340c0030f08140c0c81c80814504030003c00346100b6100c01008104d032038051980307160043e600c0d02010718600001300404580644010042003e0510f00100341da581540d540030891080c030f4105007901d5014483e007042282100d42680d108a0a403100c11080c54400c3c002607442c095818041d002c0d80d56041032043d0750400f9000100548800741003481542072102509008000100504850070b02031202c542c00c07610204202c07030512424076805411038442d2401c000080c4500c15 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 316654262 1250 316653012 316653017
    0x1091a040308030f1b03100e0403091503090312020c03160807080a020c0405070807020a0605070504080304080705040b0402070c14060d18030e060a021b030c0303040305070602010b06040e1501 84
    0x100001c001812000118420700701340c81024030b241401c442c915640085100c000c503400c8010b000300b00e0301e04201002c4004131841d4511800f440c0c1c98500301a15101210b4100445851054070074520598042c0c000f140e80511907510881c01d01904d0328408200d000749040008950020030100852002d8020307400389550050040d10f00d040c0c09661502e28a9002c05038240140e005142001c03c945068420645e00c800300e424400d1240c13804c0c000007500d42c00c160200034a040c0d9500d02180310288a40d0036500030740111000c40b80d460740c5a039040d5681f040648640391103203041c0b841c2a0960705160007940c0301e03176500c00890312419003403011020b00b030b0102072001900150f06110402a14409000c1d4103041301c1060107589400e880d908004100050301510b40340240c0d8200180aa1203500143d500c0480a51901038a400c641e51000a0300b800f482c0c1c188154103200214000c001e000c0d010804800b01c542a8000700030681000c0180412801144118652200c1c5080041c040c1c0c004031a02c600360683c1407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 316655512 1250 316654262 316654267
    0xf09020c070f0f090f0204030f0303020a0c02151308011107020d150216050d08090303060f180106031e05040819030b19060e01110c04150b0309030a081501091a 70
    0x1070070403142c003038080e5000310040d11004408100c800103611500c00300b0950000258685407c646503c1c0c400b0302003800044c201a40000d02903440c0348110042051117500510071079000e4a0201c0848958100040c030450303c90f420800041c2c0b1000c14880d01c0c0c5084010b0380f145081c010ba507020010010300761348007580e403641d524568201c07440942c40107100c440b05008d00090010180e042603843c2545150740380080c8041902032012403100002500e51040048030061130004141c0302066000c5030800407030242c416102c0011503880e8044d0095a80b05407c410100340581c0003040050036280c0648002d0404c0c1410403d40828000d44509000340405a09010a0031650040400c0c10748088869040350324a68503003e001180d4000302c944521802480c05000040603c040300f0380380c40b0000d4150344182e82d0b4000d2001540003a41d00c840040626016075a1203140c00c0c08641d071298170102c04600011854000590b080d0280400e1a201c400186c5d692540207080600b0000010350404c000c03040442e09 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 316656762 1250 316655512 316655519
    0xc0e04080f19031b12020c0114090f01150308040504090804171f02040b090910030f030801080c010804050a0b10170f0106060c050307030e130509060414070f09020c07 73
    0x80c1008101401466080301c080d20402e00004003107808a202ca28031524100068009090b0b02103810820f03005013990040e55090380c514900e004100c2400c0745415141240e040008070640460340303010034140c074002800703110343c1f80c1000a80d41e41140001007042e4070900080c0000e003801d80c050b030b0550b4482c403405480c107600d40c1044000d200340884070b5103107940f0401d02c10b40e0300580204e840b0741d820700011041d81090b0611045503124011354260034080c00c5000000703841c84800c0340c415030042d600b240103095842d24508008141c0c050074040c5041c0c5119640008045500c1046250710071078100c00a010301810b181d454050070800580350b8031080781c0741180459a402541128601844640002c100e0b0800c1e60018900303480003613001a05110f600040e00c0c003c604044100c44000d54945800e1100c001c20500240307405465541d0031100398580002c1000c41200040c00500850003061954464602e003c0f00381da88003100d001c3c108800d154140704010204564010304034410585007610311141c6c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 316658012 1250 316656762 316656787
    0xe0a06091101031a21070b1303060606020303010303050322080a0201060e06040b030703080d02070c0f051206070f2006040b06010908010c0503011202010e03120301051503040c0e0408 80
    0x400103860100d00140e8509440da018031540a80d5039014404102038880440094000b005004a1012241d11007149031171015080c800100030f03283c3c05d25815110f02014608410082e040c1c0030444005191000215883d8000000c1c0da040300d9242c1c1d01c80386036030350b15849141c00200c488880c40c3c03400c1c4410f0f8103400045051001d0030480d0160341c00002c0c1d81d4948031a8200054006c3e012601461600007503070501d0b10081040001d41c2d4010030100e60f980303000003400000342b10300c0c3e6020b066030100b11030105101c5c4814610f0805c848048810288019a0f0350820743c40748019030700c2d031021525641141004501035200c9400e11045940600c000c042004201030a001c0b01700c80855150b40d0a0007000074a682002c05c1402905140000300840640c2c85800b0303105120600402c0421107400c9074103011a8881c1c01001c1e1801c101401351146103c010200001d035410a000f007a201c4d944401500340b10340041f13010390f071040f40c01410301410540703481d030382d01d40100018105460040d41008603084004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 316659262 1250 316658012 316658021
    0x60f0f0706050a020901020c0d0b04030f120207050304030b0f3606150306131a2d09060c1c0506060f04170d050705060a0c050405120a02040e010506130e0a06 69
    0x40e80c1e03030f015036200d9403000024101310300f10312000d1107000020941c0c0045920082502e900c01da150520003135034058414203036058082c20540007825800000d0304020010040003400807240b04004c1e128098840722a9403211000449004030000003492102250409202d11840b560550311300c4460744020750100a801c1150450302082c0018a00c2e141c0c14a9007000c1100c02c2e40054611242d148106070760740d5420342010700c8007064220700054400308101c0c030351140450f0304443c43d00020380004462010303164002c28088030084201c0c010100041d0380b5030300c450101e0307000030072450381c1c03030a840d40c04804500203080240c0010341080080c0400004003803444001c0004e000031049246801c100d10820a14083d0280695000c2082c144003000016034002900b03a0801106030340401e401100c088212018003985c0d2046600240c00f0100c103200e00030204020b04200d00a50707092007000004030900342601c40c240c41c0c0a0300185080200c0010300c2d43d952084500c0841181035a00c00607c0d038444000344c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 316660512 1250 316659262 316659271
    0x6210304030b010f050402070201050a0c0515160f020d090909080d05010807080c04020f0304062021010b040303020a031b0c06091e030c0513060e0a06030312020702060f0f070605 78
    0x15034100b00180002c01015010100914003154150310b496441d0740000d10030f0158000e410b00344030340d00003a5410424144130907080c10350305440000c064503160014130703190b460310070340240824200050020300a201285241900d43c84e40c998400107880e00741c0c00801040d400034151841c25082c81403c08155075405110b0003006041300802460f1308182103a4185448000c01910031031040001c1402c41c0141415254065040040000c11110b82e10b0b118184000024a984500200141d4070a407201c480d450b884021100c4034140c0410782c3c8032258130120b031286000240140e407000311088006441451000d4900c070200c030b100c0000f10f00a64944005001907003000010030301c05c3c101400780c0c10200200c01d03100100c1c031600c1102c851550b00c131010342c02d40740c0c080e181c010741d4030040403580710f04d00c0c2c0c0000000780781540c854180c0d4584450003c0c01064203000403400101e2409a40380012072500985450a400a207000c0c9448002c2824580540c880043d40403881d80522075280070626500c03071948207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 316661762 1250 316660512 316660523
    0x60c06150602030a020d030c20030c1c0306050109050310180614150609091b0c0a1109010b0f0307050a030b030d03060612180602030402061308071d0f0621030403 71
    0x130b548411078041c1c144a0041c400400b058500089610b22a03406100d2605203000b07841a131440c1545403540500794455101c1141d031508c29801c030308020ba44103503908458580d032036508002480d142c6004489a050920400d50301d82d204003450280b41070306074070143c48003106948025500b0129503528050f83c81300750142080042d42010841544088086050424021900349151449100010301d140713502a046441c0b02c119180342c040d82c0b203150402c65031104440c0d01101c0140c101494414041c0c91212029801102c1a100002d0300d5260102902c48005409990380d0442da602c00048070a508480b480c034080607140c007028852a1801d000d503030803514681d0ba010992904100d000b03001c03841400b0301d82c09607601d13058a0f012000340f4080340030900f80e442000503030b8030780703460000900300d02a54400d0501c0c40a200d00004ea80701002808804075028849001c820492402c03072140404030840d42020720140d501c00040c400c0c6060701f0b0b1420120040340c101200c5076003001c0405d1960b0440d4008590 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 316663012 1250 316661762 316661767
    0x40b0406030f0606091503030512100f080127020a09050705070b0f0a0b10051206060d060f0812040311091902040602030d060906050d0b180d030f0b04090c060c0615060203 75
    0x407031007240510785086d00700000e007005051465900500d5486000100082031303403001c02080c1c5205209a0300b5004143c41000342c842140c4070b4114a00030f0290301e10700803402031840410280b102c400c2c090120070540040112583c24900880c42006d48402401c08040040400a580000b10700c0c0d0452802000d03902511005440c103032217100102c0740080ca45500c50640c2b08918421560310400300c0d01182ca050786180681c0d00e4450100d03400d4007491140b00c00c4c0c541000004030340006a4003021017103e41000c00c0358031a41402e0403005043c4914000640002c2070040c2d00384103414071300c10306904a4100c0b1290710b4960500090482282c1294000700c005030800120322180703030100c5c09264040e0560b0f1004000c850702c0c0c01c0000707580581b280c000078025500c01d000900031100c2c0401d20561109841c0070350f00c03c00d079807100050060506100c00d00c4464944042d030809801d180c82100841ca034401e01e020115820440191070103413240d10f0840f8155190b030144d99861650800040041519400442c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 316664262 1250 316663012 316663019
    0x10e0a0f0303050906061f110102040b12070c0c03030309020310050403020f070e090c0904030c05060c03041401020a0c08220305030c2e0914010c08060405060f030c040b0406030f0606 80
    0xb425030300080c0c4500000e0740010141300710f5564409001511461104841f5680d0041d22002d6400404004000c0c1072540f010800003010202c4000a01c0059540300c074500f1166100c0d801075882c901200c001610803505001c0c01c0c00000c0c081d51103424030340d0004044400e40c01c10800d0348401d44600312402c6006030013aa04c01802d1100c10007090002d0b04000704881c4040c41c0070400035a85030509002d0a101c0d0004401140c10305014104001c5416000130a646842c98007050f004c4e80ba501c2940c0407583e1b925480d02c50310800e00e0600c0ad9a080c1d40e541d540d02d8003440c0e01500c0310b94981d00300c020340520002d40c54000000814020b1b0b401d100451255001d19190a00496424185813440440c814085001e2940300040c2c4056000d4808800003543c0c00a150906c1d820318801541d12144100d032103602e0f108400b4001c03500311540c14881e000448090116035100300501c00400c047ca51000d800d640144d0304603000345001c0e00b00e08100c1001400001380655603486540d120115610152441c540d28601070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 316665512 1250 316664262 316664267
    0x3060902070507150e090604051f030305220602060a0c18121506080a0f2102010515010e100e060c190c082e060906230406050a1205010e0a0f03 63
    0x104140c44e01070600400707506007440481c840c6800142070600c1039560b180044e44201248050140452003594800007140e240e241c0a0b20f164060340e801044d404403e0048424502000c0000c0140d50440d4050081030711040081d034050042d00741c4000070b10101c6c1100009400070750388880000c0c0080001700c2281c001d0fa00308011141d801c0003628440509089060140910002e00b9603c0f079a0b100b110400c0040007410440130600540d01480e4280b422058200a0f840d41508880c0c052944683c40c180c054400c0c00040d01c3d0011080b1410303400035040244083c1150003a000c141034910302800c01c910b418444683c01d810484402d8000c0806030744160300c6c0c8103204143e00c8134005048040700502056480340c0385000001c9045181400c03808564807107501a509a802550081c11403400c00d110705511025085c240042d02c0d40c00f107241c1641000c0c0400d15191600681d001c803100689114506070030f18400720400e0266103001d80c0c0d299229802c0d03003040a41003118001450241005100c041510310f1300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 316666762 1250 316665512 316665539
    0x10c02010b0f04090c0630050609060102010e06180102040b0703080106081e010506070501090b040b091002090901051207031b05040f0c02060c0318030418060608100306090303060902070507 83
    0x10075005928049500b03001404803850300c0c080d1b52050170900c2640300c810700d2810016280001141600080c6500740c1c2c1011802d0700185d01900b4110b034000d00658900c0c004a080310382400c5440d405511100204800011200c003011000b44000000341c80c182d1200460051503203c00e0044000804050041101550100c4000d81100e50320508402c14011540c10080541040c01800c0c4074a000040c1c1d1020014250321004400f0340c03001600000e0701d007908002504280c00c442001c118002c06c110141026020702c22aa0a4000145050b0b816404c2070203000f0601c0404004050b2445a41004000b2800700603641c861007a403000c075076040904020921007550708600d40c07032000c0341c00c00d420141469008202d0b2031303000c401500050b4491740c07214803c08492200c030982900501000601141400026010030121060000c1c10301085640703c01c1120f00307030701c102c030414078115500c1d40600000b000354002603102c50213841c02007482d54840030030401301c1c1c2c080b5604440359030181c5010811046032490 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 316668012 1250 316666762 316666789
    0x1107022e020d020607120207051b0102100c0c0b0c07050601150314010b0901181805060307050913060f110c030c0f1225120903140706050a18030203010c02010b 70
    0x10304120b680444019545181c00f600c080103000701e9880080c42c030122a416245010b0f0000c0c1242d81a8004100003102d9001801415005014240380d10512040d940224021581c250742c415a48001d19111042003401c0a80201407040040058001281080180d41e028021240e0703040d10103550700300c000e000c44040c10f21848090b103200c4010044000c46030256102e880f420300b0705550000c00e02da00070030404404d8000440500d8005141100201c0c00d600c141d03c148819000c4a01e400e440c2d6080120030001154030351b06820310348980b40700007104cad034000082010001c0c401103201c0300400c1200f00305800a02400d143c0d075101146001c5805801c00004441c03519240c003401420a406c0c0039158140b00310031301c0324200d0311903409124180080f41c150340c5000c0e8210000e04d04202996900510000c65440140c45c501100200d611102d100411200c084a069440b4507150140022007130f40d654541ca009a01548110000000580c41c2030140c0c0911400030381c00010b440320784c80c0401603502403102 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 316669262 1250 316668012 316668017
    0x905010b0d05040c09020d0b0111070b0a18080106170d030e06070309031b0605061002030a1d18090106061d0618030712051e1f1107022e 60
    0x14010849110031804660629956030030114043ea510309042c5507480300c9900040000c0d00c00641408440081d900824042c3c41c01d0340c9003a00700054480e8030380c0e184090300851543c594108440320507180108003132003600c0d0040d0310b040c0300310780d41c0ea45a6003140d032580c3c0030f00c5c0c0038209104011071f03040046c4425040401c55007001c0200051008200399920360040001040c540e5500404082c5030081c00040080d040300b401d090380250361841e1131b0001c0c1c0401c2e1582c601816002c0001c840603030022007034038184c0c4007580c4c40044c0711f1358a00c1c5c45103e401d001c1d00c200d600000d4502e201c2e0702e41000d10170f0080c03042d01b4107000420b5043c60400c5c014403914100c59010000c0f00304c02812200c079910001158501c4c0810b51019220140ea8000642040c086e94000c2c0400841e5030120020020003060201d001703082d0b007013a8450200c1c00050b041c0c9503003c8084014100c803032001580c68402e1103a0103501011480020141060752a501140c62483c94540340c560135980340700c22624215241c0303150a00c414491 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 316670512 1250 316669262 316669271
    0x1009091203110309070501050319110a0f02030304050a02010302030a090605090f070501020c0604031b1502070329040b09070b0f03011e0501050d0c120614010f0905150919060809060109 81
    0x100c4d4a9101d031020b015680c100500080800c10301101d00c0014012104200c100f0040c000030300d41c10740656408440104081080e6046400b8418004403d0f24402c0380c011002c1c1c01c00310016801140294402004800c200e0b0741d800d46100800e100d80314252055800340010308c000a94070120500d0000250300c01411075011401d45011780d00d40700c00f540c0c21030742c0c07149004078425080320300b0740128812608004040c048020110051f00e41c0060304104a0b40541d0703c144110042011114040d1800c201080142c41fa480100340050121140d19a10094400586050781e840d2240da20855220b03d81c8044c25480220052140d5110621110050f50000440054082c80e05002821901030030040c02c000c40da4404004402a01407401c0c40b0b42c2040703059040200d13a403201100030900b0051002d142c00030b0300c1240280c02150140040100340c4100400e034070300b450004000191103034820030f5400e401c200400e00102000e16040300382d9010700802d0700c8155092038481c0d0894500541640199003807401d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 316671762 1250 316670512 316670521
    0x91509020f0a080a23060d300e150d0b06030711060a0203040f02090a14010b0c0f0105042303040b0403050a030f1805010c08070b09011e06140910090912031103 70
    0x100005141e91001c1c62501176240e0b00c2c580091081943c83c403024064482465800d038080306940141c00510051014054104000741d101b250020104400190080b2807403480e00c03143c12188002c1c1c07001c482e06680102d807403101a0302090306038005450480101e1594411031054403c03c0c04030315400244a00110300b585010340b210381c8500584c0d00040d015044010108903001d68542000f44920355020301c0c0c0120356034075141c200e03079a03000c2c4003036003014002e001e5202143d80381030003040d00854100810411408100c12103030f0702c011040c1031034074061000300000206809034001500046007e0070203014031036140d00b8007070312003100c446001c01041803044040100d045040c041e5802c0d15002c0ca080c61a14013a4941305040f4421404060070782c074182d108014202c0015000242040103900034446c9a404110001094a1590251000c1d0503240b80c8140400e040c840106a800907109101c011507641d1010540210b0b40840c0f0162800442030031000e82040d00750140300303039694010784c1691031480c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 316673012 1250 316671762 316671791
    0x4080118050717070e01060f030515090105100e0d06020a030e030307121107050610030203011a150a020106180506152503030e10060305060109020a020601091509020f0a080a 76
    0x142809001c50595005605040c000f10401202001c3c00740904084081e5860300005001e2012888580c0002814100042c40908000c40544105400074040c00616402d01c0c1c10400000200c1c1140030800c01180152041d60b51049001814203006034001a82c842d010f41004080d24501181290160300070418010710a500c00d200c0c501c503500220700003c1c800d00681c9004010f1083c8540504148982030522200303082e10003610b41124821002000100c00c0520603010300501241c0c3c4680c814400c40750803201055080081011408500c00003031401e4480d030003008520802d103081c1d0000703991042000843d05084042c81e9507076680251003030420101e00e44a80d21004918401940c2d48900085101010b0180c0c105206075400c07c01940e61410564142c0c10040c0700034803054646118000c000590802140f00702e80110440341c0c0500010382c20302544c00301030000003074400e545070030300880003400c4c125920150442b40703030700c92009940c1c0c1582080180450720241150f580380f231400404054008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 316674262 1250 316673012 316673023
    0xf0812070305130b04060e0415060c0303090c08060c03040510110714150c0a080630070807061e0918090804080105040b091002131215060b0408011805 66
    0x5500d490401e40e2070048070f0304400020070079488501d503d01c001c100465215008203822a4080c07060fa420410904005180c9007511100d110f2803001c034030398001c01801f1a1003900060a120300504140c1c0c0201d540390052840d0000898003500206c0c404018032081210030300403041c482804010910140c2089408102e2510803070343c0041003880502d8058079036090500428402c07142d008106402443c1c00c4505585960100100c04000384078000040d9041c40c200525902c043d51800f02080101c0100f001c08000c260480c804420900c5072610010300b0385000c0101001070302c429075441c42c00642c00c4001440c00d089000005040c800e44d004240b0249c1040314800407510301c100c070301040e54589814031401d01d11032504200119406c18042100748083d03420441c1c000c040c4c4004035503c29a044502604070b000d14034401e00300d407100d5001006808a258481585280944043d038a80110304813154201c03185540b0000d4034400105040181d95028404c07500c60402e01005800c203ca0640da0f01c944a4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 316675512 1250 316674262 316674277
    0x1103031305010b100203090301060501050f030604050403170a41070e12060f0112080301030807081210051306060905040e0c030708061f05030604020d021c0305040f0812 74
    0x140030180492092110940026600000161402c14071000b0070000075203903444284624040d60a100300000c85520a004440b4802e03000502c1c2403c2d600c4680c00c002c054540a8425400c100d02e403200d0058a254074040d0500a00208038001809408074507003001101c00800d000c0021b00205400317071148175203184490b01e00340008a01c2003c690b140700090740d01ca0700b000c1c01a50001195800d00844400018201f400340c6840c3ca41086030b41e80e00d1100c0d124241107084d00500c1580c00340010000034804001601e840392042850508000843e009004046411652000040c0b240780e0700300814203110380c1040380810101c0c000e01c8124146100030b07100000d02e11031240a5983c42003407507160340c414016107502d000004c0656650681d90310f03d0740e684980950707405088031841181c43d42c00981074a0b004044580280141042c3e940300e03020000c0500c02c4400a80c1c0151810411000541c03d050010280328440c2c0c0710180c442c1d0805005106100b030319044004c0e254030a000240714002c500d016200310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 316676762 1250 316675512 316675531
    0x1060c020d06200f03011e0b0711030a0f050a0201030f0e0c091510120c0513091802190311030d0212160605100303030b011701090b0d151506110303 65
    0x81c00c04400f641d11101c00d142d462502406408107841140682c4440214100e51801030b4000c1507500509031600c3d100303081d01c0348601e1404104222400600010310340301140038010f060360103039000e5450302c80712408210303001c0311250041e41c0c1c860115078261141c1340c681400c5080804c0300c0f40c40c0c0c942c1c941e40c441c40d01ca0110303c81c1c42d5010000d90345010414205c0301c0d01c030000e8040f2031106401500a0014000072022130354076410003246100701e500ca28140e4900c8003000d011100c1003403405100d100180300fa0010005070000380b00300200035032555070700068684444540d2040303652640c02c1034a036007604d04030080d03c6078110b00f15003508180e00054150f442104c143d009546c4800c0744000100c2d21030f250300000d11f03080c288003c001c2e140380080c0e06501201e020340c500344602030b0240b0044908044a5034a0003158a040c0018044105039920041e600c50f40500020b20100050b00c0322000460340809824100d40c07907440f08120b600140c880000104164213200c2c3d030a10820040310703103e01004052901 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 316678012 1250 316676762 316676771
    0x2512020d06020703020a170906030403050901030e01060602070614030903032809120e04021c0b040f0501030b04020f0a030c0614041e0608160909200f090901060c020d06 74
    0x150355440d8034000d880c81d4031100443d940e10303561070041c0d154070700b004003940c500700007201d1010fa4100d90803c0350341d0032000401052540c1e4996800fa03945400c10003c107810541d990380a100711100910840c0c1c003406003500240b211901d001c0004000c420440301001411005205008810000006407600708513141c2244000c0e04001c5800303007580110128500180c0d0411103140240640c0704120301074000d03165205114030700c3d0141440180c0c810441a0680200901d100b01e4504046038006110420010000b240f5501e00441903c00e0324020381050f41c1e01d008000600c011440e00078a5821802c82c25102903144600c1c40e1683e8108442d41e00c52002070021614900c1104200300044901074551003a40c9140c0c05500200e50061300820f015400c080740204010030b4510340f10f0400d10b1041007441e682e043c101da0a02034100c01800c001400e11518a8282c140c180e051021400680440180c0340d800944401c2000100042c400301a486581840300d01c4100501503114060044125900a43d0105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 316679262 1250 316678012 316678049
    0xf040312050906120906060405061e15070602040503060601021204290a0509040b010e030d0e0406032414040201050306010810050a17060f151002070504020a05070525 73
    0x1d80d1807003820322855003d500002c40010061001040501940402c81180c00c0f075a10701060008550040c0d441e40c5d4406012207003c440d041100310042c160100c0a4000704065a62100d22003040c0c0012200710703102a00410240300c141802c00030550b0200c000d100400c0c204608031540c2130140b1a0380646588400810170012030021100d08507460400611882c9654000b1041c4c0282507400040302e1910176420040105090740c40b4961001c10340c040200580050401d0074400d03a03060910401d415000340d20b44a0001c0070074403e800d4002140b07001404c4203221444010404116885500c954009095000501026076401000d40c2e500440c20f003031001164540e01c45841084041e80d0001d0342c8000e80c40008110100704010110401c2c1d05401211103980701c1c41e03080c40710b203036045030300814443c590700601c01d107840c0c402c4121060381121b0058801031501c500200e4141d0340070450100100c0c0b4001a1001040000c2019903c460b9003640e01d0000601070441e21204045180b08041c0c001c4a0b54141c1c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 316680512 1250 316679262 316679267
    0x4030809240103060506150301121a090c010f0201091109070c051002130b1c0207020607060c050a0908161a0903030412021503190906141f0b0f040312 66
    0xc01c14800700710300340700d1040503041e500d4090724240022960581032201003089414049400401c1c00c1070a0507041c1560300340710584d203180568800a840003c1c1d0308044d0701c0388001d103402441c06002500e001d0149a03003568009000762074a882c500c400c5a24280e201802305d8a0010703110b040620441d00d00c12a6281c100044132034000c4e014000d802801020204049a652075009180d2210300d800304000c075075aa440a12200d000c0d01c0b1500c0141b4101c420220701c082c03103e50041079101d00c010714550600c8801c0c0c071a00215419560114080358000800f14000c036000500c8800402d0381000610404038498440003000d1403070710a00300c4074080081602d0300020041c0c1920680640941240c1d02e440d510084000345d01b020a401340c0c007d0202645580b88060014104c9104140050307a0700034024054054000404199806441c0c0f669602c0c02d1100520800100c0340c0180710b8000c1c041c100c0e540d101f85e0964217a01c2540643e410000810090240d1011142a1001c4a40141501c2ca840c02d042c1020f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 316681762 1250 316680512 316680523
    0xe1c11060c1b01020615030601090504031107090b040b061912020f0d0618091e050319020f06091b0d0809100f12200310030503181207050904030809 65
    0x315086401200c02d5802c8055120070152142c0c1c009a0846000d0707180c41c40e001e40c0c20000080c1090305500810014068103805800c001e0f040340c800d2500c061a04800000d460a144154000c004490f032280d04414483c0f03482d00446060204c216501841d1114560340401d102c1e241441e044140000d071603800b000800183d0550302c20011b903c0500d60390ba034000d031402c0b005040500481c0041c11144042c11040180c903c91082003582c484011140e480a000d264281034103210310880d4948820840c01822a400744108030020301c641e0000e000703201c40c040c0b07090f0900324000c0985000d60300c4050348a01110500c2040b00c0035200039148450400b0150418010f01c1c4128074007290004d110b40d20395051194041005240000700c1d50b00c4100c10940012090166003030b2078403001030601c0c8400c10121101c0d100c00115045076100c1c40d03012850340c2d20b589290543c1c1000100302c581c0c050b405404401410440b501d2603c40f440017000c0e02529042c200003038103092015001404102200001505d140c0d0704010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 316683012 1250 316681762 316681777
    0x4020d020901080c09010801150506220b04140f130c0917060f0f0123010e030d0315050a050d081b07030f061d0c0103020a090915060e1c1106 62
    0x4016076581c49030a8240d8802c80250000e0050910700000110b03a5810311401c4882011790410b070001500c3c1004002c4160055a01d03401c0d513072800d0411a40f010740700072102c0300420000074087d48441c5465040320b0b01000340e06205018120301c0b03c025030a541e031290445840400407000140e07851360140100d0f506980341e0003000e42c0c007001c6070220108000010b0405e21039103071030540b44090750b1140c9154a030008223114402d18181091440440c0444032543d5506605040c9050350705580e2520020f0310b058074211302e800100740c0d6001030720228040810342c8006048241c0701c001c412450800400c5241009181c09000310402041446244203111000100c40980d81e081b21074182c0c40e41402e00020020f1101101c4851030310902003c0340880018002a0000400c040c0c203049045000550295000c40048070401068103404108507015100f680800841c0c20401460b42d03007007280c01390408411000441c030454409014029034400ca0904004180d4001c6000041034821004100390f40213a40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 316684262 1250 316683012 316683019
    0x20a150213031a04051c17040218070c0c0605070302070b030402150703030e160e1918031709010506092202150a021204081e070302030f030403050d03140f04020d02 72
    0x841e182c0e070079a5007071943d0b0056000d007066403c3c18800c09184000954100369032000f15013039404058101c070150349140d03070280c005010a03000030700c0d820841e8503004044440c500490b900311521001e00c682c215280c8007405075410014138020b900e44010f076071031446e0301c0f40350602a03000002808545a071002d806242d04188191900c901c143d00d000f5024081c0b080e10400c90303100b065580407815100342c00410444809050307100c425220303010882d10130364903054508409500c4044d501c00100d03240c881441a0f070300a66841e44161541c48a0150b07070a00500100d403140c1c10070050090320380d2910811604198ac4183c0c03205c0d00d12046000005422503048081d51110380741c2c604034001078a01c002090442c0e466802e81d001e520301109428038900a6003c0e55500b5400710702e440048200d503484400c0075a581d2070440702c2d01d40c0d03a580000d29000070207510000940000c2410003c101007003240c2c03100c03800c0c2c90074240485005004409500a8010401e80c03c0e420380c03101041c00e548a008521003c00c0c0c015 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 316685512 1250 316684262 316684283
    0x30c030e120712061104180e0309010c080901030b090c0901020f0c100f120c09052d28030c0f0603020c03070b06060d0509010e12090f0103050402130207050c0f01020a15021303 77
    0x810003070821491f0089090b2007103050080812148001100b240c66003901610740b200c49030210f44582030503400501c0d04a040c0342e514415941d565071500381940c41040a0322113990344000d000b000a04004800c40c50603000d50210581074850b5488203c45500e1100f9483c00350076601900d40c04440f158143e2400c2c6041a00d44030800d0b52980c2d0140d0800d00341d600c1950303580420034098440c824644801003d280050a03030010070141440c0c0051904070284101409104174001038110000498182d481102c69002d0a50100070403801a0b0f000e000501e2030782021030030010110751880c1c591140da00000c01c2092a200042c0341d5a4848042d00d00031011008100030030320344003032124028190500c108001c0d200307007064040f1b440c0c140e00495541346030282031300006c6445d440041d00a014040e0080f42c3c004c02d8210384149480c0640f010b011490b000310000c1c81e454a52405101580c0700545070350303045400144018010940800d60071011582c0d0010050b03a4401d2001c400a241d11590401071008030349 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 316686762 1250 316685512 316685519
    0x90108150c120f04140a12050c0a080d05040b0603072d090c180830040e04030302030a15080303040b09100906090c05060c0604080304080f0403030c030e120712061104 73
    0xa507080d04d104911428180d1101c00b2404003082d40d907801610000d0120103026807142c800740c82039028140000e000c0c001c8581c100d85507a113200c0f4035004180030040d00f81d1388804000078003a0510940e50400d0003a4003030311941c0d040ca1225071085414040c928140071108d9a4a011226000c810b44005c0481d040100440101180f0040c070010a99050702d92000805501044a110124001702e405007401520701110707161081c4141c1c154161075100980b92020722000070b2891034105014402e40c429640184c1c4e074504070008004441c000c000340748801010380760520150030004116500260040500f00c0c0c030b03030ba606802030f103000d0300e404510b220181002d0311201000a181c00c10003456125910a860064a800602c0380342c4c001d0582c6040a540560003040210f43c20000460300280103c1e0b03a039191400d0b42610184540c01503001f1800100003110f40c0d400c2c581d0222501050309411130f403404030300500850481d074032043d6006202614006948250400034039511102c0c182e021040034584481c3d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 316688012 1250 316686762 316686781
    0x270606040e0106053f010801020a02070324060b040f061b0b04020d0210090906090504030509010c06060e010b0307031833140f010f06021209010c2001030b090108150c12 74
    0x524407175200d41c40c2180d0001c622000180240c440e2003040d40e00511110f40303583c403100c0f40f00c1400e1400103000c5042c00070314002c4113564040c0d40b001e080304c09403455645183c5a004008001194800310422400b56010307202c1c0c0510210391807030326411440c03107206600c0358000100c0c04801030307500a500c8200021030400d0350b0340154840c3d04076080524100f10495071354428809880d01240d009000810801c03001180d5801005290081c0d402000c0020304241c4510703040e1010319003a00281c00c0304c0808800c00c11420b5250242030003003030700b49407139408840b5141d4400c142880c450100c501e60140351307002942004584080851600c1c1e0429040c40783e41101102c4041907413007a100913440701540750011412510147d444000c890300c0d0350062464601c0e40a25410580103080d00e18100701c269401000410040c4081c906580b05038041000c5c00c1c000140058100d85100703e46031301582c1c40340b004000504002c60384011010460b2103001c110780d90808810f460784100f00c01616408001e9040c02180728 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 316689262 1250 316688012 316688107
    0x90103030815040b1302130803040f170109030917030d090606090507080f15040e01020706060501091202130513050a050d090b04080327270606040e010605 68
    0x200702c18403a2224540541c1031009441284ca101130300f0071129400c3c2c101e02c1d11180e00901a210303600f00524801d50b142d106503130540e40141c0c41142d240c0d030342040038806036250407001c1c81100301c0d0a008020308011580d000c0c003400c071940700b0300d5005000e103506e003620a401401100d210130781c203560411840b1801d1804030b0040100b4020340c00d02e9481c1400081156019641a40c000c2c900c08007801034550324400d80c6101c4c20024103203030390499114807605d200c000b402d0016140300d921400c408607809042600041000e921a8401185092803161480141e1284007200741000e40c0c80c0c201240725614948900c52401d410180100103104000c0c3c0c00003440000300301001c1200e01a685c07056211340d1080000564042c80c0100d0506800070001c8020312140d10203450741c5a011841440c400300078200014000c0341d1802d00350302d81c04429940d02c0c1e03450340215034840e903c4202114020708060070120f110708411014020403080c0480081c0c07680d44d411008051102c08a0b40480120280c500c0314982004035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 316690512 1250 316689262 316689271
    0x13020a02100c2619110d0207050a02060304052104051005161403072f010c0302070b0a02160f03030503010312030f180b06032e020c07150906050405101d0901030308 72
    0x22000813a040712511078014014800204003070f0038100b601d0f40004c14000e6102d10801c6a1504c140b212060049c0c0751080a180b2550090020f003003100d44a22500030140760f1000c43c2d03104500304000611050743c401294150b040020314116899181038440d100c50781c60002d1000e000e40c4050b040d801c0200c00000005c18100f441100240741303010103080d4119022104d15112540c0c0c0309001c41030440d551040030007040c404e000c1c0c03049030300e0150b550a107062203a00c90042c82c001078200841c2c40381650300c00c041112c014102c4c0009a24060303e903032001403150006010050580024080c8000541e2194020700c60700b105091007003000224098041541604815081720381d1510400004d09607e0007003410182c40c44400694041c000381509014601191052402d849070b07824400356100480400102028103528201800265501c8402806e482065403122040100030802400a511380680720071000c1d1182c100f24446096102003155440c455001e44ca400c4403000000100303140c1e0202059026 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 316691762 1250 316690512 316690531
    0xc0509040804080d03090b0103060504062013050f06040605031003080c06070813020f100c08041421120304110607060609050a0e060c0310030b01060e13020a02100c26 73
    0x540e490400580c280c070b64000c0b024081007185401000405e4039504859483340c800e000004007100e03e401e0020400d2980001408118400302d0700c1800101d14480307443c040c0c14100ca83c880242811301c00520035114a000c2d40c0d0070004044045561901c85881c0c5001860f40084400d4484400c040102c0c1e54038402c03108040024a450301042981c00d424964442054020345158100d040c032005101e107403e1100096420403c1700c0c4100b60100344c81001400c090042446201101c0b60a2010020f07811000c038601820802511070706844000006401c2050381d1413840403580b00d81d11401c1800d00c030b5190540090f000100000c0000401c00d6580c004801d6807480300d810003860b103484c1c0e200012200030b0381440c40103920902c046a00d585680c0302a40c2c1c04a003155111402d6600c980d500d461481003130344010040b552a605940ad00d1508c04014900740220341021800c2c04007150b002035940700450094116607584a042e11001c6201d941101340d6518882105241e11403024a007e49004080340d00050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 316693012 1250 316691762 316691773
    0x120408092e090b030106020d030903141204020906040b01020706140f040303030f0501090e070b030a150b030a0b060a09180e0f030d2906030a060906090b13090510090c050904080408 79
    0x448110f0002603c1c1038401941c028100c5428000c2c0c2a8010410741d14250705000c10341480d8140b89070003c005101c011903211010010781043d10510000020103000d00788500d08021031885181d0340040c110b07080701e6140c0303400565a41030500001540c4544601031340f00c0f050000d00402455019001080e00c0181a88100a66170765814044115500c00c5081c100350b0300202010000d205500d009140c0040740020f00180318000540e41540428645e4088955104088108002c440c424030603604081e1080d0755261600c04c0750710009003807200078054005040a01040c00e1460304c0e40340d21030310003070541030121600240c3c02807a00355681c004004884000d810110f100380c0303c1480034090011000400b6140481d078001c0703420410300d9080142803000959030384a0004081c103490040030300410014600207403805500c02805490b18043c0d48010900d8280702031900041e40015a41120301c13040d400000741c0700700d54940303042c1d4004241d111581c8102400280b0050002e50070041088501c041d04507417 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 316694262 1250 316693012 316693019
    0x60609050a1b08040818130e010b0102100b0315070e0316050a0b0c0303060603040305070b0423060709050f0f040e0708150906040f0201091d010f06020102120408092e09 74
    0xa9a881c003c613801031010300103000320102e0400701c4070803007000714005100c84074401c84e2208000440d01100040e10341691650101d900c6543c05004801140c000098240042800c5c0000700e0354401031141344415100003000012003040c89501400b0307103003e0003000d8034800781c00f04114003140c0c25140604c40c8144040c1d800010280f82c200c0443d111154400c0c003560543c0d60750030801056810040050707051003020000d20000076420100725115038403848500880c0b4440c032183c46650904a130590b4070541c03041c410f01c18002d40003e40c2008891045600d4000400311402155000081d0040640c001e81402115500c2080107d200410346a4600c100e503425407a121500400038020346a402560b0041c0e070100c2c022400c0786280190190040c142100340590710365280341503502441028800d9107900006001041400c1c00341001441f580c4020340c18500d400c403c80d0004880030708002c04014001034601d1081c0c036101e0074411142c018007078812030208504c0702045c1040341901d03034100080b0a0b00020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 316695512 1250 316694262 316694267
    0x60e030312010e09070e040606141c170906120402031603020108161812020109050103060b0f090f0303040602060a141312021608070801110403020d0807060609050a1b 73
    0xa404424044019141d5030740380c40012410700034043c00655882c000c04038003181c1042000422030140e84100800100070340740481e840705400c4500307941840360030a0740d1134443e4440c0900c241c0ca60381c3c0e040b002c41007503140562055510361089440b41c41d00400003050004070712104c22210351145000703506580c00c280144e41c02c05c1182840e804020301140905012503a192102151104440b031603050641003030140c00d40328101408140c1c0708641580c2c917401d880c42196407050216000b00020300b0144851401c0c907001050600416551003102200822030003e560303180800724901c0c1c4009010341c1d581d161607001c002c0d210b0008030348003a911414007850402c41800029518801c0c408841109100d60311aa1080d400440d510000011031140c01e43c03000c0c3c41c1014040c801c005185d60402400000c1c81c1c80000c07800e40d010b244004000780001d000070000350300c5000301c8449082d408064035030303980071f03500e00070008010b15009888200d10700001c200e046001d681c0202000b40c0c44d0101c2c1c0c54036a0042404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 316696762 1250 316695512 316695517
    0xe010b1011150903190c05010204030c0303020d020d090b0708070c031a28020a050d05010b0c0709051303030c020f0d08040c1211010503060d0f080d05060307060e0f01031113060e0303 80
    0x100c3c0c40c5500070080a0010340c490911005482c04601d400d203030084490b100c060981c2c00c41c0e0021f5481e00300d056020400c041c2c042146001511a0340045c20b4864a039801c0509400240d102d1044407500014500040004e4141192051603000544c2c4900b6038490074401e802d09902c0e0991741600f420311000c20b0641c00c90200c60791041102c48101791800c8100031001c07004e5042007000905000040c08041d01030a01809804c5c00f030014095505e8980541140c15850400c466002851180ca0481400a02c110501110300c00d1901802c004c60780300c100c507400700e19141d00b030101c2c5103a40c0108000d00755030a604c1116107019074050f02d1840901d0303480701e0070303912007014801d4010700e025800400c4440550052024640c00714009103095400c1140741c8a409032a4030954049460030f000261203108880036106031600400f0035001401c40609240703029200c0921000024070900000b0f00201d0075070f10a4102ca03407008030201d12291201d1070b00304401e1901285001e444045a05c00e9866815030400000303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 316698012 1250 316696762 316696771
    0x80f0f0708030403030f09152304030507030b13051f0b04020a02032d0703020c04050f07020a031218060b0405011a180a15021515060703030e010b101115 67
    0x10710f241078079640e01a00d00380d4005072041c2c2400030020000070301502000703801d42d5006150311480b00303100140081508420407900c8400440000b40003e2001ca000080e03400c045d41c0d400111a00c1c1c81d1106800507a0110381c2002c002e040d88500c1c026002e041046c00e03204404421440c0052088590020410040c1d00500411100680c000d0110007031070300b003090296a4400f107158024040c08400f540640f0503610440003500580e20107075910300c00c0e041601c03c45503c400b0703083c1460102d007004c80009480b490015005010803018000310058250264002800d15590041141143c0c1c820710b0200098100310b10305620031841c110000400c40c8805140211035204c1200e528540301314110201c81c0c0c88698a03020360082e03014a004914005560841013072280e003a00100b541041801d0112046400146070410038440c0102480840d00c410064840140c4d00d0306022950602c4101c4040c010802d50000b02c2c0e118030241c0c03007a540344d42c00040502c44200d0310348c25200c6440c1e414508607003684007501c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 316699262 1250 316698012 316698029
    0x60603070e06040903110d020d11010504030f051c1803080f09030405190302040504110a2102010f020a2f01020109080405010f050f0423010c0b010504050705040906080f0f07 76
    0x80720b615103a4401070320a8401d040c207070381c004022610a803400d094085c54a0260b40090061403007542c0082e80c0d00702005a880091000c5d15040e0b6005040310400c500050070b1250101d020b403081040c8507415001245d000c40204100c007104010001d10140c4148141c0c0442c0d54040803442040300c62001c54402d18152000754605454001880690341c10340a00c401403050204001c00140d9a41c06210b0140e402800350000060740d00007048403640055200c00030b01c000800c4501000c0038441300441056409087c214062507202d981039050262100c0d000b8060046c8071000880342c00101c4010b0b07402d48112109210b07821800005908030303482158041c10032642400b080010b513100705c4600814100d10700c2c0042c107001e01c1c0c0030190a40e811580007807030140c001c000303030800b4400241486038000307009207424a640412920b4030460040d042c091240510344600000340541d0050044400801003100e00300f10490b920000192203004812003220039019043c46020851030020b03804040c3c4a180 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 316700512 1250 316699262 316699289
    0x7020c030a020f030a080c010f1d060a02070c080105130501050105030c0a0b07080f04060207140607030e0d0804120f0212030c0709050a110c03031b04080a080d02070203061806060307 80
    0x190204045503c441c0182c0780d0500c03072001c244000554203400b80140b541401d001050743e140202e4480d081d90440c1c0c0d2685510b010f0320900300d901080001e0241c3d000b0912500c01a55044a820201e6000c8441d421000403907003011309000d40e01112011041100340034000030091a622007003056260001701000d66400008004180410300b107070001401d03611300c154005840c100720700707108001a41295003c9005a008600308121480c1d000020f9003035040200c1e0810314190840c0c1c0c1c0034004040141c130791030180d8021060b410420014004a502601c045591400515a940340c11085c00c3c081d410101d00986071402a91145900002603510012083e4080c11003141004410002804c0040003065169220b50054072009090130040c95100500d4001e075640703141250000002e223558101c01c030700d5454200403c00c200100420300407030980d80840d1381070762482102e207860f000e401001d40280d414010b46003071051680360010058003400102003554059958403040640b100442d04ca81200603029 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 316701762 1250 316700512 316700533
    0xa050c070318030f15060608071b0f230705090f13030c0c0b0c010c0c0519031815121e1d010e010501090e010209062203080309010504060507020c03 65
    0x544119542e011664000542c010799a032a210400d501c152410f403201c1110040c84400045e141c0640805804503003441c60140c1080c203401030455000c034810f4034118140c007032100304003c450343e150103405400c2074000a40380e040300390002d13040c031080c2c40004080c41402000141c07070070001100b40c070440b01c2402c034100350b03542c1c200c10031540d40b40000100d0401c01d2900e54100080c100b0100700300506070030318141d82c540074520210350031601c41c10004000d0080c9440802c0c0002c00c00111240910006012a1056119890f09889440d050410302100c400c145101040ca00da01c80c0141103e80070b10341d1644039081c00501e0900c210785070315865015414403250034001c07030070054002c072504406282c0c0390420278801c1c20485084490040c0c40c12a00e9440710010010250680180c10406d6010720003103140120050002d074803407045000301c0c0300c5030300d10b103d8140040d044007000b07000850f0411c0d4420b640e49401c841040c02044115000c4031f5071841c0401081210f41300040465004030080c0041c4107400344c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 316703012 1250 316701762 316701767
    0x6030d0804020315010e0f0a090b011503022502040b061806090f0d060e010c02030a120e0102071406010f0f05030303040b0a0e030a02011b1404140f090903070b0a050c0703 75
    0x400400983c1c0600c1004070300d520b02e262407440d5074000c2010021102d020b0030000840710907c8009400616440e0408a107080401e42c00d861940c11a80410700c51004540c1c188000d07400f90160320180806c8606000d030008441c1442011a80703600d20072141002041052410050a80100c55001442c140d079500d50f4622420070700c4c0149403240b0010301d0403d44a51701000a106030f80340c02c0c0e0481d1015140c0002d14030102c024029002c4075103660010b14140b5454803070051040345c11510008074280c4820b03138001e0546083d41101c0c41250010110501c0001c0d102145a5840c800e2281144000e540c200c00107103038020b58008015107400502541c45c43d183c684440f425900c1c040c10380860b06035540801d0742d800e80e040000308059041d9030000304204240d80503419005460780076107414086400074940b20b0280300e008803000d0303a540b103006003030b200175a00c08201e1581d00c0d202150341201e4900b0500440f0400000075224051158104401c181d4038a602c0f0b02c1030360425510287e4400060001c3d000090 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 316704262 1250 316703012 316703027
    0x120b0a11030a0c1812060506010f0e0145210204240f0501020f0c0612040807020303030f1501020c010e0d060b18160e030d05220e1e06030d 61
    0x310701345030400700268400c00742d214821840d4041400403207031164601c00c012160090035844282400c00c42c841d406000301c050201c0801088440c104a071241c0d0740400459282060750040c1140000e40e0342c40c0c0c0d092540c801d030400a545028205c4144801d000400c050b1000c00c03140101650076110001504a5003032002804060365038143d0b00d000d800c085000100c0d48a0f1940007407200c801c0d50300c0401d1521001a085c002041d4150141d50022100000691510340c2103410440700981044140e076510b0a0403100350140c1c0d40029407500001040c4145012031004042c01418003114900340350640b8001039a0382c0e0040034410f80814801804c20038507142c5601c6c4418558020340c80401c9041c2c458000513100102e50b85480406a000300903c0801c0d000c1060341210789034039080103115407041e400020795400340744458108002000400000302c07000c0d5030b0451840320000181e850100d403100a49100c15404880745880b0701010b400c4120380504900c0858001c10010300500700d0350104103021070341d64 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 316705512 1250 316704262 316704281
    0x307020a09110d1a1203090a0b130e1305010504030807090b0903061f030204091a011e051509040c0e0114120f0c0f04080a1b0513090309050a120b0a11030a 68
    0x41d030900c424400c1d1200b9045d1000ba04400e409141c3d100c0c103440400c10300e0416034120309054001030140003042c0c80301c546802d05403080c0000740c0c20039540b50352042e01d10101000c1c0050955080400340001c1503004501180142e0094580c0140c3d10703203481040007903024042000f0760592200300442c003002251034140c008021154017020106440b900498191103040000b203900052114428000d289031103076450140c20040307460100310030608400c0103071207682e00901340f0841003800002008141c21080303881c44080a8403e00141e81130b00400b400240300d05100758086038402d170840100c21096003c41e4440600e13406a59840d4a4040f045541283e000300b00c1d00a208040000041d180700d250f004c0c000805e1b2101c0140049000b600e0607a00e0300142c0b0303104005080c1d0700c950611465556603d01450030a2559000030560203900701122400314561110f90421182c1e00c0108240c0720561003149418015669501d031605c440c42800c0444030400744401c0058428404150307803881c1c580050420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 316706762 1250 316705512 316705541
    0x51e0111070f170c0f0102150c070c0905060301050f10090b2e0912030e0105210a09031805010f050c072301020d030605151c0e0307020a09110d 63
    0x1c958a800540718404503d400402c1000510071284640c1d100070410010440c205548650312080362000103565200c441040200c4a019040000c08070b8036940d055030521500098600c84181ea40c0344100003d01d000c0c0c446c1e6009501344070018403a907580381a014010041180124901450040e80c00000c0503c42286540040d405550110045002c000100b02841c0d4007403a00315049403900107800d6540a6008440414110400401080d0000c0320422600c1c002c0c2000d60391241c0e0264200031f00301050408440391900342090110004403030f44011011486030b15040c50a6078006900c809904c2c462088500107007100078411142d030703c038038060101c501201c41160001c9444864514480c40481c01008c42c4141680e0428115a810030401d600007045080400c5010300784000300f4a01610000c210341c20300800075125608616860005001c00710005041201e01c40301d09032562694418030081e423284040320000700f0a00d40034880c9204058041c004d00b45400144420300340034105407840b2130b51 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 316708012 1250 316706762 316706773
    0x6071706040f0e01050406050f07090501020604141c050a090501050310050d050f01020a020c01080703140718080307050c0414010e0f06060415020c040f0b01140d020403120504050406051e0111 84
    0x303c0c10003400b9050182c5d10526003c900c5103009442907003021002803028007004000700d0100405c0c0d0b0042066504182c1088031400101d84807542c46190000e001d40070004c07242846000c40450b54450050008580c05564400419603920011201d90000341d0b100045803411150401491a01c0502c02d1030040c803c00a03148068480d40c0950300f260000100440543c03c143c400c0721a540e0b200280030b0380000c5505040003078130f1000000e049440d00003000c00703090110081c5e03d10b1144104507906402030001000f102e607644030074541140c89900803003070326005500789622071030901042407201b4181ca0350400440c20f56524182c41041041c000780140e0382000d81004085406000d0800103000502d0700d0300140070503800f41307060104071b401d09415078158510b45405188541c0c0c0c416002a5000c626204807500c540590906600911450f8170050884c080070340340300700413a001030143c800c5810840d4100400d0f0b13511400c2c03100d04100c145101c840b18940d038060040d198098114841c0d8003030184126203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 316709262 1250 316708012 316708031
    0x60e1212310303080609090a0f050c1203040513090b07030902040b04110a08150d08091203030112060e01150504050a0609050c0c07050f060a050d0e07031406071706040f 74
    0x1401a00c0428080716200c004281030040c190080141500320303c007a02c17110201d207061000c207038590ba203074072008103241c0d4007041c9842401000c0100a01c652001401c1249900e04800074507078035806440f445014001402d80c10642443d40d1080c11b040c42e400065115041c0c3d5004402c40c001d1003003540c1203a1081d61001403e1007a00c0764858962200041a2055a203500340c0310090f00031b40e00200b00c01c100c0004680721034080d89445030b242c1c100a03800204991140c80703c3d000070340700710050041c54030903100104c000981c04040b02425a9000d0181d201003020810b03c030a070078280c0390705501e03081e60000c13000410492400c085d80803a5203c484004001013898460000b8400c2d01d0040d116400c440d070f8046204501030700144089802028112074461f40302c440c842c0130444501810f01160240600412072948000d01d981120320b40400c2c0701c05492501da100e01d0b10401e0b10b00342040c00c00080c443c0c540043c05040c000c2c0005418805031102c0250a07645840c20000a403410925680c0380644915401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 316710512 1250 316709262 316709317
    0x3050a1407030e0301050a090203100f020c030a0f0912170a050712030204090605030610141c030206070909050702071710060b0711060711060711120601060e1212 71
    0x10000305100c3d40da05400c00903890700701400e40343c0241070a185c052904480c0030059500162001c20002c42072008642c00400c000c00b0802400f80c1c0507024000d0000058803000c40703500464000d071070300c41d54498101464584c061701100404102000380201d02084203151485c40f1400500300322a807525100d450a0f8803640d446c1d03950040d0380748000100360085001c2c000b56580b4021345010301000e400078121031500d100410010913052107011b1021060b44070b03e0069880341000050009582c50259281c000c031407034000c0d5103c00c200d960000040340c00b48080b906c100749000c2c0c036020b1241640200301580c200240d45211402c1c00d42c0f4403040c0c0c410415603004010480c000d410080841000868850344903090090103440380090040c8900c10070017210001981c02041c582d603100042c1c0700c041d00c0c1c0300e4900d800446d44142841003980843d030308000c00e040e16000a43e80e41038079035564800781e0014200c07060108000d2180560380071908407440815500c4065005400c81c0681c80d80920306001c200c081d00d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 316711762 1250 316710512 316710517
    0x7020c190305031321030503040605060105130f050f010309020904150e0d0503010f0609050a1208040b03362e050103050d020c0303040b0304120915021006140a0303050a14 75
    0x690f40001c0c4e5030801c0010034280000315184400d8401c0c080401c1100d994020014407004000a100720f81e24800310f4003d0340304e0010b407000e2131200102545510385440d07901d83d04100030310500e0b0bc50320455001d212694070078040d200d03000354045c081403002d80b1688d4510603004240b00e40030351800d654040b2110464400c10481507405070b1502c41565950410001c6d02c51007555402580501030425030410103501c1d40034626080b1400041c00070030201c22850010420f1003503500100840c580030090081840c1c050700c1d01c4260408010480442116034801440500800a60654075801c4803501031030202210005425030b5000100d034111b0700e40c0008050f02100ca0a07002074a00307500c012000e000310303901002805c1640c1401c50003141080d141000341307151031000070300007800d20101075035150303e042c014829071002d402900100c100a60b80e04000030342e02c40030042c8500b07040e805c0440000300c000002081e5190b09101074482d1021a055490658003a4071070a1800300f0411031185007500260108003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 316713012 1250 316711762 316711777
    0x304020f13060e01090e031b190b060117040201020d030f0603020d030206011d090318060d050c09041104050303090609010233070206280b0a0305010501060f0807020c19030503 77
    0xb0b8503e051042c3c0a620039416001000821b1074842c0d403030328844002050351801c0340d2806c030325281011824941e0303040a441d40d104904004001c2620f00c104804801d191384109000c0e070b503800c020300b560011800100d1781036501a026801802c0d54800c3c0324440e0b0014100d03440388040100d850b41d66640802e5406110a400f50700603004400144501b407140703140d035051940d01d0203044c4413901b41101a00d88910034260001d0821b0080e915188040d100e00043c0e42020700074260821040c54840340d202c0c48ca9102c0d0300b64901c128988528100510481c0e4140c030141c0b4009002107052800c2e060900c089a40600840303415481003040c5481140b4000b000080c258454140c040d54111a140f500c50110034041c01150954028a04010f05c5141d2940c1d17210015200440c00204405503486280081441031605904942801c1011041c044150408e034103c030b030903030341d030324070340d94002d4000c80304940c080c0c90500040c0c20801c00900249003551524158190f22040c100c0460fa0b00d655135499a4040030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 316714262 1250 316713012 316713049
    0x1030b0f0603060412050a090306020a0f021606050d0b0301060810140105011e030507050d02070c0e0915010b0307030b04020c06070908030412170409140a0b04060513020304020f 78
    0x10064410292012280c1101d03042d070042500d41440e41e0b8440c90f9541c0f041e614810860b01040079400244500503141c000d540001085541c1c00d0380c1203000b081c0783e0100407040003521540103000b01070000c0c5c1c1c10a008544280d0359050401c2040e204010140554014080c0e1564803080c0201b00342c0c8092202c00c0440454000009802801281c0340110900c141d208506029410302012031581641541c502552454a00001c165031100d500343d81c2030043c060000b80281c40402da4100300856121140309a13004e02c035010003d617852041d000d40c1e4001d01d036403030040103100d18010030052212001440e0080b20f81d00b00480c00c400f0b24400f0070100e030015410300700d1540c07081d4144000d441d0803c071840d01600b0614081c1d07141c01d0030721904200380d2210407401801d29800c45000a99840120241c5010f89404002404421442700c58251611000d86000d114a40703011240c0e40b00341b41c00c1c82200c08a5202503d12008c511001d82c400c070081d040200300b81e80004000c14001101d070f6506085c4400460074a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 316715512 1250 316714262 316714283
    0x604080304120809060415030b0919050717070c1b050f010c110301020f0909060909061303030b0a0b0a08090105090a0f050118060e072102040c0c050a05070905060f15130308030103 79
    0x340787c001e0a950b00c817061140240318003428028070b0500d00d030001c16250345a002c003090644415004031059441101546084803500c0241b0420681c0801100d40c2c542c040d03490640d816000c04041d02d51180148900340d44401000801d50095014204901c50980103150074241c20103a80d008c02c2c2a6403081d010402c0c00c2d4800650000d1a10380a03164540058083c0c1716402a860070108082d901c2002505602401064043c101c00f014860780002c1e5030705801130201c1c4489545c401d0051825040071000c1c00216040500050700d02034144551791040600d0401485074035000d0b100c04089200e211429031304d9549980f07003100201c0d040c3c00e03c40d01c1907115203c0003d90710380020f6481e050140d1a0442c591903036001030920a0082c00003d0300d07052030f404072000101b0520064003980c0070001c03070000a0080c007404010006000d804620700c411689001414440c0703540f0a010440c00f0a001031200c0e90003100c01c0420f1885150340d0020f001d41030803024107000800c0d00d98071002d940360003d0748125a2140395 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 316716762 1250 316715512 316715549
    0x150c09040f0203040c1a0702060705010212160207091d030c07030507061d060307020307170304021005030105010c0b0721021e13120609020904050a1106040803041208090604 76
    0x24461036180392500e281c11415400c00b0342c0c1c2ca0105505503c5002d0b54410200c120240c4102e185040302c2295034000e00c07107541d036072407445d059002c8e400456070b85010580a0000aa00480255600002007450b5000c2c0445a0501c02138400400703a0425200040602e1100c40c0a40c080030401400c040901a004008061071450101c0ca000340302d400141c100003c2c070601510107104d000b0003042000080b103a198480d540e6180c12440c500610b40e015125200f0b8025400d5640d01480c02103014500a4684860b04141b0000a0b20a8030082c402c150002d01c9004c0114081105040f000c3d80081d014a0801080b040c2c0314070411010012101c1545d140d0341c0007850b56035820b911946c8280440d10300039814101159101c000d96035464601c00d08040841400f40481000450380c008881c00303038024103440441c00c050415581d105e810100c1100d09802e40e500c4e120035032400c002900c0072159084000e52900742000800d41440c400050704840c5d0303410174440305105680b003401610141c10200e4610300c001c200d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 316718012 1250 316716762 316716769
    0x3070c06060311030f0c0d030302160b0f0108010506180c030603071a1314030c061c1409010c02150a0902030c060409050603061506120411130506040e031201030212150c09 75
    0x3e944407800d8282c6d0151501c0740341138403001030081c51640c00d8140140c4884c00d0304070041c00c5032052400240207580c0c00c410469801031580242e0b05a40903034008000554505c070901080b41030400700c019401c14500002101055040c00840d4400c00150540351082d544080011070140340380c4030150702001c041404000c9200e000c01c0b03000102720b1442c4507041460f40d04013280d1500c4800e40400d02440000800f00c03171340e80070070418524201200c181004414035044103608600e109651000c055409c1040300b40070f0520000c3e80f000f11000e103a90907000c0391074004026008061640b8100d8141c0641d00040782c960b50741d0000380005045207076000c100b1b07140c0907003003604021008140922550100000c1015500c038241030b50042030b4451191501c5850b642491400310f011403c0213540128962916910318001d074100600a103000d54045c4490310203040042e40700d0103408411340401d03034014010400340c40c10b41c014191980c42001503601403900d0040504840780704894148651f10f002070406858103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 316719262 1250 316718012 316718023
    0x601030b092a01170103080d0504170a020102041d2e090212041704030506040803071418040b122a03030c010e0c09040305030f07020c0d0c09060b0705030a0503070c0606031103 77
    0x9204c0381d600182d40c156510f100b050302545d803c102c00c650741e81c4009010000c1c001d007c88800020051255103d000c5403400038045c1d44540203d80742090080004e61000700008501c500070712004003942c075880101020780038044013101640e003402c07080c07920024ac6000d50703100501e0b410050440038412442c1c541449036115003800e00408511004020410104001040160300a03074030000d815a00c3c2c480c48400c03540c2103001d000030f2031408000201c19004011041404202040581c1c0901c01500c805c410811a0310303822225040607008100b61406000120721081450461070803c2d00c0d503586400c002c80e189d85c02010350700003240c2d5507d000c011035070002c01111001a0701169507112919050f03070014007500010701020345041042000c625068004c0c03010074050f03080580090f004403000d003002c402e111054840c2c030024600d0285c01145218201048a01064108004500e81000010121a507500090884042001751000040022a00c0c0180c4c0025400740101c08140030000b8109410030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 316720512 1250 316719262 316719287
    0x1a010f230a08100b0c06041101090f08010c0e0a0b0f030c0d0905030a0905042307020f0105070525020d030c0c0803070f0209151e131b1404030201020601030b092a01 72
    0x1010140b2403101710400000f021a802544032003800b409800140040c0d80325a100c0c0c028011101040f54042002e080540c00090f01800950f01c08440040300400d115803800342e806841008101003050f48100d00c50380000316000344803002014604a040c1c46620104d44e1001c0c0d040b1031030703000002c081a00561046105025000031501003115031151041c82c100c0110b0f1030160441e880d032070000139004500a00001040c0a8180000d00c000e15004c18018060b901880055943c421003030071800d908035682d21024000380d405421072039090a191000d031441e10008504407040b2500031030104540d0030520240200d14403444807180c5003003140c03041006070b6800400c40c501044401840507217a0783e4401c0500c0000c5d4032013000b140408198000b04001781d02d2654060211818444c0b43c04950351002c0c202e25608003181c1d034420041c1c40e41c40700e001c40d81c400c600c8060f00681c007800062000c5407034203440d0364001c0b1407001100c205d600441495809001600d148543c0303800200c1051419503040601c0c3c41c4003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 316721762 1250 316720512 316720529
    0x150306070e1e03031204050f0d090b04090216080c01051e090a081803031b070503030c0312060a09090b10080d02060408090402131403011a010f230a0810 67
    0xc01081c1c6000c02c41c109514844645126408060500c0340d860520888480c6050b0f4844250a071070503062695548888a4404041e849905848480c85108403080310607210b80390350091400745003c0001000c5d4200c008080144040c1c4800d58000401d001c3c001c000035692240081001d140604501459015201e004d00c0c400710b42c04100700402c0004105034110560042600f9100c4070220040004018405c0030150903100000e8514000c01c40c01c050540702c41c2042003155441e070380392810b00d5201d01800340e40950550092010041e00c00000300d03050380c07284000d0510066650340e51250401c0e0f5801c00703001c2e5130081c0b0000c180101300c0150300130f640103041d1002c0140196403151500035500d00000300017500040b8080f441c20f005175501d030104c50344e01c144a0458200700303271161a10142660170034445807083d8a802c207000601580e02128401f03403407050315401e003800f81c1c00d14107a804540b014032040d00c8202c4a1144500c12010070090800500c0590f46c14920303103000b81c0c00c855108482d402c070203003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 316723012 1250 316721762 316721777
    0x61512101202180712060905040c080a0b040f030e0604060503150109050303040b0d0e030c0706020f010c140703020f03130f08060c03010b0c030f030a1a0a0807061805060315030607 79
    0x1580340e00d21000b00e04005624180c141340e40d001000c0700c6010402c0e942e908118109030001454000580129001e94000c03801c0004a41d694010f140c0c1c1d503011001e0082c040700c0b55100280c0415080c83d50170344054040e00300348207006003903c0003a045a00940102300450404000d0200d50025800400000340084c00c103170307401d9030a10340029524040c2e0b1060a1400b24001450391610702a5003240c4e0804d4142012292a0811252001d454429a005810051203198102000c407e4140900e072241d40e01c90701c41402e440b6400700031f054140e2048131309034290f1181c1c225588103403104000801d44007400001c400d494906103024400a00301541c006002e6510107410f024820f9100804c89044640805600d99142000480d00f421800750300551303080035002004005c42d4403400e4104904003040740e6403003c020403001d0104916000c15019440096000030710a210407400b64001c5880062000c0c8048442c0740d84400041c4079500413500103402030107154001c465801c00300802508071145042003070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 316724262 1250 316723012 316723049
    0x60d020105041502010f0c03141003080306010305060111070320031203150a0b07030e0406050d0309031103010e01092109060f1b0812160c0506060906151210 69
    0x2800d9004901520071107560114201c0c42e050b000750301036000340c0760030b1409210031240154003a00410740381c200c809c1c12614000000700900c9031408590240c0f03030722111003411501c2d4000110001c000003071401c0d05000c82c003889400c4410f41086200015841100041243c5850390a9001a0010f280481b4001d07800415800740603d0765106507680300300081301c02070802c5010700008449605540c000344001d08000340010074554040d141c0790300c0100644043c05680d42d98811b001c29a244000b0260000d008071030248001900001e40d010070220080000c510010041c400340c1c2110940c2804654498000720b606c1c90402400300c1006000c41c0d6410000b21151504602a0140c0da10002034030400890440c0c0d50001596200326045203074220652949898540d808900c089000ba02c0003c851285596000c00d154801c540c4000d0459218014200740e88545050200190f009802994003504503045144d9880c03210001c3d02d02e008103646c040c08a400c0010354800d40d11280c1e040f01c03000003407422620 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 316725512 1250 316724262 316724267
    0xd0e030a02040b1c0c050906060403050c090601050c121b0105130308040f080d0e070b030c160c050405040b040c050103090804050105030a06080601080a0b130c1512110406020105060d0201 82
    0x40c00c03501a0350100d60f504110b000074861000c6aa0b83c82500c1165021903c184501002240705944047d40e40d4061071700c0303000070043c080c040c510001b00740303601a01a50301d09007450400c541d041034044c100715040040d00714420f4102070301d40903c104100004200d540070744050426214162503884000c100d0b03401d04400d00d0400040c0e9801c05028417010318003042c10020040f004585184d007001001d03032204114046400903116000e40c52616106194010030261691000c80307004024207030696240c51076071440600038aa00d65015039011038151340024054403240100d900c980e00c6214084264034141c503121070310120365042541098580686400000c0c3c184003103c0c01d4030000d0800d1500c940d03407140070b100030b00420380100d1144c2c0140c1000180d103040015821614501c946040f80682e034504020220101984401400c440c0c010042040000610300c0040c074108103600d0704082c80d01181076508141e0f0140f07040001c2813000020200203a9a081c45940d401c1036049518814589458000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 316726618 1106 316725512 316725523
    0xc0b070302120a094b050301020316120203010501020a060f20040f06021209040213090903050403110609130b011713030f0816030b0d140f0d0e03 64
    0x80d00d40300102c10b0041601044404e0b01e0180340d0002002508041d4001704102001501081011505490030b0004601c2241810500c0304e607207032a040004c000780c00d2800d0038840c0602c14070051106a9000c92440b4000781c00c81808184200180c180300000c02c1d80c404041013a48191540c207480b030842001900444038084e480ca468503540c0c0b10180c2e104c0c1c981c02c40c0600743ea8010000c2002901d06a4061304017501c2090480c5000c1c0d40f242129800c58202e600d040c0d0210340045400c0040045841041c011140d041e106603042540c61004a11341061001a2104a40d2030b80800c0b24164802d402d0041d0300d510080442c030b21420020041d06000c000c24405400155624024542140c00340a141d0f008003151105002400340d0404200d0041008884450340a091010310502040289a94066100e074031000703010780c244580a03031854812148581020301250070358580042d41d0100341d = true := by decide +kernel

theorem cover : BRFrame.Cov 316546762 316726618 := by
  have h0 := BRFrame.cov_init 316546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 316546762 ≤ n) (h2 : n < 316726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
