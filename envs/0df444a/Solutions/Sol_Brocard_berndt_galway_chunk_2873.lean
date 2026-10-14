-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2873
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:59:40.68896+00:00
-- url     : https://prove2.me/submissions/7efc1622-5051-4354-a8f7-2ebb69f18ce2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 516546762 ≤ n < 516726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 516548012 1250 516546762 516546773
    0x30f032d05031b090d02040c02150112110d030c110a03022205090d0203030a020901090512100e03040608010e0618010608071e050904111312050d1e0c1506090209030105100b04030f 79
    0x240e50030ac16150b01340301800032411020040d0000780161041c801e00c0301d42804c1406100165421a000801040150f982030001134242d114031110010040c00304026142d0300c0c3c00180108809008030014441020321651040070303580140359204d1907c400401002101d244003d580344070050042801d00d5000c5504400c0e603100c0c40f0082c3c002d1200406800007010342c03840460b21410840f580504841c5071010004a542c000700c140d4046820640707030316010760301e00004d21500040081849034050130007107094901a1401e00010f001e08115601c0183c00e1501803000f602003003481701c1c08403502404000c1ca0720b0056206017103a02c056400d45011400000001c1381c402203004103071804c3d107a03039000000402e22240c01074203585e4041c01001143c0c804003071702d941a5000d50b98941c20104140714110324100490248220100880c0704501c101854000100c040044412130b030020000c058000030850540c0c41c0034050381c0c0d0044003215136842c00ea4034100072071030580716070f200c001c0c04001c0e804000300a120 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 516549262 1250 516548012 516548023
    0x1111e0301052404090c180e0105060a081302030115060210020f0d021315050901170c160c080d0908011a0a060f09050301020307080f0901020301030f032d05031b090d02040c02 77
    0x1103917500911011801c010b01510300424000140012508144002025109040064103c400181416103010700c4020211400c81c0020601c4424014030b5800400580342480b80074071041b0781c461100d144906102c002402c02e0402051001c0c02c0d40144505c3c14100c18110499241000e89007006036203449006042e00c82e03580e5948012948004141080c181e244c0080040c00130450984e03603204540c050300d20040c46214252101412002d003071105016140f08036506c40049401240003564482d55400301d949050b0b0801c01017000941c400e13008200603003090082c0d0607107000c55110114406001c1c3d010034290080351140d2805c00071400d80c034100b2180182610800f40c940500295030b07070710381885c01070b014000c140e900703904844003400011a5140180b0982c0d060346d0703124410021014135501d044440c40301c01e240c600707654821958452508044e11080b844001901d481c1d441d142e1500c0c0003070b62108002c5030240075108904002c01406903941620006800768111000500120b0081c012841e00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 516550512 1250 516549262 516549269
    0x90d03021609020322080a0c03050d0c020c1c050c0f0103060b0d050414061b180d050c04060501020f030d0c09170f060a060605120604020c01111e0301052404 69
    0x210381c2080003040c96032054008501c00c40c003800c5440340140c22015400d6031105000300280900505012210b90240704402d071504042c02881c100d400c02d140302c0d20700400c0b19108441d170805079014415403555030a010700c032180c0300e00b04601d20350220f00054490945403401400c2040c410900052103400d5a80281e101e50064002c00c0443c503111003007405840010003040d60199100140a0111080b0800c0020102c0c811012680e2550844a01c0c500e5645150480810250003042c2d440d03008147ea103d00e014201010300950040405003205003d001c1201d009402042c11500071200c0c02c1c3d0442d10001c11116417240f01480041d85c0540400100c8201100b6041514400c1500c0f4585c8080b010010300d012211025005840c400d0300c0d180e06980441b903d0b031044201194043c060005c0b46080da440907580210040c1003d03103040c503c2d140c402d085030040c0d0040b409a4002048101c15840410802a00700000590305403555040c000051007281810003100306100c05030320740d00001c940d10b100341e4005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 516551762 1250 516550512 516550543
    0x519030c031b110601240c05030f03190509070506041e05041b080106053108120c0f0c010503130515010303050403031806120c140408030301050a1505090d0302 70
    0x1d207069050050440b2485400c0f90f1151048600204185c504110715850b403909644c241c44040948081c15550050008000c0d07900d408180080b10760070540300300545c4904218034000c400042048802400c9450180094480c0d902c45041800b0303586459080b5800d99948225812b102151444603510544840d00030640041c20403801c80b4000a00a000380c09984450300c2d0480181c0e05d92000701c45900802e800f03078040c905194012110b00d480c460301c070113844014030708440d501034440c0c02c241e00e04803102010313003106180003e5031124408140201d614040e406405801d401c1350a80000b802d070300000e018a1403d01c60903080d2000c024042001000020f0300070b00c880010f40e501c1c1406041c41c0c100703100a90100d000c0c4611034042d45610000c4800b0307502c20b900c541c4241c000c0548940c00415100f0954000d10014116110721103004401a100800d1030f80c00456a0b507043c20240a101e446a5000e01c0300c400710111038036a520307048801c0c2d41d41d4038001c0d10f414008150380e00f400c83c40c094000080698 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 516553012 1250 516551762 516551801
    0xb220b030a0f0b0d0803010e070e01020d0c020d0b160905010309020a140a03120201020a080106030912120e0307060603050c240304020d1209030c0503030c1209031c08090d0519030c03 80
    0x20009203501460488003402007403111275442510541d404100d02d00400d005070090001c120b80c0a02603030a008181d800640491207141d025511031510f4601034440981c06411480070400c0d4950200000340501000e04e82881000415408294002500d0150070003e0701981b020045517103da80c8050025078102644514410003094064000d511818030701000589030700020507654024014100380660203440c010180d100180100c0c0c07603540c01801c8450b820740303032803550044002c1040a4040345000703400c0002c645245d4a042481d203ca924441c0c0c2c050020800c1240c011040030219800086405070802d6803540c480c800107080101031031008022030140398603c4c00951740440818280d0b0720404180494030b890708101640d900415480c000603920154030340c0c9400300d00d00d001e00342c1c010000d01201d81487e4444000760445070780410310341c005003910381045a07840040101d641940d10b141000c51415005c600d6007528608050030320400d258680c080c0e0a101c9101e60b100c0720344030400c07018061 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 516554262 1250 516553012 516553039
    0x9150409020406080f040f02120309040e0c13050702060c0a1404090b03010606020c030c06130503240f040807020405040309030803010b180f0906150c03040b220b030a0f0b 75
    0x2000b500240a2100000e441000283c2018840c1c9101402190030090101d5a001c0c95400c1150309150fa440b01e803882c0c04244101a00303070b02c0758040c0d410390703094400280881d0b520540500c20841c0b000700c070400666007004280070b201034020595075000a11118004c0c0d942c0d151440540e4008800c803103c0d00040c40c00076002914241a034800c040f8000101c0c0240603003030303442000703d9886810021305941a0400340c40e016040c500500109000349040d003614542340d40d980300013400e01c20181829560128800c40d07000350340400c62111a446200d03440e00c9a594145500c500210740103242c4001c2c02196640041707018140528104002150b0000509030380e50f84034406809030f5000b10b6041201c48c0000d5840010500c1d01c500204000c1e0005040020b941d41c075442001250001140c241104800070041d80c421440c003400280007421490480690714080c40d418102d003031074604c03102c0c141c4e00203181085c0a60301e0000c04036a081041c40794085628280268028000e00201c1141580b00c2019401c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 516555512 1250 516554262 516554279
    0x70c06050a0215100501030c182607240216030b18060903180405010b0d1107080703090609080307053c060610090b0d0218100201050103050f15010b091504 68
    0x400d80d0400e907014048c108107044140d4501144d2810031590400280080c4400715400b42c624840c054003c0c41e014031b01d00421800342c00d00e9115004074005141098011400ba4070120702c4c1554102184000c0011400458442c4042016808000c081000340000700c0c1c5007030301015803140840f040e0402e99540d802c1250705142c0c3e9178040d03025100d039030380400c0100348149002d204980c121648164400e185c00c5414289000903e05c0300d4685400080030301c1148082003141d0094641a482900d40e03050580c145980134196901035813000c072155201308211800100b0100b890911480107803a151800c408001200d0458451104018007450038078517102c50190b40080c1442c01140c091320120a101000c190468104500b0300400b003000c0303400c00c03141c20310a03410760061480d01c80c4048008035003071144000901e0201070203c840010303074542e0f00600038841e062000da51701070002801001e0f184d000d4be43c0ca400410701445400b01403074001c1441002510f403450784032020400420350b6a0740c0d07520340204 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 516556762 1250 516555512 516555541
    0xe060402030706050903060402040903030612081c0b0102100c0201230f0703060501091710020f030604050603031303020f030f06100f06031103040816050303070f080a02070c06050a0215 81
    0x50307100e4450340c000054481d000700c017114504c5001401400141d9255000d0002806000d181101019624000011040c0d1701605821805100350040355544480d244851450003c4c2c03402109014581031100301181c2e000035013003550721411070020809520740b8509038010850210b070700028100c405d0601c210082800744161044501a006211503155803408600f03e940071b0003110b001c01d018880174068100c1281034480c1c03540754417003121280075140c031100007a0381040d142403aa942020003070040c0392400e4040c0a40c00035080e401141000c0e130240c40c0041002c0c0c98807010b4003c070b41100542516450502515041194140840f165810030000d190703d24840c9100742400b0451042e40800c406110703010b14400c44908605540c10b6071140e4503060f903290301040c2841c0c10519442111400208107101441c440d54041e00c81885d0415010340107000644020f04001c2102d204200c403c00080546940c202035400900d07200d41c132440644416850425a0700c02005240081403c004c03190a9040c003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 516558012 1250 516556762 516556771
    0xb1501020f07030b010303180f030f0b0604050c2712240103050d0e01050706061e0b19081305031204020f03030307090905131a060f06040b0a03090609060e06 69
    0x3124550121203440340e0302c0341c00780c0c00020070703601d0b5800040021030b2040100c6074140c00c201140200f8990f42d45000c1d440c030301403a841110043d901c03010042c00d101e42140d10740e0f800902030b0b8080c002454844003101983c4203c01c0c03004480701d501c2440e80d00c01402500b114410140c06001c4a818446000d4a241d483c4054881450b2a000c0350b00c1c0910041e0110340e5080c1241d902200505001e8500b0f841507031035200b0a941f46040204c1404207602060b00e07402400e005103122840d03803c10000301108041c1103102600b04096040d010040e0800380100c100ca81a00f024251400d40403584030170303a60803004811084054071500c0040740004803406104002d0b40134920848038245903501000915880303000c112103000c081041218200007810041e0007056000e180c3c250503211000482d910307205030f10003032640440c0403d445401c10906042800c270380490394000301d400e00c0c203151501e01818820b00c600200c0e2020903484086c80402c000c22500841100340c0c0c894004e200080602001940c0e8410880d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 516559262 1250 516558012 516558017
    0x130e040204050601170a0216150507020c01020a03020c0607050712150501120f0308090c130b04150506030705070c050a09021207030203100501080402060d1803020c010305220f0b1501 80
    0x89655503018443c0701800b48000200403070f2a03661b42e52070384001d401804000ba42c0c49411403a100c002044801c0d8602403040184000a86050040000f4505080711480506650003101c00c480401c2d0001750741840786400301c2d9155611207803803a1050510705180d00040c4100081d20304902040200c068407201c070014808100500d03a1382d44188404a503101701c015180c2a01c6500c004003080c82080482c1d80401404222584903210340041061500c442888100032070b61520903070f070546814051581c04043c10803500785010f040c240000c0c0caa10024000304244900068540300304680340c8140b200a020003441550003580d0343c181d0602035846026000f010f020502c0c005502c85000740b0a89005043d0962096042030038440191000400a031082c1d9002070240701c0344030742e400140a8081408103100d4100804201ca240280c60107683d0b07401c450516051108225014250301115804000308109040410b102070400744074910701c0c1e00014244442e50000c200c2a0005514a0000c4140a9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 516560512 1250 516559262 516559271
    0x50706141201211b0503010506150a051b030708030a0b0a0807050111010b0a091d0a1e0807150b130b03060402060f280f0e09160203130e040204 63
    0x4030324100c41449403001c00d5184500040052005011a402030b190340d10060340c240c10005201d854400080351242c3c1d40a410070780102050025084c00e0084981044042e00e01800c080c40050900c2800c0c068000071100300300e00070481005100c12991110140c0407680d06895840c1007500b400010796004494041107203003402201c0140e0300700b800b031050480f40d08401030321500f42010011211041d607255111003542d25000c4c0402c2da59160710341034005190001d800580640c54940364035030500c3d20780742c16085070025007480740403503400030500d2003005000e0449040d40a06241c104075a024800001e040714007041d4600e48045e0295100ea688410300300c5040c1840c00f000500306094030b81e103020094060b000800401e006040401c082c2050709030500c0024140700c0c07021940c0c80103c8050030180c2c001da40411400141d0b03034001c1d0b000c080000b00c902d041040c542001c2c1c04a40912800b0b0111412010070074a2140f05034401d00aa4070074801003080040c20035501d00c08103104a4095030140d100f1b5141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 516561762 1250 516560512 516560537
    0x30f07050307020a060b03010f15090b030f070302010e01170430020a120504180204051305011d040302120c0609010615080f0604090f15060906140d0c0f03050706 71
    0x240007520301c100159801450311501613680c0c040684084100e5540641d22007445c6610902c0fa4041d5601701c28102c000304801c3c1c0c0c50540c2080588052101c1070f0700030340151100d858406400b00304102542d80a00702490426040b000485440515841c080b40740390070b031028801004169425440c4021650722002c1c560b03800548a08510f042c5180b40101583c4007040f1840003400b9003404510700c01e0340d810094101942c0305000701e14511030000310400141d0000301030019241c0042d031003800c40ca102000704882c1d814145080080300c3c040c201d0340e040650000005007094403c10540094144086031a5117400d0068192a0b451a058a01040c60f500f000d80c0400c13040c0114512144040080d9a0585940c9601104401402c409085071f0b82060b1030f2851840402c0b03640c4512040f5a105001007100409010494412a850fa0300000021820310303000b001286040007007051403030380880c2d00020b042e91520704024113a840d070b401903200c40e0300345500006001e80030900700c3c03c80e0455221140b80c640c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 516563012 1250 516561762 516561767
    0x17070f120206100311211006060804080a20010218010806041a060334031805060105010f020109020307060503181c050901210e0f0a080306010509190605030f07 70
    0x101140c02c50142000fa003420004a00c5484d03560b184008081c0c07102c61968501000e2084081208802280d41e901c0350712044050801403246c2e030018501e42c42c3c000060f0805580d000c1036481003614580801221450718418803456003105503580d040790300210342e07425800c0100303502c41080c21141808130716604000380719402c15010319200341419400c81050141d22104011041e04050001e03156440020f042c0b000c84081d6030a1301030311861400940c500f4042009000707084d140d41c1e8610000c010b1559a40c80c0008900041c200e06481c1c0074200004c4900b40030004900424291102950500c5065000641c040d00a0000c2d4050141075129040404042c81d46a41d181c0700141d601c0c003000343c4004008030041c82a406001c00b50300516110391076158034802e0002c0715a004044107001560f403540613032070398003c110508508541c10042c0800c2d82861725001d00768007005042a040c01030001f20078050b0f65800a0f007100180f0501c161109054a444008286070021038172211241c0320f038404140c1450 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 516564262 1250 516563012 516563023
    0x15030608060f011a04090906020d4704050f01151b02010c08041701050a0e01060506250803090d0206060d150926071106041d0417070f1202 61
    0x1e0740c2c03460203403140d107410034240020f414110341d41d4800100b4480866181c58034040e00d15924040e180141e140c0407900070034021558502900066011400340c0040c9200c000c42c1d0010360300420016610090304000c0c1c1030f040011205a070303a6030080c604002c10102c4e00ca810180380c140c5102c41140c01800c1d100500641b81c1c801a440c02d040d1600580c81000c0c0158811110f10745038a02c58460503040c55502c0b0030481000411141000d1241d46500402001c404176100c2c80c00250030250007440301c20301d45030100da0070f403040b10407040340f8448900c04c1640c0045440030200c015a03100c417046076289804017a8540300d18500e10440014000c407000b0a64604e0300000e51806550407800c03050043c150300d01c441e4002c00038840c00304c44a0119032500d41085c0c0c000f07900a4410b4240d0340181d1b50b540f200d458a2002e1542468940f841401c00340420310600030f4070043d4504044071510092100c1c8c8071030900141c40010b5012b50030500301c0018103030082200e00070905072414071640d00702c40c421008400c140d0302c03076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 516565512 1250 516564262 516564271
    0xc050111040f09050403020a0f030c050606063609070906030e0d0509010f0201090b1303080a060f180e030f07060b0409080d150b0a03060807090203041a04050c0a1503060806 76
    0x60381d0340c005001d583c00552196030001c4c401e00449404100c1540c0d51504032000c601c003038010402050401c1c052283c180801c5501800c116804c0380f07404100020083d8850500881804011758221290320050314089044503541c00280b6181d518a44190000c00ea0000c9019210000741000000154000e0006140c10b440e6001e40782c690074003a030100116a1003403503800d003008543d21004104041032550400728000d0610402c0503501400908016000c00c001402400c0700ea483c0240c2084684414203406080d142040d90451348181c0007210f202c040c0090700307800009030000146c01440c80740040000c3c441c0911801003407081001d103c0c100000c0b10189003000d082120104080d122040d01944503011410000342041130242e01d41803820310075001513070b4901c0803999032001804000400c20140009250301401035141d40f42943c5c84030f04180c00e251410103888458008602040410701148418400203422410101d40c0c0e00f031010300507a16000024080380c80e1920205114801042c1c80b03119 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 516566762 1250 516565512 516565529
    0x1505160212161509020a03120e011106070c1b060207090e01090b040201050c011e1a090103080f03070e1f14040e0f04060b0d03080103020f0609100e01110d0c05011104 73
    0x1a6a207500c030711811480004140c54195650750b5a07000603035800c11464090360080c80c60402384040f44c10050084402146a0303070622450a506041c407100001e81c156121031107140c4404914103c0c03400400403207801c40881c1401120300804606941e0001d0300408507901c01d1000c2c13080c03030203031144c003801c03036044510140044c40e0441c000b03809540550020240c14003414000941c407201c40103664a400b44203000c140c1041d4803001c146803030003601000d000f03400d036007190035011551440d560500e06200ba02d1410704800c4000c00010200c500a48e8844081e0300081d200509010750080100c00d480c04810b259000700310b841c403121807094600c100355015140041d540036801d840700304c0450b125490043c0f08130707223041c2c40302030120b101e803143e8440c0711750244a1f880e014803e504500c100400545028840740c0207010500803c0710310b1341c4000c80000c140b021400c000002003a85c3c070040340c08402115954a0904c00d0b0707052800e04550003c22529250300030700080003440320301130762034403070b8840c41c400d8441 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 516568012 1250 516566762 516566797
    0xf030308130c05120a020901090c050301090b040b0901121506060504051c0c03230a030807050d140c0a030f0c09170c090c030f06040c02191505160212 66
    0x1070012140a407610024014480d400d459641c40d0009806111500404d0000e40c001c1d110070011400c0c00010300c1d02614400c002801809030304040140b150105100f110401601c0f42c0058200c1d403956880910b610001400b002060345e1148030321212030750452811120440300d0502041c00407018450303d000e4440300d65940745054544820059100c0120030758000101c2a100c071140052200a105401540b01e5820030501310800b032165580d4142c0850800c8081c2c00c25024040060740c0030703040544c09180c60070602d40b070700e00302407850b00100b00d8294249900c580715401c0c00549241100600402e40040d6418040340350f081c0d00d00b000381c0318042000008110b03100d41c1030113103c1424a80c00840c4520a0840f0005000744c0d00180040c4400d451040c00001e000081c0000098040d038119480303102a03c0610906103c000001d44e2070b481c480e00700b60050261074a4004001c080d05483c00d0305880c100707040c006400c2420a000b05d40c0101c01514026115110003003c2c08580700c03040d904514600d100286 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 516569262 1250 516568012 516568021
    0x1605100e1c1e0302040f09090210080c040306091e150f0605060714150709090606020d0c0b0702101b0e1008070f0309050d0908070506040305061506071a060a0f030308 73
    0x2c4003000d6007001d0350a1640034000400d40d01589034408008003184480824002d495006218481c0401d04640c803c11003854108004400e408040718116a44150001984406420b260b44401a0003840114410070f91103c001404190721007518000200c0400308501540040f081c000c0701c65510409400040601c0610041003804038400c00038034a803401e50b844c503414400d00d488908001c80d110b00c082211042c0c1444804e616202e54000762601c2d000034850945011000f0b4251400c040f00142445c02500000c0d41681c802e100000d240c0c10000d105001840e5000e120b0003018210340a1000002d152a601c82000d1504904080d00141c264840c0803080c1c82d5458225a034100c0c04102506240d190030b9407030700068040001c1d800090300342c3c0c0c41d101c001e41400066824051640c0c007440c07144c83c007880b0600c0400c0000c1070040d00b0280392002c004001030400d0200d00340d80503140300901001d1204160b4400c002c11281c1c580c1c0328100071111446003075114103a6070101c120500020740092513100006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 516570512 1250 516569262 516569297
    0x123060a0509011a04030506040b0901140f190b0301020409020d0f06150e010e09041b1502030a0819060e0108060a090c030201260a141305060402061605100e1c 70
    0x30080c0040e9604c0c2185003a440e03440342c0f031400c80e054030200c40704d05944e01000514002031050014001c5845a4444642049031041078400805410b5002c450407030362030400710b6a1141c2c02107490b00e40190096440300d546014010003500725414030551242803d1171800e19401610404080c0c0704024a074036002d46040c1c1c004c96140400d910343c1e40c18880e4103c8865500d6591035241d41c8214400c113088080100510068400da030307070580c441c0c10304502007050680d450b5008400d541c0c00c44210306c0d0000c016614031010210b09a104014450701c44c1c40c1980200d9038a0028848505032071281e400c55501c2d031141840d80c03080390051030010346440d485074000d000541c42110b540b101c101d0408a11554062080100c01c0201c0c401d0b541d010381c2c903a54132180b035402281240d18036405440c2042c409034147c4d564503900d40704d21009100038400d690000302c0c204030001c031170396178021160040119409803108c2014140207000c000c18401c49803042a00449203541210040124000d036680d40c0fa503403a2465400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 516571762 1250 516570512 516570539
    0xd050a031407050111030a0c1403010b0703022a01091a09040504020402090414180304030221030415020604020117090a1e02130c18031e02060702030123060a050901 72
    0x403030075918030030061040440c030240100300403a60b4000c0b000340d490a10090b04004c0b00c40c400000c00c10310101c03043d149400b0f2048402d0328111042e10014640d142c00c1860f04031f040c44110001c44851003e0345140f040c0b1403003983ca1205088000ba201c0000180c2c44449181031b41160070070070b44400400b00000038032400c16410842d00503101070000350a180e000000542034895896041910754181410441040354000c1080d94428041014500e41425178010611041c0fa4805d24012000860b04803130341e0350800c1003184c0051a000d01d50a60800101000030b4a40c142a10180d00091100440c101070700c03d03801d021030181c03104034020407040c201951806000480741d640d415004a00d040e04c11301503114400b5101801d14000e00c000f0b10521010000740c800c41508104141811800b0800d000107030320b100f50a41c0384001000d80b44600380b00c03440080d996102d2404000e4044d428940142554401c41c3c06c6a003203d1007500344940e545e0303503c0d01403140f40c079594801c1075444001040100080c0c03001c00203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 516573012 1250 516571762 516571787
    0x20f0a0204090204110a030509100209010507020d031103040e01080c01050421030e12030913021606110706090605060a0504020a1d120303130b100e1501200102180d050a03 75
    0x8085207100341d1011205c90342c0c11140742c20340402d4031103017008500c840c28440031804010f01e40c000c50504180800080440c010300b14028040ca400720f041e6420b15004005031103a03c2e01820459981e0340d20340c01e40010301c18080c0700ea0640352280c070444880a60288080d5829a2510403449990b1603005000c0c20300080182400d0301400300010301d05015850300504040049514801180d07540c0d4a01c09225411108100380d80305c541c810b0041080c1240c00e18030411802ea00800003044070070030241c02c00a00c0c460900010489441e0400e01c90801400e50402c0b48200c4e01140d400000999039000c0c03005071320400c0da00c2d10000b511650005070003120b64240d00c500001c040c3c031040c0c0c0180c000401c10315681c02658800c024045103940c0104002c912010729a002c801e0f0071840005901d0424020103082003e0b003010081d01c00c849041001d40d104008aa20150102d001c00d00303003075040031a0034000d5200341280319a0300d83c40b04c2103101030f003482130000c3e50080d031040c01030010203c2c60310100c5001c1e0300501e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 516574262 1250 516573012 516573019
    0x9080c06091905060301081b0915091b0d0b0102010c140a11030714070e0a020906070602030a1401060f0f0507080a030b061606050717060a060503090118080316020f0a02040902 77
    0x12400f0901d61100000346000c0c02113000108001f04240740413401480d440e50b01a84148024800c0101e1841031000c0d802c0340c5031080c1c07030030b0344507444e21080d460581a00341c0d0040e0060030302042c214006444d03600500c40042c1d003a0008c00154118a0085a40407003212803c025404100300c0c844809225052a10910b5103d0341503030308041d00340c0e456a80c080520811031802c0c0d40610001d0050380109520380b80c01c0810004110b00d000c82e40404a02c65020b0390744045c0c455a07002c400181807503044d030881c00a095541e21103240fa5a11214041d1584924120080c00160007012888510380201d00312540d450b00800e0043c03d091410350200e000e03129080710545c1000c0240094501c1400c01d4850b4070006101e9100400c180c48c00282c0100407041006c1410300c140b03681000d1042c2526512880e5081c1d80091410547d030390355003074109015220700044540340303d4000c0044010b02070741001660045d00300c00030003c55440c1d82c0e5001c0b85e0b90a0185050040360300004103160061901e9030001c111944040c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 516575512 1250 516574262 516574309
    0x271c0b0c030a11040e010e010b0703090e060d022808012703090e1608070e01120b19030f050f0312010608090a141c031e0f0902030a0f0309080c0609 65
    0x8010a20040c0c000341d12890a0b4010800140031f0f200307418510a024249244945040000c1920014080801c0e4441c80001210301c0c008030b081607d400c0445a10140c0140c01c194002d083c4400f09c8504040702400c0d44510501c0c1e0901144041c010700480014005024250304040f400c02e0071044072002400c0c049081c4944008000b0f4580300b01d500143c4120340c81000e00440c01410200a450394070002d10720010002140c448080320f0b0307007101c40342494107130650001480c52005000b00d1603281b014003109071603014600b00001004880c00349698514400c1d03003a07443c07807025501d80665a025201c0841d403142c0e031032001405a50301c40c4606a40c84000503084842c1c0c05803649501d02e0000b0003908100454000144135002c41551045402c1210591720341040126444403101e2641000d0700038802000d5102d205100104600f900141281500102660382103540d9107424000c1d029003110850200c0e41e681b0f00054080c81c0460014040710002e803841e40f5041402040001c90b00ea03c140386000040c21 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 516576762 1250 516575512 516575531
    0x90c0d2d020f0c0f0703030212032701090602043209040f030509061303020306060a03030f050c1e0c130b0105070201050c190b011802090d080a05271c0b0c030a 70
    0xc04c260502c2c01503075005880c0150840c10020704218080811454094042061003450491310484806800740000c22542041c0300101042c090001a0009005540041400310350082d4008a0048490f0340c180151002068403081c41003413070111805980c00707001200001c2c08201da8420010150384685082440d088503080042d00c00e030040d0b115420304180100342841107003420040260408800c0b1054036020307156640003007250700340c50015420001c0100f0340c0d681e100c9041040c00804044801c2042c1d9483d07604600c20780d204540e10380e90b4841d9980b070501e0741210002d441429104503040c1d407035030315291941e001921a075001da207800c48140b103040e400400300c010710800000c007940300308000340040d45050366400c445c0041800c0004407520400c05401c2c00c0e62407502e1090101d43c4480b203180c039010b1680c8161058016102000010002d1070004982c080c90042403d8541000301c2e00240740c0c1c0400490404501342c8410001c000c41e40d5040400d412030180030156038466480500030404044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 516578012 1250 516576762 516576787
    0x62a021014040306050901150e090a020f060c1002120106050c030403060b0d060212060112140f06060c0d020709110901050a0309080c0d02010905011b0512090c090c0d2d020f 76
    0x18106c4d60740c903080e590b40c41d8a98650366600d005900400b0080c0c101d15290070300644081c3c6814001340002d11580811400c4c60413900c48505444025944509031251b000c400d14207040170303501034041d44000c00b040600100780076015005950740408844001d609090455560300020018100c0340350340281c0e010705803c0007840c2d07030004111101e00c00c01821810f05003a0005001c03480c8983c0010841810030f08541c0b12540f99017003842d440780003803a642e03c3c00d072104400700d021031040310101c14441c0100d01c3d164640c190009604001c6032510002006100b15603030201060f4011a11428006141009454200392080e0071003607042d4050110304e80b030040810752070b03071414002e1003580000d40d458514050600c8805e104000032040340710805402107600a90050681c4102c0d60b00c0100c0807080f50110f200501c0c00c100d103e81b940340183c07c4920b41c0c03c103850340041c1074200504480e0490f003050308440003900d0b5010f43d000c2442c401b0013501000c8a0703007440c40003c3e4000e0004e0811303a031020b105000d403459 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 516579262 1250 516578012 516578021
    0x1050a1a0f0d1b23090108060d0b040318050907140702040b060a2304030203060112032307060507020f061b190305160203031b0c0a0507062a021014040306 68
    0x1150143c03031640c4844004016040c0c030440070380d01184000401003030350080009400ca4aa544007481d240615a488000207800100c1e136450140040c20341d84100000c0542010207200e24a0404400c8404141d8a80402080c20400c642c0c0c14001542d8141683d060f020880140c10018030040c00444c0c10301030000480e4041d0400b01e0b100c000504c64200c101e8009441000329100100d05070016031800342544c0210ba61800103200360340068805001c0c0400313141c4541d5654182e10840300383c4c00d00301103141506c068a6001607006542c842d182c9800f0a420600000301074400003a040060702c1250307514141010071280813505200c0640040152040b104081320b400d2041d01da090b20b00241c0d900b00000390b6500c949044070150290f500130000e000e030000c074804080010040181e0555554080654128140144200d00414501c1303060b10114007030780c116a030160561490020740f000160070403010380c140c82d030048004e90401e4204003d40790036032051501130400080c00641903d41503a80d51124101ea = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 516580512 1250 516579262 516579281
    0x30307060911040f0209010318050a0b061201020703032309060f0712060e04030e0d030e040209130c0c030f030c090b0f04150e1c08180411070b0a0501050a1a0f0d 71
    0x1603a0001c0c10000e21f42e010300c245d130b400d8101c500701121024141c1c0e550542d24405a00050320480d0480006103071703984c41907100300000091000954641c01c107403501901401181d0140140191101081c581518034084d039103100d030428000410b43ca44271241c0b49110004040c03d81b800300130041d2052140d0400c2405484001c00e0341c035010504a00d4603050040c4402841041c07948601000d03410a00420360229140044980c111001030796625003100040e024240310401541250822402607100f9812200140200340a51100f5404c02a0140300b101158540c20b10301001c00c0440da820312004e00010045c1002c4490048010300e003503207445220780500d040e50a114009043c0d200061154100101d02190504005076481e021a0310b6a03100211802800740c04902100c2032442e11f400ba503140e821200c1c500005000503a9110318500340030744480301c00c450003020682840c3c0001454200602c00e502121211080d80342c0e44c030710031342e00040f40780d0050980303000c40e00043c40344190300900d911403a45003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 516581762 1250 516580512 516580541
    0x307060806090708090d03050c0405090103050c180c16260a1d0603010512010f110904140c03040201080714030705040e0a0501060207090b0a0b070507030b010801050603030706091104 80
    0x280e00e01007040110741c4000400000402c04540140710420303600240d038029441d030608000c00e144d40d4000000f8160300440d80711642c4200e18000000510201198840c60000701780d481c901c2602d900344001011290079900000f500204000c03100d242e02c040d00f45041d40b070344229100e84403000941e0108000e5040710610302c0001e03800092201d051508a1151000c01c030502c00f0110505074504005045404148551402030343e0f41409210704400c2036010500c0400b004d8420000c1c503940302d58a0b680c0e0340000240034040c625140e007011001b002c41905901c1201e6410b4154915030f1381d03900440c3c0741d03400500301c4400e00814a155010b201050805980f003140295100c0b03444928210740802d010308040c180c2c290b502c0c07820b170050020710b502040039020743e5013145000c00c4001520001c51007100055100300030346030b8080f17a0780d400c00501150400450b4080d00d00318816980b00c01715079080362001c0d1015076144c0d20802c0200c002075401e8000746069030140f401060303c4e408820200381074683c144aa00e01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 516583012 1250 516581762 516581777
    0x804080601170706021f021207091401080f130512040305150105011718030f030408090a0e0f01140a0e090a0501051006170a1e0501262a030706 63
    0x450020051225400341802d004000c3d641c0341c0b800103500d03140715021340d19942c610716130401d10b801020340464100a403007404402c03992502560080c82c9400901940c5071945045942082561069140b5801606e6115580c2002d481d0b00c0b000030310703942d0b0403001103030107008115103080b12150135005440114010000f8001e10f03028080020390088050708a107051001990684910f00c10703891180c0d81c441d00400141e102c074591040b10918600030080388035a00500001007108000015001d01010102648c0030011161698100c903040d00702101c039100c50118503401003049042d0101001c4541b4000303440948616256060303010820400c4508070100e0b0710490980341044024442c561740800d8500f0404c00f182d04024005021071504003c03a103040b40c0030004100703010601e0f888070a071680046c41c41c0190a16421300d1802500c030034802c070044007503e000300d003d24400c9913003c1c0c0c03501c901c882c01030141a000071040c0403070220420903450403001181811f0041c0e0300d00f0807152000c0c000c640c40d84903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 516584262 1250 516583012 516583019
    0x504060902270109020a02030d0c11070b07050708010606050a03020f12071d1e0d14030a0c0c150f080907050a1403101a010815030a030f080603150a180804080601 71
    0x782c140606911034041144100300c914403444c0c0c088181c0307151900352407000c200004c00560458110804a45005041c000c081340040c070100030000914400344102c0a0f5040741d81d40b070800a00326890741c41303008003003141000300c4c3d01907901c2680104111003a500c1c4a078200440d100441b0104282110103001142e00405040c50740b5100206d001090041100e0404501116011185101001444d06c50040e58403801003410012036500000c1100d0354070003201c2c0c036400f075124020503410003c5010354055003c18401b1070403501002c898000380300030f40c0b00c0c060380031000d42d002c07144110010145412400b52000c0880c9542d280040c81d4001c0012000100504110808050074108500c00c098155440c10441195481c000700c07030301105460034208404150b5071400c044803007100000c01e00e941400351441c2407007019041298000303001c8072507131002042d51301c2c003040c1507039078000342901036a01e0038690000f0711000b840e400c50800c854030740240b4008d502c001d82e54005241c02c00e0f0401d50098001c1001403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 516585512 1250 516584262 516584329
    0x270109061d06030d140c0303040308072003070f03030b0415050a050a140d020109150206070305060f0306041403220501020d0546030618021c0504060902 67
    0x1c15800c080c48030100e0141400400a955190300407100400c3c81180494880c100e090201505d102c15100416030707540385000e1800905040741250400003060810030000c2d9409070235850b003040c20031103d0046103008120f840703814603428084030807400c05480c0c0030300d103c0071b440d0783c01110280030341410f50001c40740c1003204002c103030000c81d040b040c01008001010010206071100111903400141c4500c0da000015000484d503c0e11180c1058000340255103051060700d80c001015440351042d03a801300b020343c58200410802001c001a403e500d50300c03c00200e004940e910422041c0d5910310b13001c0303d14202040594209141917441c1002050601080030040b650f0140202c4900400d00e03e040703443e01511250b90000c43c20440c101c04030740c1d120302c0d0400c5041c0d40c600d206401f00c08540c1c4c00406100d90501030041c00780c905d5024160101c1401e010482c5c0d164418000d44d84060b001c800840644e401e00c2040c2c1006100060003524526210f03d00c4a02603101e102c0050300342e02001c50300c041d030800e418402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 516586762 1250 516585512 516585539
    0x60e0c0f0d020f460914031203070801030b01060c0201020d27030c031202010618050c040f1215050919081209070f06020304031a0a0b0a090e010b040204050f27010906 73
    0x13000002004800c5201c0c610f588400d448054403000c5020348004c1c0010000300b8030b040c060303005510a00d4400824005034503040000c2c581200d1207804c2801103aa26031208031419031000400a01590020f082803c505004450312185484544815510414110440440319000b5442a5252011340d402401032060791340c030340141030b49240002d221042c40c0120243e9884451000300049569880105800112003003c031402400b4020181101580b141911100044220f0007150344030400c0f0f651002c14419401141d214480c00005006500844580c1403800d0003901c108a580b00002c009031400000c0c0d23122654003c550344002441d45604144420700305200540008043d94420711040000590f0b001000306450b03112070001340103803240c6040101400b8840d103041d5002c02024004034003004540d010f02c0c1510040002800313860b000c2c400744002c91086018a5800c40d803410003600e40c0e4181180354118032601402d5014003064686cad0b80748450003080c1c0145030055200e200c10003602202500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 516588012 1250 516586762 516586867
    0xa0c0b07060e060906160306050604150e09220c21050610181d0a08090f0a030c0e06060c0a060b0108010e0709150e03010906060e0c0f0d020f 62
    0x403c01400d0081d0110741c0c2d0000280780b03904418114140240e410b00c290065401404043c004640761900c409620b050040e4030280c220010b003c203500701c592440c241d06040c2c0503141c41024885400c6021070715048580d440b09098030050440300c800503001ca120b400341d070354810200400d59098491441c1c50340c00c000000c1c0151801e40036038901031040c000300b0500502101d2803280300003a01c1c094032002101c0402c0080200c0c03980d02a509040040c024150000c1030503120031075001c42030030415010080c0300c200038040540300300d40c01102480480c0318403070800d401920051080e41030085600146140280c20a000c40307150707407210360808076941c100040310b02400c80050b0003881890100c0c0001d1031a607040c440c3e100303081e072076806e00c8040c0c3d4090700000340e0049000d8001d0054614509042c0040c0c2224800d54141075042d10020b16006002c00541e0b01078000030b80710600d03000519a542c006900000420020180100928000f642003a5416490104500c2c0c42141302c0c81030101d90020380c0240007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 516589262 1250 516588012 516588041
    0x91c0b0f060d030206061905060a1d010f0212070c1a07060b04021c05060111011104050f01050c030409110409020a0206090c19030201080c12070804060f0204030b0106030e0a0c0b0706 80
    0x1540300d002a40116403d60300003010307914411103102c2d90b41d810742c01d50826401300360488400154601ca4a45c00120134070b40350701c512f4081c407004122400445030010314994410040e08405c0500c401075860788000c0c081c05009400e418030301621415107414184041645420380702e400115002080300b24081c2200405d000c507011424000e58400008110f0740160500ea0702c99035a5000880f03aa01603ca01011404140000c2012501c50100d913a1141d1013801070390f209031101812030b402588103008a8410035610030165051610344160080506010303103c4081104041c40f020610040e00e201400c2010000e500901243c18208220350a02ca88440c1660080001c0003d900f010700c1d81040304001c80340d0a1034140c495641d0f5407019001c1d07000f100758a00391a091441800b640e80da00c030340b805004900030034040240102c00301d00e850407071042d4803000b424801c92200400c4218001d6000f0740c00340f400441904c00d06101580c4007410f014150700702503010304d00403c00c0001c0c08a14400d80c80a940d420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 516590512 1250 516589262 516589279
    0x40306050a021e280c03080c090a1e03020613091805060601050a12020d090212060f06060d02070b070207090f1a0906030a0c06121a010c08091c0b0f06 66
    0x28110f441c0c0c04241002180e602c030b20001294201c991040d00008002504070244101048a4503802421044e0b803140070b030300084100700400c98140651040702d210720030041c8190711083c030304005010101c007040c8206880094141d0004017507120140107012800440c240c2c10030f0315082100010480d03145400c0140280840c2801b9800914006022600030300709081803030b03c5408040b012a00740529000d084803060001c18894507100f0260001500d152007210300348000b82d481c50205540759000c648008484c400c00d40801d45504201d4000c00803490315000141c030b001e11a40703500d820382c40c1c01c0d50fa10005034030044041010510b02e11032000790505c80881031100c542d01c3d10090718080b0303c0c2c26010303109000d00c2010501d075071b40c20030400650342d40c049200c140047e50740710054801010391715850180350400c08025204018128039000c04d12050b111921900d60359200c2d40c9494010b00c1c0041c1d00141c041c441c140306855045808646c6620404140d2490700d0901030604028001030081402003440c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 516591762 1250 516590512 516590527
    0x91d010209090a27060219022a060702120a0b0f09031e090d0b0702070b0f041e03020d080309120415140418050103051e0604081804020a02010209031501050f1201020c03040605040306050a02 83
    0x60308800c925a5044038510403801000c09c0020390350720483c0300c000e5024840d031103141c00d00040491180aa540500c1f82e00c01b00b07035a007210740503107010308458182540e0400c00c61022441600944c200c04002150400c1d400c0041d59408540505d1a80400b40d49641c07907081004078050781005640c010301482c5c000380c1d040c0340c03800482191a00960080380c68041001c040e40c0c10002c80800404001e5800514881c00c0f00f1142c1040e00082c0d10940712201c4c140540e40c4074002c200c4455046804517080703203081900c0701c101404201e8103800e400c00064008a003c0000150f00d2030140c3e01c0744082d00340d0318000101545585441c92420030b418103029503501d520b00301011007803404511a64019001040e113503480c2d6451908042080c1125011a401480480d01070325199055000e490f1007802071f000c441410840019880741800c09100c1c160340070020020002560030944102d0100b408031100260500c48208000d5055803c80e42010001503408101001400560b002e115000b4090540071443d09a6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 516593012 1250 516591762 516591793
    0xa051e040b040b0c0a0204180c0e0105060304020d0f050304150e03070605040b0703030906060303080f0a140a020a0302040819030f1b0f020613091d010209090a2706021902 75
    0x100d11074503c1d0714002050f00342c0d13600800c1c408800c40700d80c024000c011311444040c0080305081c4608050f1007548140f40c011524030355241c41541603610082003030b070440c0c1d5503900b0001c070098120001c80d107210b0038200c40130005100b0000307800a002403d0103000142c0c0a850003e100d40d982e542d24038400d1740000c4041242d9174201d4101c405840d000c1542030764903c07042c00c041e0003030011690010b12081c41e240b0300205250744000e284d0701910326a51109882c5d150224104107482420041c0180c0411640108921008a5005207500700c1c81c0d09002d0305050b51006282c0c14444070004881081480341c01e980201980400c10b03480c03024080c101145611000000c0c007030707448100c44c0c0c018124101148824159a2504103a804e120400754250b01d0180e294003c000180c4908000403139580003419500010080c10f0007952040a4082d00100480e034498000602a0036070a503003128510200c42045100d0b0690300310091041e00903100583d0341c5000c00d1000070324280c10840141150801c82c16081c1e90407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 516594262 1250 516593012 516593017
    0x30103060b010c120504330305060d02040608030901020127020d081218011104050d02090c190806100e09040318080102041220060319060b0a051e040b 66
    0x80e04240000745044140300140c868008031500a0484d0030b074005000340c1c059100b4020015a0000103100c000c030002411082803110308066004000910708105c15202c82c0700358032440d881040100120b2030002c868020400f1514150802e808a400004000d0358550b024010302c0154a504030519551959801030103a0034031030a60020b20900254502c1802e006501090303c109081c4250444440d003045207030304c0d1004140545081c555400c01001c0d0280c0c2d13212100f42e03011540003608800c22103c09508021005000401410780494280a80500352010003c0d0403001e034204d0b01da04d600c60801c4003c10000d0005015101d080103d1440700b0001520307886d02d1250400d41c1424014041c110054607001c40b440581c020240641c40820006003d90f44810034000750b078005d414101c0254030030141211031f00110000180c0255040000c01c6c015001042c4c0325030041c012903400a2419141c044000b5542d11800211000540100b0513141540f840d88000042e0b44442180034942441c0048001e400d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 516595512 1250 516594262 516594269
    0x30402030304180b06031e280506040e0703050a06051f0b0c01060806090d17101e030c0306060302040f051909051203040302030a09080606030c0904060b090f07030f0209060301 77
    0x1000303101c08116500643c0d4120404954005209907141d10784a10700b558138414840c103a500b80900319010802004849178000303a8418121422404800d03405880c00c0500700c0139200300c1c0c019503103084290709454144049000f43d84244040c0c01e0040540c04e1900a445010303001d0300f04819200a21802284400c40c0c400460780500422034990141081d0780d4010b10666210640314000d907000c000b1024004200d56050b40526256000c0906159665000d18003089400c06002241404144030103d20366201c0803072120f950716950400c0d9101c0d981c02940318810344c8111022034071890700b0b20071840c1502516100c5100c0610821145c036103800c15000c54440035084000312030380c41100340d090202c2442034002490341d0441c01c0e0358900700f83c50000e5590744004000c07400585149804079042102084240c05a00e0080041401c6028242004401d80c4050710844025946080300301c405e0302c070350046620035081d601002880d40740600e4085d05030f5082c4100440c0241c810024001541e480c101628190f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 516596762 1250 516595512 516595529
    0x1401020a08551e05040503010e0105010e0103080c1e0d0306120302060c0310050325051005044b0f06140f040e0c030106230a0e01140c06011505030402030304 69
    0x5280c5501010383d481c00c404058610321607a0228154420b03500500104103c4030250020404d5490001000d400c0311420b00071800034440045c01000442c01650107029030540038401d41c2c00f0a040707503400c0e8883c945c1d00304940305645c000b4030050b9511134040c4250f9000382481c0503a201b05000b5035178001d48840009180031001c0c139020001c150368a071100685e84c00303407134064110341d00c40c1c42c20340c50400702551170003518100182c0940c0c0440c56041c0702d43c200065241d213454950410f0708101080381c00302031401107191040d8003c0035100046c1c0301c0d09441d5103014003d00c1c02c20a00c90300d20000012a085542188030303000305145081106a5001200d404c50340181d4200c20340300d0b8280b03410f14881d4411a03001143c03140d000c0043c420b510030807100a504a85a90b2030300c0d4000c180c506000c0c0d94410215070754508241090140c40c895500451250055035414074001907648060305100101d80c105100c18415035000f01c0060210000c0107660750006005820441c4c11407409074006136903403203a80900c889 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 516598012 1250 516596762 516596917
    0xa15020c040509030d15090501090204031709040227030601080d0203070303020f0d0504140f010603020114090301060b0a030f0b060c0309060d020418050402010e010e0a1401020a08 79
    0xf091000d205960301520490340922a1652060070a003482c036650164070030492801000182d180d80314400c682c200c13940180d0b00ca095120511008289400169103a0740040c0c00700400c507801c5510600203c45e00d00c9035070445150b1440d131014180340c000e0580041400d98400604140080d80000c15240042d078586409a41c034000c20005a100d4010281c040c000c20b030070701c8140402c00c0400c04152001f80c0d00d85085404e1400303d151424203881d030728803004e0301280703100c03481c8409110004003c01c2c50140107400421401e80d030714000c0003d640800d1400d00060b5440088040222807802089904c50007180d245041c00d54500040713440c3d02c1103940181c8100c0d0006484240e82880d50140d40c001c108044c14101601c40b0840c80d440075242c121000c90008000410951456001c0c0707140302c440c200081e01400f01c140c203042d00c1c1303a40340440c05041410b520441e0760030800074901c10000c200111041c0302d03010342c400410701c9590b8030415052186c00250300440b01000082c6844c0327028070006260301e18881 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 516599262 1250 516598012 516598021
    0xd020301020c0f0319090e04030806041d0607120e0606240d02070201030c08070c1101170406090b010506030f0406150b1801020610030f020d050c0604060207050a15020c0405 76
    0xa00a1040d0800b00729180215900b0101e581400700242000c07441c0d0a0080801324210b0f802100c0000081c0114200040040c000c1804a8402c801082e40128081c1000454420420009140007591080355490798828000c00a00a81c405601c070b80900807014240300e414040341c2c04a841c1c2d0f80090846010780900c82c1d81240380494038481030701c1141260b12250b41d402210b10900041d40c0300200a0340440e0910b20140d003042d100d2000c05105589969030488034610b00e41c1c030000384840c4c910510b0304000d10301004100c6015010b02c07640c0280d105d0f8000003000b0f091450030344042c000581c403542c4a070005004100e20b0385103412815070700035403203000024140c0c400f4410445459561304041400c071390101c0c0350040d0b10301d080032000d02c800e000d80032219103541d8140c0300940142d0074080240f641090580d940014200001c02140240c070038802e82e07040d0031410002c10565013013a800341005038060242001380d03050400c1040082c041e80d40c40720103440602c0c20060364442110070402d02444d600e00002c4c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 516600512 1250 516599262 516599269
    0x80a0b01090510091a03060904110a0513020c100203090d0509031504050f0c0a270b04020c1c03090b011509030506070f090b07030e09040c030b1e07020109030e0d02 72
    0x14800362100800320207034100300d008014441c21380c41c01503410741160400301c070070450000c106592280d2001000307c2056034840d0b43d180315031201c80c5159900001146000310742079a404040c0040c80b00070b401c00585510110301c01c0d0745009442d03021005424410800d01085c5030340400e050384208403a00f01540d9514404010902d06a05034590001042d003881c01d0008204002c031300ca04417a42603c0458841001e04410417200070300a04c00c41038039502910801400d96101090801c81544180d4002404864900031400780e81c00040e00e171103580c00040c0e011801c0900c01099000c001c134a441c080100c98029690304030300002c1801800ea05035012651058501d1064442e400656440f03419116141030580c4040c165004d410301c05008900300a80c081204800b8609480b44607416583d070641600d548014824205c4001d0030075a485135440300c0100200d00c1640c0d015000d00c40d1041c1c600440445418000800403014001e1411641007404100201c0c2e404240140440c1c41119402035240c0c0e03c0c0b000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 516601762 1250 516600512 516600527
    0x15060903020d052811030706200c0306040f021e0604210f0b070906050708040303030b0604030f080d0b01110c0402090414041412070503180a0905090703021f080a0b01 73
    0x6200440e0100ca20002d0f492840340004d00000c2d05c41e0540100301c0004908254030352405002d91000182d0700d50b540f070402c0650305000d990200303060041c0e03001d4190200101e0704109088505031a43c040441d40c42c021030074680250201020440310212004586030005400b9115900c116180c0c44461100910090b40c90740301034108542c44000d64410b280181380c0010f500100300e62001c0030a0a0b4000054203e0041040ba0110740d404036501c6d242030b04694080e8020f0140300c4031160010b000344000700c0040c2280c0c044032043c1d0b0046148a0311490035182d6041640c44090000e81004101d21180e14090000034071414940002c41c1d0140e00d441e00322021800900b8101c268164005480c01884240050280f0300c030031b180001d8041d2907004d00c06559001a5200f0103100800542c0100701c42050050064109442d10100178100c401283e40d9600300000d0301c200750303900c1c5da04c1c0d04072110130030861611900c800c9240000d9401244456000c01c0094444070005240c20307000e0742c481450541a0384503a07034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 516603012 1250 516601762 516601783
    0xf09011214040c08010e0c1201110301080313050f1f050d090b150f060409091e03050c0607030b030a03180e0f09010c030b0904080901020114070c030315060903020d05 73
    0x70810150203036004070740c800e8203030340c00d076980107190802094055040c0503000c01055214014229550000180308140c0f5102c2940c017155580e84110004500c4207100860003084120021500c3e400d40d81c0c070501c0e211200394000c520070802e2264a1141b17444501c200a00d10b12440b0b1060a0001c03140000d880d244641c1c45014102c510701016402000884254140180c105074940e1215080388010701c40c82560410200c0d078024002d10040080020f26003151340070764800d480c404100c50201140c84554150281d0440c0840c0e40403400d82d2790040201706e041c0c3c1c13041e0703070345024041110b10302d0120f500c0302d140603800790070000c040300b00c5071844021010f81002001001446400c0d4601486000c5211a0940b4200001d500f404501c2c00300034840c0c085c184080320002d003040101c0d180ca5907038103120f03400aa03050b41503540b02d01d82c061040c07d01c40311003842041c840d1101d0403c051540740040866850120340e04658a06407010f1240e41e0380602e040041e04d9060794081c078145c0d050304089140c080310b1070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 516604262 1250 516603012 516603047
    0xb040b0901030b1f0906060e0f01090e09030408011806141006140c07090230010605030a09050601080c1003020408060f070507080f040513020a0e09070e04061e0f0b0f0901 75
    0x440060180d04950106d8100c810703e944480d244404241004042881201101d0000300c05c403006004000784c811401d500460b031403086130300c1c2a0303803080d1050030740303a0301058144500c40a00480080c801607000b065500c0d0180c07221141e19181140c150020602a80107840800541012500c8030610034011030710314500704004c448006a4500c5070b000079500060ac031519003c651b80a000b400b13180324050500101495800011070303070070813408641d0703900000e040f8141c1544902071030b004a0030501800303002c0c1403050090120341e041b0a0521181d020b02c0342440d420548108000c102180c00480c0143e004a54101d5841d4242c541c0d01c000c94680c050500c0c003030208103001800000040c0e2650081c0200c0e02d06881c8000758980c2941d88404a001d8a12803002080c20080040c21915200074081da00420a0506404026408010908640e03554000d03912042000344400006005035540758014000c104490360941d0418421601c80e0190720f95004852038041403d0111781e0080c61501800d01d51807 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 516605512 1250 516604262 516604321
    0x5030304030606090c090324020904090609030305010605070f0210020f030a0203030106180501211803020c0f10090303050f071a180d020c12010b150a02010b040b0901030b 75
    0x34200007005104900c04c0b00780b010719014000f058140218003502c12650040e90900700004208600800f11010848100820380d081102c01c000369624032881e4011809440002215030241c0345c0a0201c1d241038000740180b01040c000c0c000011111807010800c1a13058503166204400210203030700e4920a540002128000452400e00450b8000040d5048031141c1d40c401030450140b15041d0340c1d0465038080e5500103501c0b003c06011403e0b408042c00074105030110700080c3c81203c005001d825030a10441140141c1000c0e004c181d040c036103a107100c0e220030f07400c880f011142d280e090303800741c036240c03c03440000c081c80008203940550380c6001044e544a1a00440480e05085480ca806580d02c0d4045803030742000d40320241c1c1c054020b200003480d00313400c0c5030f507400078511601c500040040c1c034000c903882060959202c40900070541c94084020041d4552450250307110b50301c3c0035003e4250f910005800d800303149000c40e119500d94030700c0c0d0f9035411250404485c2150b926030380308108915400f0495032413007108a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 516606762 1250 516605512 516605519
    0x40e030a030c1e0809250905100e06120312070915021609151d100e130206090609120c01090e0108060117071d150108040201200705030304 61
    0x20004284031000e99500b0030510a44200582d00792860480088007019081819002240180d660b5500194903201300c030f40390000d001001c4100e000340202441403184ea0001000b90040d2402034540010248502c1c2c284242846001444440000c100d280300342c3d01c0b960043d15070310b414000c4402003d00030038032000034a40800050801c908031300c903002c400b01e00209030f1403801b80b0100386841300d84503010380b5204441c50300500101070481079501c0c040c031144060001800c8040440c4004c483c0c20901c480401500e007010414031107a910394021084903d50004010110b01c501c552055140d40c100d6011b80c407071030341c1c802152080c000c0c808c0b91a004480c8280655048500042a500c284401d81c1c4166182d40c486c083c002e00c000e001e116420385d0790710074001801581c50300c40566140024500c101c404036a070f1046064144001c800c0c415000010142c1400000100303118401038108080c20608602d06150380020440302105c401c1415800401103140309004003440903400a200080031661510707103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 516608012 1250 516606762 516606791
    0x5010306052d1b37020a0f0308040c05040504030201291509011413052715030708100f060518011203050d0c11120921070504 55
    0x1500c885201841610501000b4200c0c03200010007281800161582030721403d550346030410322920b045203c80403d0214001c40c2c80804581c000d080c001000950310118403041c4c4403001d012102514086400100400e0041003a0301250010345030b140c94012a0703651281880885e07c49160403281d1700c981081b0500050540c150091504580c41410540d0440400c180f1140040ea40790701154111854815034010410107070701405020764103052206000b0a40508400a94400b00004101c1c000c0f0883c28811824400c0003c0d65004164140b0305c460751700401e14504503a802003241005400203802403c0715102402441c00910140c411903400c0c1c00724202c900c01074560010044640d0703203010340010b0b83d894000705555082c441c07040e46228a03400c0900ca410000100c4009400740031040211030614182c5e8131400d1041001507844030a640d5040480030704040541c0400290a0000c1c801082c80d036841041c4101c10301007209009582010400841d0b0502d05643d0000c0d034450f203446009041082e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 516609262 1250 516608012 516608021
    0xe03160806040c0b090312091818070504060b090405100905070c0b0f0411060304030c0c0b0306010809160b070201030608010c08060a080a050604232d031c021c05010306 74
    0x902c43c0751030050468881d601031945000e034240c2c2c940e26501c5881800c0b00c00d088140140340860029060442c84010a03408031084002901c1100c0f00c030902c98400740c4400400d024030340140c0b02c100e50501540d0300e004045045805140d8000788519524408240d00a111070020401001d10040c10301c00c51a06140281c0b52030480201a25402e810200050100800d104624403407684050300d40d218001d900c0c00e100da150030050044007400030004000307001c1405614200c00070180300120320780e6880c00b000010050740d406000c1481540c00002c24885040034002c40c1d006a445090085403144600d00048000c6c200991012441e5403130503154210b640d50000900348644400d440d5817034039964449040d5a900c00e880c0001d0310a40108003c50001421410a82000d1818070940051503d4480c5010f081151280b844040101c001242a210900140c4490700184148001e941860880550442d41020811031000015400219400b80c1150442d0300003450303017446c20401156842e450200b0051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 516610512 1250 516609262 516609271
    0x90b120d20010e030438190816050d1401090902041d0a030518060a0305090606040606050313080f0a110c09010b07110f03030d06090c08090d0e03160806 67
    0x44004501a00360710350500030009400952401180340900e0035007100350440400c0311280e00e16000d426442c40404c01030341e901122644a0046594031711400c4c0d0300085181c2c8400c00441030244117010015401d8402c0e40c04121104203081c09a601c288211000703008202020b0402c000e04100800890407103910390201c0f64044c4256810401c03498000305100c1006084403500d115603000c0c10355035000a01c160042c00700203803404030303aa8440300b411002034038070703041071000ba000030350741d00100048184100109038204074107441c1003042c642490b0000b0300c80d01c4014842c11281c08008c890b4000c000c0b070740044810780014096030030748581c50aa4028aa02e44a4194a03c3c3d4468140c40344505d10b4020700081c103c81c0104003a514203982c035992015841000100d06502000c2d0a403070b550b075614280010044404000d100103500c0341010b0b046001c6a40900ca42c8003004285010460450400169021072619600342594901500c800091500e00e004070a152800d01e4000e00040300080019207a000303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 516611762 1250 516610512 516610547
    0x2010c080d0f05040210050f030a0207020d0c09140a0c0f030b03071e180c081302010306050301061404060e1e040c0f03030503010806071d06090f04050c131e090b120d 73
    0x1901b6501000c036118080c1d64045242c2c0c0c1c0007000403506401e500d0b801003841d0380c406040782d034010081d84c59582092095038000581641c0301c00c200c0700d0010480d0b042c1c65200044020030420402c49140082036145900411014140d0706c1c41210400d640400c1940010210045828405901911800103443c103609c076050408914403480c201103c114011154a1115941c0303500282e80d0f1324650904c121200b001c05e905041e07031000003080d640c60038055900901140789040f42c1e042e12400901c801c13645158022035008080406014800c0f0345045180ca6a00c21040c40aa4988460030991610a0b565201410492460400104041d04030016604840c0340d401035800c6079555070015035190041d584000400d036142542000c040c0760a0003d40004180588020190915440030a007160300540300780104000104010051030741e0040614003034918114502181c2c101c01d60704041052260251004141c0ca99060a016440e11007072282c05c2c80c007040032070b081c491050001030040201200711038003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 516613012 1250 516611762 516611779
    0x18061109010f020f060c0a110d02070503070e0603100b27042d0b0a1107050f0f1f0506011e03050f091504060203070207080d03020408060604060803030402010c080d0f050402 76
    0x40300b5001098803c0c5946a2101034940b80d561210401190780c0940b032004240b06119200903ea03940800058114003015001400f20504003030070145040b600780d00001c440f071420010802c3c0c946020030384401340044c400c004510b16032000700003040d40c1c0c00c0d1604940c5014601c0002240241000070240c06513024616603411510b0264066180141e50368102602d50100311104000070307280e8403a581c0c024551704000032800005508024184c0c808041500c090f070054400e03031310b00c401c284104000d00003014028250001ea544a00c541c80740106012028a9a10340016050380d01410302c0038a1024100000002d50030100d2000e00200002e58080e840c5810520004190602c0000e4411010040c800100510741d90307652000e010f940001c03c80300c11802802800594110100100020800a80c40242e01c0d82c1c104140d00d807801c074004010602ca207003071800400503020040200c84d0070640a1800c80640e0030f107030030725419502c9080c6282419505c2c2c900088100c01c0c19600081c02948229034205 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 516614262 1250 516613012 516613037
    0xb06090103110d0602040f0f090c02010e120a050d050408211b031b1606140c04060f0903083405071710050a0f0b0a03080406031806110901 61
    0x2812190074007000b072681034000c0150704a8542039200d60b030340038410700015291980b038200ea050034204a0340303d40c840c40f200050901c002ea13030a000302c101c498801d2000301300000c2103a080300c2d07641c840518160b484ca000002c04404861103442102c2e034080c00c1c0c4109000340d04142c640425564040d081a01013691001240c0322640b08804001d8024004031f841a1800784140c1014112580003421020010b081c100c1c0390103010220704054018000000c0020702c00c2d18079414541c041e00c0d101210000041d00ca0b908218054600909540070394000d0f213004c00649009010590305a0507507040500200e0700410071254050102c24400319868400c40d64444095400c2200c0c400c00d0390084d0020480c3d00410410701142c554174062030b03d00807034542250000d0786c0380043e000c01c031070007903074242403540c0c540300302e000c000c801401a4440c69005946c1d0207181071171030f00c50850602590041c0380815403250062401c00035071014051040e40c000f001005203016081011840360310000c8018045111072245e034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 516615512 1250 516614262 516614269
    0x1021801120501150e060d1841100501031b0501020c090a022a0a030809061b03100503071205011d0d031d0a1101080a0207080906070c1d040b06 63
    0x14100c3c0c01840032810f1544400c007040c0c0391030301010443c40d0071010038000c54400c5d81a0380905501c2282c231800100c40c20740c00d030410780050120b0a651111208500c0105550712100c2c100440081141020b030150a20b6644400e90a007146141c055107001d00b000008000d00102a114420021046000ca42c85507035400059840b200d507541000d5004100c0d500040c4c50040c5900103014082c11665000151400e070310b500c2007100c2d10b4690f0300c60303d13a10549645040603004031140da0840741c044000c0007030785009a105550110690b00c040801c003004004900c40e103600c03000381000b82600505441009403101203040078405000b105a1f95907091070880c1d400404200d07400b140c61800c84c1c001d01141c84c0a660241d01400304034100e07070110451041d0204801e1424480c1c440c4051041120344041c0294400040c20010040c20006800d0720400c0040300241c041000c69066001c16148030ba200d2905060034980304225030300c0040314440b0008840d80d08010036141d140704911841140420340c0765441407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 516616762 1250 516615512 516615521
    0x30105090c03251206060b0a051c050f0a0f15170c0d120e0609040501140102010614010203070303150503030406091703120c280f120203060a03020d140102180112 71
    0x10743c1a244480b401d00440e15190750a1071a10b01690011900302c0d9112895141a8041c0e5219400a00045a0b4803201c15051510300e035046a403c50900c01408d000011856844002c3c01100105644040c000c2031746105800030141c802c0d02c0b03807100c107500da032760f0201c13495214100c48848040e0140c4903080d4100d00d030500c02681d075282c00945544019114141c2640e008411444031544007105000c020190703a01ea0244501801500117600d00d0880e06000290035181c007600304200c14200100380030080d980c004190741a064041c0380108a50300f10140c1b074950000076801c49500750100140120b03c40d500903601c24211844110a455032071a400b401c942c582c0590000103540541c60000300c0d9800c880c0700c001d40f46401080003000070b02002d51007000c08829995240ea400702d1008244102415000b880d8030220072400c02c0198a0361900c1030001d107050155000081c419031000c6603c4080c4030703680001c4a80410082e000b15501e04001c031408035040d051811690010349c84070008211b4407154043c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 516618012 1250 516616762 516616813
    0x2090d052e0615120f110c0607091a0d02040905090a050706020604120503090115030b1902030108031e21010e06060c0706030221011511060c0313030e030105090c03 72
    0x180d00d40083e40b1860848480302000c0824980e03940728003981c91040824030640100b407a060489540d102d40c14040f030350070000d0062101e01807000c00d400c1000400d00c040c482400310011482200c0d40c4122060000f40240510f400c00d10f03c5c00e00d48800c000ea84040010349050050040301103454040d51000203e0f907400303040320000c0080c20700c1010b40c954076014201540d04942c0c040000b2848401446110302c0c0e40302c1e00c0e801a140d0600f41030074001e084411558070080303070b0807846040d4074540c1025011903907841400042c02c907501342910001d00b051441415540ba0040c00000407101007607100940d0301e000070a02440c02401128008a812031030308808942e1207121100160a10078034100c1c056009421442e00e46080b6001683d0001c40f07032240e80d40040c060401142c4102000d9150303840141001c0100105410607882081840307556010f000030307030764031248908007a0440f211a00c5d040b2030007400f07203101d6501507003424107000c1c19090103e5800501c0006a0032161140030300c0b4001c048021500300c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 516619262 1250 516618012 516618029
    0x20409110a140d1d1e0118120203090901170d08130b090304090207150f0207030914010c0803010b0a11060112140f060f1e01050f0402090d052e06 64
    0x8455590400002d02411910046600c0010b00100401041c000400e42400e09615034000c05031030401d8404100b0000681200c800c0204054102c040003620f44040b88500506401d201780b000c80030390340c420011248048070152600c002540d403007500220b0811040e00a11244c040e28208480a52080b80789034440c42280060010802e5103456900b800d60000c1d00743c02c90790004100200d540842c50000b014240e00c01e9031585140a204c1117003004550140c2244c44199004100b20000300e03901c50285400c0c0d0300c1144482c415403080000580351004c0050f8000c1c010360300400000782d0442102c000d003021913a80e071504203441300303a60203540d01c0f60424068803800c06d40340a01d110118002ca2042042404020300703c42c22051f0300801f00d4604201110940c1603102c03004200078a4460209102c6200226007a801e41a5418840041c800c0d64810590a000301c5d0301203250205992900154000141c0020548815140189801455590180789442c216114000e07802c000c5403d44901403c454110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 516620512 1250 516619262 516619277
    0xb0f0a02060c18090601020f0d1106010e04053417010518100207031b0b041412091203090405010b0a0e19060f050c0708070509161202090d080706020409110a 69
    0x7501088800500982400e0451089070814150b160b800c10113181c503450240c0395001c14070b0385414032b207250a0341600706e010002414024407002a000003058601500c0c5030405800414210208291032010030468034801e900c0520001005500725050402a9440074000c0c0115590044448002051201d00c0070700c036845808030241d00801c1350702034080c07540f00c2e1514900c20b400c15061194041114501a10b501000b1410720013004071030b40c0383c600c420a42c03101a0100052000401e50103000750224140581c1c00f000e00841090424000c407003100c64028800c000e02e5845403d60304040d0094041000464100200704c01c0324a04407030103012300c1080c0000005520300348401281c13201c2e000c10110041c003406000d011a200400d2019001800c42c0030001c0030340600c3c01c1c0800c01c1568000c0c100303440d43c0f10202d00c841040b60344a020103000380e081407005070361040d0050200d10207450b84000900075810102c0d92103300aa550014030440302010b07020f21041c04100d42e900d0540c410b8013017480205006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 516621762 1250 516620512 516620557
    0xa0303180803041a2a1c110c0706020607090320030312070206070311071101200f16031e05030f0f0306150a0203031801090807050307030f030e0a0602070501060b0f0a02060c 76
    0x3003002040c412021140040c511207001209105480e04402850110203000c03030310316450702302000500c008141c5072004211300e081240018007000301900016010000c0b6041c1182c0c0544100c030200960b00000e02100d40c0c0f00c1101054441129080d0b030b0110060040c04041035800d4428082c070750402029131901c92030311006035500c0603021448468181403289041c1c14030080b602c41012125110f109502620140040d04007a5003407120400a12955114403c1d092005c06c480c0d1200c030001c0000ea80f81c11054190508156185020b104c012012015000603056200078203240618000c45052f9001840d41096000440c0280140c1c2e4940006900900002d110f06141d88040c00030010800c0c0002907e8141d0740359040d16910140c02a24203070f10000d5210200f6070710005201c001401d9180401140420840d05525116680c0d0068102900130420b40b06009080d07000c50000c1860020b0b4035944c5c84030391704004858100040c0300c405400398000003244a44807004440e1200080c0c601c4c1c9650301e52 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 516623012 1250 516621762 516621841
    0xc0513091805010207050f070905190b1f020706020c1e10050d06060c020f0901080309131b021c090806271006080705030109050a0303180803041a 64
    0x205050401c060401c0e601c600081070003840140000790254001c0e04103c119980c0e220302c1c02201e0f50009501e0741c41c10301002035000c01c0901d01c1003040501c00b4045081c05a900000f103555007c8000d44800204914014203031680015025044403c81d4090360300382d05283d0100140d919184d400d440042104181501d00e500d06000c654000c2c20450801e0350034101170003900b4040320380d039400200208011300d602601f0740c038002c10b1002241c0300446400045606040c1035989074040e51105e0360003440017410101034114290803414040c1c00d41241140000c0095500039500d0195011013241e01d034001c003e50203c188203800c1c0c241030701e0141c17004001d192249900c0308064101c5800495444c0c011081c1c2c0340c0004400e12403090400c94601c000f01d001820050700170b040800550041d4807a80c5071040660001d0f9010079038030303407550300360a0004880d2042001c0780c500c0468124000c00b108000010001001211440c250000b8215145d0078441e9035007103422464000008031403e42480046004100e83c01d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 516624262 1250 516623012 516623021
    0x9191401020c090610020304080105190509030c07090b130f020417031201031205040e1503010c051c0504060605030a031806110a170d09080705010b060702060f03070915020a060c051309 81
    0x17000e4812286080c1d0785600403801c590301620f02c02c1d811030780342600710507890b440c0c069690001e01b414040c3d0301c1d002c681240541d881d216440350404441e1074031030750792103541d46a89240010340305200c01d021040c40560020001c1d0701c203000c1c0a215950050b00d80929401c0001600c0480329030281c071114590031a12040540766040e601103080003001c020106101e00072400c0540204400718135020181500001c041c00e40701100305400c10460184642c0b0040862420707079022100071000001030984490500c5400b0302000d400560301403183c44c02400816a0004c0c940b0300c400d000b41c030405241340d20746508030741d0390725261b5890f907481e80829400804944020502600e03001c1c400d0795903140404503880780b0155141c41034103070342d545800b15054060290a00403c118014200d03041e07031900a07aa0300055550041c80d00300016400c010001900c0c01d8083c0f55100d018280c440150481035001c0341c030007562040e40f0309007110158242101d540382207006102751820903d4074000a44003506002d101d40040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 516625512 1250 516624262 516624289
    0x8030f01091107080c0c0406091a04020f0a050304020406050619110c0f0f0f040c1214010602280203010510150c15150308040605071202030301061e030209191401020c0906 75
    0x80c040c03458101b07200c1c0c1e25031080c0c1005160400700810075950042d401c800c1030011014640c0a0350042241c811003455803800c40b90785c2e11050600a45079104d6001050050a15410040c0c002c040003070b14425140000c40c0c5014001e1496658a040d0291a045c00c0c0d16a5036031042140c004460b100081c00620304a99140d12191000d0708014006540a0000d010b071800c0c601000c0109038146a03441520105004200c0b03882c00010104181d03500d0084000d640c2c0301c400d00701005038201c00101041020b1009040800c46400800a0203075052488841422190910411b00000b9005901300c120314060341401510540001040030b5001410246501414a5040c4601039051029020000480c0d03080684083d002035070303403142c40f103081e0301e84141809103041258081d5401403004024065012038941c1010202e10801c2e0b0f13100404403000d50280c01140002503012409021100f048048030000e88219400405061310f50002240107a8540b09648001c82e0440e80c403c002480c02e040c50340c1c8911a2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 516626762 1250 516625512 516625537
    0xf020405061c03030f0b0603040f120c0501110a030f090209061c05120702090105030f03041a0d0e0a02010e010c0807080c0a120206010509070f1e03150308030f0109110708 75
    0xa20424242406001e140c2d0000c81c0800d0350390041c9a0020130f030f44514100e240042d43c03514a182003546030f404c0610058080104482c203103a400000152040000b00c41403a4000000d00040d510102211410b410030300e03a80c2d000078074003104c503000030225000b084201e070f8018101340f50503254403082c881c01d44d8008a2850081c8900301040002600c100f1080c10b4100c116a88503844040ca03104220013140186d00283c420742c8890f0002c640c015012046604903441c41018904181e058100c03a0a00c0c010406400e82c0300340390208222a0f0301c7d0100e42907841c01d00c00d90b110021070b001c0da401980c070502c8000010f001002c0c24041000015200d01c018100d040c4520225040c80b0313041d54442500110540d2103d0050f009503004100e28180f600c0100e400000c10704100080101281c0c0003424520300000a04100d19420007135071016019901160445d10110849a400c0340c89090542542d40300b9540d08403207121210000640da000c41c89031851140d03602c92010314142840d00c62004503000103140049 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 516628012 1250 516626762 516626779
    0x906150d0b0102190503180a08030d15090c20010203090a0219080102070c0f0f121e080c010e060a2a0921050c041116241e02070f02040506 61
    0x80300f1880401c4481382e84250f00550365804805581703640c2c92002840c1c6170055001800c18015814003206a8800c2c0302d240c440040e030392505106046036040d203540110304080ca8a60718940e17039076003c00c41e1050035803220100c1c0a00705c03036051060700300c2c40308580c10703602500220321100040c506010702c0e00300302c000302c0c611480543d207415229089038400c4100702c0383c42d1180c00c010082007480e020880018a44550f411602c1d604c4d2101c5046001003290005003081c848003d204452100401005542900111020b40f5001d8200360f0a0003480c0052582c0482d10032039000800c00d80160050303140358400340c2911040549580c0042c13000c0c00e0301ea80d06200f84103a0b181e002c01d90050303c80c1c411945480513604040b1010407803c085041160540a09010b141003102d40c0e842600d0320402c0314412481205240d072102c2c42418005026400b507001d070181072048031200901c00c86d43da04404110006050070041d6840080070384400c030310421400800c20714000c0455405440d0643c003040c0d0100c0d02074922403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 516629262 1250 516628012 516628033
    0xc0a02070b2a0c01050301050d080c120c1e0a03030c2d1d0f060d0e01051302040b030304061e1b0302060121050c10030e060103110906150d0b0102 64
    0x200d858000b1481000c0790001803074066000115141190010803446014041daa008103000034500d20050080c0741c0900705020f00700041100708800c0b65102170628059078102c00d060150340e00f103540000d1212034184500c04200e16202d628a0917202a03082032401040e6402c0e10766002e401402c2e61a00300301c01e01c020004060412004c0e040704945101d0324104c1c000c81c540041e07c003e01020321012040340f5034502c4100303d000b20b8031004034100c4011021109580c07103200d6200440040e00060b0060803195003030a061180c903007650300182c4841d510072a402d000a017101000c0c15600c5c020362080800240081104683c56441c116035000301a0042c80c00015040b804841b000300508060300860050b408100101320504010b4407048600e0351200840c81401035076118680e03503061005680303125003680042d0410f0540071740c1c00714032907215020581e011983c0d2410412880c6d040101c5071402000c03c41c4c0011914642301008000001400d00d4039405c2904510543c0c004020394460507040d40728551200c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 516630512 1250 516629262 516629279
    0xc020c030a030504030c060806100c061e0204050a050904051f0b0901060f0924050f070c0312140f04061d03070906050310020415140d090b060102010b010905090c0a0207 74
    0x2048034041e4603610380d643c1c0740d0300d8080c10a05499201f0410004040700b4013440d41d55001510704400c0c000c2c43c0850182445080030002866001d00001d01d0315400c9416203500038032500a8000c54500300e5036035100c2c0b0f41e69403c1c05081c0c10300f107600904540203480c01c6c0841120b0742401c0b001d00300505000050b03030b0a44501040d0f0800302a080600490305469011448546c0314046101500c00c070581112004008101c12407200d01c40c2c100881404030201c1d031104883c1003103003a90f02e240d03041916550141d9881c01c10115052420841100094950000203140810001105e55240c4210394451501e4540340d0210350031090100803520000e44d40d000b004550f80c0c100401c0d0003520f00180d0001c1c4891130901010f00c0c11841055018455005010401c6002c07180c441c004c4148000c0e050500c240c8900c0744081c1c019205070551400c4413450305141da8140003d03586540d20903207081e0020880842c0490041d92a00024072070294403291220000b41c2d0a003000c00079080c0e00b101401242c1d0183c1c0c403680f12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 516631762 1250 516630512 516630523
    0x306010b0d021e09090601030e191b141021090302010f050c0a0e0118060e010507140a0c091a060d020702040203011203081803030c03101203170115050d0c020c03 71
    0x140f1283d00118003400c0d40e181c50400c040d004142402d08122502d400d9002c039842321b400f031a40320480d140388003028080c020382c2c3d034080c003481c03c0a851201880c0e0321418491454000001d4190050034456007010002d40246602c4e8035000c0305802e072020081140792460080c00054904070115502c03000c0907a00c54915001d40341c001c00c00814196203031950044000c040902844079241000500840803130b46045141c00722003035907003a00d401034440340d142c0d0060340c083c8034502c001088051040100321040201203601400345100e247c0b001e07041c030b82e1001392000381c603c40d80703500722b41c8000d004001c01d49141c600003c0010394101d20300136040000302d4000500b01e800c242e0000c0e07a404e810800c01d108055202c103982d68400140503002450301241c4203001c1e6280401401c3d414040400004903503000040d105400c028800b0228111400c503091030014003070428103e840083c5c0504078000b14211050403001c0c2ea58030074a560701810500810241b130050300c040c4200500f513000351311030941c4a0701c00740309 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 516633012 1250 516631762 516631807
    0x1091806051302150406080f0912030f090d1e0305220b010e0705120a110d060602011401141e0a05060301240302040614030403090f08160905060306010b0d02 69
    0x20214850010b60060002000004144408000c000c0009001c078a0300640c00da9007190701050700d800180d6403a4041803802c4103800c1e140c8440c0307001004005908005040c00c500c05c558000c25500581c02d80682034400c0820b480d9010761103543c0500c60301e4010b21950105900c11040b03070040080101541d00d001c10344000758002d07a2018100720050002c0d0070310080e0650881c1c8249003035480c100b144920401100d4024100204c2c4544611010030451a00c500340c42c59501d45203020482036603502e030083d000b0088018007150302038807000009058005800c400480b80341c0a0f0150959904c581c0d0300c100c00c01e0fa45c6181c954004d85048010070241c450802031800784c42c3c0503007820803094045145e4480843c4200d114410540100001c2c004540e2003100c81c40300c00d0101c0300d2940c403615140b03416100d055081d007100d1002c1025000c0000c0c880c0c070000f040054014145840040315495205480903500304035030040d01940200c00410602041800500008840032001410244541c03551080040c03c41c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 516634262 1250 516633012 516633031
    0xc320a0905030114130b13020315090607080601020d18090c09031b1a0c0f0d02011e05100501110319080103020111031306080903070c0e04170a05030109180605 70
    0x18018070050409108115203034144024082551800700c02510010b141040d004042c0040040402e0f03490a43c0e2482c2600d243e0b0007001d0703074541910b030280e0303a40b8080c0844016643d84601400320316294000d152041c0601e006901416154035890740075201c0003c441b4444903c408140e00c0042c16a65034031480039085202d5886240c0c01c0d00e9800c000141c2c05942c0320302141d424080744200a211000003044d0541004410080e0722000089002c038117021081400e4a101d010b5031103140400381e0b042d8003040c5280d89501160504000398104032088617021103035910401b40c000380900403580a18410300d10755842004903441d02d050310000780c1251020b01030344ca01190126005000315030300104211443d000300310040d400c0592a40c00b1500c1048030f44241c3d42400160070104213901e8003131040380e580c150004c6800e25031641d180301003802e00e1021141601d0785140130350b80e0200c0312414001c0b112103850f0742e500d650440c1d080842c458001c050a800e909244015100f6010000d040d1740645031180c01c10300f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 516635512 1250 516634262 516634277
    0xb0408010f061715041a041a070f050d0e0f070305060a0b1804020f0f060a0903110d02030a0b0a090b090a0c090b0607031b0618030e040c320a 62
    0x1e01100c16034107103030812103c03009202035203000c0220015160502c038200380710881450b16141000e40f603150381032a500c40581490404c22060001c0b000202e207038410511140c03161035460540c2110004101c00d00b40d000500208541107130f0300c1603038200c0c120403034460050390407448850182600d003c18541c41142c170783d00f1103000c004c240703822846903441174003003654210703184580100646000345004000922401400040b0f00c181c0e101c90544200e00d800c05407002e82c0d29451070602074000340d82441b0882d080c9104100c59070890400d506032180c1e030b55000d0002e08071449070f65920381054800072f20140b000340c3d8900d9000c000c6501d8211107402a41900058451803049050031040e40601d40c2042c0c54050600d0b0100c1c1041c1c0303038a070840d920181c2500e001a0521000200c0320f9050b4201403000d0700701d909004141c21500080040c0251080c42601e40c80104a2460300780000d5851000051000c50541c100c0a03281e00d0b03030151507070140300e414024402e0251031010513240c1c2d50850400300700002c0c4003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 516636762 1250 516635512 516635531
    0x3061a031e1603080a120f15090f0b030606060c010f0f0b030606010f09090902030c0612010f1505070b06010c0b040c05031612030f0909020f03060907030b1e0a0b040801 74
    0x40c403600c1074202c1d01c0e0074985241815620f4540c050300c184240c4008201c01d83c050f1042e0051a50701140044014038000c2c40124138072485860003404500034414228507015034201002500e100704541014082d018000d60b07600c2604120b0181c109500a540039525001c4050f02e5804a1184103182c4c091141c0000d0128154010305150050052119040c050078911060701c680e0004940b80854044920100d801d1480d4404a400d1a4008c00550303008000482c481282000d440c00b0f0074184c0e4520704038a1a00b40d5201402c00b00781130301407408004160704001e1000842e50461010342e1209040c108902004015603c0500d404800c441c180ca450404000a0003a03103014840351920501020719100400e0030a400310001220a140c001c051015044542e50341d01e01403c104802407402c1441191100d4260203188016401203840c584a140e00b000001c210a0092003036080001014200c540300c0c8003401e48184a01509961361680b250000c000058095258030062000d0300400340040780c84a02c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 516638012 1250 516636762 516636823
    0xc03210313061b0f0f08041214030f011a070b0601080a0912080a0b010c030905061e03010905041101050703020a020d06020d09050f0105091c080a060b1603020c01081003061a03 77
    0xd0050700420054444280700f00031b03920981064000360000e0b0000440040d5002c25038080e0110151180d0300c0c07001001300703c0c06003855083d15040fa000240c4440000c114840821103901c601400100000942000304465500c43d03110260b002c01c42174400203014070107454070392402d00754689a10000300003004002860556028001c507d038401e09201c40200501e03500030b040e40084d402002d014180100b02c000544004510500c460140c0070301656495031241120005040110307011740c1c2040c12030141a03060751081c4100d420440c0c040e40a4200358445a0030440c404000b113034191000d82d002d0042c100307810b402d441843c00041c03080c0010400359030607100460039618002d1a121072900000d00b807141e00030f5414003c1254604505d04542d035075681001c01c0e802000c45800020304034102280f408940380e09120003160042c080c3c1c080300e01100c450f000441e9000e0007200d4140c4210640f40c020000104580c22200851034012030243d007030900103001c40c0c500400032110782d5040c840d0360020803c449 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 516639262 1250 516638012 516638027
    0x309020618100e0a05060f0d0c0810080d1202130806070203040303091d040206031e0c0a030e0601060912020112050f041a010510122003090c03210313061b 68
    0x1841428480509502c40000410604c5180b02d82d9005503400114070001f4103101085032070400c00030701c040102c120140350041450fa8221202101c0340b117400700118040c0c00010741c0c2100c0040f65541c0100d80e844040103140a03400c50340710240c0300c031460348c4d0116036101c040c880217110760310740e9008603122442d500f8000c211000320780c0115141410081003290280703080480f00d03030054058402c141d0f2a183c045a40002c20001c0c01d103010422413131018020540c0d0958011300032001680d40a01005800090030368642100b8070071640401c0390344900304800e650340b1130ba203c0214014181222000d8040040805a443c1292001e14141102040004210500d20200c49d40c0c0d003050180481503040c0000305409440d000418001d01c031509156072800845500440c642203c0d0810303c61903150301c03041001d0725401c01d5510b002d044c025045e041f48a81070004030560340c0381c00310310805241c03907402050f41a550320142001004c0d41d0b80349003400108840340510a00ca40802107094000d0703807060402030002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 516640512 1250 516639262 516639289
    0xa0306051203040509041e05150f06010f0e0d080d020901020d050c0a030305180307060905071d0a02070501060b0a0c0209060103050c18011b03080604051b04150309020618 75
    0xe141c0c0c8000668121000001d44090b110b00355202001600c40f070801c000003000b064543d030680054082d01d101044400b1a201c5010302c2c0550b0241c0554032a2400509640d100310350b40c50000d0aa11601c504044c46011605915640503040060054540c1c49500096200b11401d4195540001e84a0f0321540e040181182c900003502e00f480c02c1c5001c24400544414002001400b05610703013002c00e105440901d0b60481e00303201281229641c1c03002d464110301900d15144161154094641e0010f00e030305800744000342458403246d4072920f07542d821721944000c0d0021581503609659640002c503941c9e489000422644200382c45005420340140704000c102080200000d0406041600748511480c071074054810800020011210a41d1008012140440881403a4481403052003007001071503002500305000d04030a680510050741c404844151a0010000302444003108003c00c011043c1c3d04018484030756114500071820501c15000503403980c100c0004042990120301d2480802c3c07626401c07044e241b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 516641762 1250 516640512 516640519
    0x51c0e070611030318030f2b0b06040915030212070320010e040903020c0319060b060406020309210607050c0c010206100902071515030506010e0f04030c080c070b0a030605 75
    0x1000d000540389501c0b8040508543c41c1005c181c00c1c2a0b0030003900b40180c0d2070784000c0c0d4a0050300c424140840ba010380401600c0f0701d42d8480710201540780300c40030703000790404200d01921181c641031500c0703441d800800c5541c486209016400d4070200c01a034403804288039182180000303000c51421420117011300301c0c06100c1c0d203d56160318444402c0701d0b60014048009a841150b0020340c0c80a5402e05a0822003440c005e40d40c503018040724420302c80a0b480b110034101d8001ca07002c0100e0b5503442c06214481c860383c0590fa000d45d10901c01b502d1503241035051050301800d110100c110804000104600e40310041c0c078401e001c688041616801c9400410074910f0b440b4091005090504014101c21000306240c010041c00399000942c010500c03003c42800081d2601000081001184030701d80c0d015824002d001c2181c01d802208000150031041500542c040d0502d40e1014030107884640c1d06444018845100f26100802070145a030f0111080c442c0d60700038024680c0c0d2503070b030b00e00e00c06008003211056040381e440b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 516643012 1250 516641762 516641777
    0x30501030c2601051807080c0303070602090a0803030a0b04180b190e0a0807020103050f0f060d17220f0b040314010e120c070e090c04050601051c0e0706 67
    0x85000000c0c0c01c802c64000c040c0c81959807160541c00e9990816007514003019600300810b00c84405034103000c03500765006800544043d9074907000015103c50086c10899899401800800b01013045503004041902d00102011501592000c040e41190003c840d2130325016540d800001aa00345802040f040c88641d80c2401c50740c1845a40d034800b5400043e00d191951800c40c0c000182000b07031035002d100300f4407180084a03540c900c6840d1444040c0c0c80500100d000174146800308224003203911500e070050240b009420b05558800e01031007a0250441001c0e2000280b80c250310325041c401034010318261400f0200960304c0111140910120345290f40458004074ec841001c025645c2d045080d60107807a031081c02c02d41c21500000409002d040840320300c910781d00589000d00c8001521000400c0300c004001c0a40320150b940c0d500101003100d04964001494000030301c1d0150320314090380802e07400601411b1203820101e00003443d614441c5085c5441e00f4442d540c0c09040a095400c104c003034001d0509241012 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 516644262 1250 516643012 516643019
    0x30a1205162a0804050406061b030c0c0302130218060a050d02070c0e0c0a11160b210108031c05150d03020c13021216090b13030c080c030d030501 64
    0x50151203030011981003102042c82003861241d0340c0c1400da2915070301640c406142500381007050142c1e0151260f01d120b10b01d401c40002d00c140c042c02186409081c0d1039030b05148050300c0d0310251000c0602103011140141c2c1d104010005a45d0b104280504500000c00140c0f500c13980440c2c1c441030880100d980d84980070500401d28465804002c07030700849404c42e00562510040e150604106885422100c1503180700010010001d00003006004010110307942c00d5050214064007a4070381180003203a0741d011082100c03e10092203004014607005031600c8050707070a4146202020740580c1c0070f0700105a207030000917603184c000514803203801e508070004d03108000c0d0341003166140d204c5a81e11380f00c3c50301407001040d181f010f240c002c0c082941d40c1c1b03002805034201e0302d0b01d14428a00951040c04d082d001c411b0b000c004074000e8100c0360566896840f041e1100d5410340e007840c1c04081c03545c00c0743c40a4452001c0319035001c40001d1840031407000030481d02d00100100800c44d400c03d410b0090a221481c02c0514180041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 516645512 1250 516644262 516644281
    0x1e020a0809120c12151f0b07030203120a0c030c0e09130201090e07020c0a081603030302030907080a0c06030b010c0c0e0a0f0203040c0e0903120105131805030a1205 72
    0x35159101c00311081c110406089020310b00b404042c2c051190700910008a040e9290004280c0407549440c46205a03540d940e205030035001c501c4100d9045089404056062260782102c400818440d070003801100c0c1042a403041c0c00100801c00c58180c090b1a45491341c40910135010302503641003103254180784c00c840e066100030400c501802000316090b24440e012200559009401d041c0c058015506288840d1500f140080d554018200515000e80000400040c81c002d0226131603100c500e010000102c01499610704901940028001155601906100154101007040800191403054241b1001e4926000b005401c4070910020b85045c840a1000040082c5065202505607400b250003542d00b502e451503840000d060080c00c1d2503001b8400800e000c14003062030071a200b04c4425080c02c06080c1d542d00507094490052081d01038510b648940180b006140094401c120801001c10000342d9001403950000c0c42074410b14191016000001ea400002d903110b403241140560210003404241407101c880e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 516646762 1250 516645512 516645517
    0x611060a0b0402040f031103070909020603150f1c150501030f08030a1503051c0e060909040809090709093804060306020301090605090f0702120d1b1e020a08 69
    0x2111601a41c4007455281c5950340c0e4195000b520010a01040080e140e1034003540c2c0a03000380b8054400d204060000500e107001d802022150396010b0055400e5488003214500000d03c8201110b0b40a4a07411060384103498014541440c1c4e0008680d02c581c40c0280c0c00d010f1410000e915507800300c03078107180051005c120400c50300b049040d40000324039031785c1da551007044004240c0c20144001d001c2041d003000060020000304030311070451102490016000c40c2409880d265061402c868008800303005040b128900034a01310341c842d02aa0303482c2c0c81d248000c0001911407078201c0d01100414412842480118024807800035560700201c0480d00c4a02c3d004600c00302c0c0204202d10703074008840140740405a80702c42d0414001158800c80940d16135071196208005000c0902070140545603000000c1c520201100c186070050f415a0003410403201081000e03d03050313009880514445484000c800d586885c1441e16032091241a0795085890b0a840715401d0061003070180c6e10210741c442c01d10030b0301080d4043d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 516648012 1250 516646762 516646771
    0x7050303191d0d08030c12270105040b0a0207050c03030a020102121f03121e050a0f08060603040201052223120c01200f06060108160906050306010507050115030b01061106 75
    0x40c403174503551401c1e50404a40700701a01c0907007402c20101400600100076400441e5005000104840d00000748001801c07144100d41c0a0a1079260f04089441142d1982c01004064010f03000e442c10b0322400c1300800e00e03540c419584040181c0d03001900006154618a00a80140102031412506401070003150180000340c0030181c8481c0600130081342c014020410b03201030b2b00810b4001000302014580140031a006003c244000c0390f0b00030500d03002c403840b500125100b410300030550b5080d42c0390398004580c283c01000c2400e100b6268100003100042d21440c0940c02850042c1005c62164503d0803e1300442060140d40d901410701c0401280d102c2e207011400d0703040d8035000c2c64004410000c1e046050b0700c4003040350b50100f041c0621111480019000708203188200801e880f004401c0e01e80500c200c10750855844c404000400b40401806070510481c0110342081f03052400d5410b0261603100c0600719095521884c0c94000d000104008018840c1d00d1140180399a00f0845100100c920b07665888580051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 516649262 1250 516648012 516648023
    0x4020105160203160602070b09010507110d0807080a021005061e0a05040c110106140108130206041502060612190f050f011d0c0301050615030907050303191d0d 70
    0x4040d0403404112100340c42550b001422100b41d01035490001da403c00b20741c000c00d0014040d528010502c0d0001d0700446415807070603548c4628140da1038590200310040003007500d41c40002c07a010f800100350000080d00826014034031280c1d075807540c100041d20341270000002401950401702040f4407913440f40840d451341d02e091922010f4000e80c0c00d0004801c6a019000b10341e02c0307898800c000409a03800306203c441e1a0202c8000c00106840703075540c098000700952014000b41654000900340515001803018007440a01b50a041c5621074003181d0038600c0c0f07401e038880103030b101d2000c000c46031078283c0345405903411403805404001802c0c2007096080c94003613400350501c06103a030680c042013020864a10300c94200310081041c14204050481518081d0003580b4191094460b10510707481d062080e540204402007036002000d40101000c0f4807608014820405070184d0300e0006001c0e01e050009206141d032201e41902c48412400024052000d10142007a104c3c000c0c1404108540b2860381680c082c0d500700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 516650512 1250 516649262 516649267
    0x206070903020f0d02030f032703070b1b0a030305240609060702030a0b0f1e01080606090c0d0501030804050109081507080c2104150e1c0903050303011212051204020105 74
    0x40046118041e003130310003e4040c400c0503510700101801002130a2103404200445040c0034402d84a2a01c0380c0f95880f002ea4160440e41c01004042c2201c0018103901d0300140c04140441100b205d200d042c200e13a0740058000ca91150100310344241058001ca007884403441e02404081314000104444d4000c4180003030107002c00142030340179558100024072131035602c080708000781d1810514030492001d0646260b03a0444c1d45100358814070700c40400d15410f881d00b03000101714aa030b07002d00304140c00d0000f40c0904000b40c8100032450070728007a4040d1782d0295007d050074a039264900b8000400804990344000010f80000101080e40244090303d01e420041610700401d02c1c0d250b0b4100850ce5110700d9540c1501161902c00041506e01e2039034a042c401e40c0204410340c051010b0200f4003041d9107419141400c16007140d400c04c07800801c0d4441035801e8080c41c0c50300c13141140c0c0369035603140b441c0d10a8100c4415000241038507010403200444030000350259243c82424418000545d54038014007610003414044007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 516651762 1250 516650512 516650539
    0x61403130206130b180a06170a05190f0c090f030206071104060f15140711280603240e01090203090a022e0306060c081b061e07020607090302 62
    0x11114040d0141002c240840ea8490305c440345590300c0200003c00e54050301e064031000850394000c08840c1d240045a0411b95a5556041c0c890002003000520000c820035110812660594551098120400c00e80704000b484805000700500000c1859120805000a014091005803544025549080d6000051501c19108100003e02400c03441d00400c0700ac0108500000d8080120a10a50441c049032900070140056141081003403184040242400c0c0d4910040c0015052007041400d10759480c01c1d51804443e400303200003500603400d40c4444002600d4900312506c10041301c0301041110254810648a41c0c1781c20039422001e00140300e070303007182980440080e544100c1807100b1138045a00400300e0903080130807400d42c0340d0052019043c4568030101d41120b40a14081c0c03003403005590179920ba181100606a4503041d0b1944544d0014407066401142c410a1030700070042d1900490018030741d07101040c3c40d254424a11107006000c10110741c0300b14144035a49801c0842c0c3c6041d242c05072203c5002103070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 516653012 1250 516651762 516651787
    0x1103161b0f050d09351005130b010506040806010e040303060e0f0414070b16060b030f1507090f090209030a0b0414010f02030603030a05031305031201061403130206 72
    0x2140c00151149901881c5207003041404110f0629400881d103510136210340f1050701510004207291802e40d1203440206911500c030503c54a6442d0448040480c0c0e420400c03070300f290059031002e0b14201030301c150005018017081201c540d19405072000f901d446d400c10b442c0101c919030b2a8010302c076039401040c0c10008942030502c6904041c025040c0304900b582e085c00e107030b009240d143c2000c41c0c0607206400e9080c110100c003100031607000202c60f90138100c1c6007801d222054405092014403002c94141c2da403101103408644060004844842114000d481c40c212081c04982c240300c0010000c0c0e040009444081c4403444251aa0300140c4200e000010780b641c40c00c0002c24900240d08001524031204a0104030030800c24410701e11021821030000d001c905131040c07500d0180d0005940d006d81c1900240001c07170216201d44d01456100c940c00c0e03402560000140c5585003554059800d440e8070300110b000503c140c5801016800c142200103200a10310302c0c00c0c0081545003100480b00901c80c000028290960b5103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 516654262 1250 516653012 516653057
    0xe0604050423010b030708092e020405120f010b09160e0a1707090c02150f15060403150b0a060c0210050c030a090302030d020102040b0d1e020319110316 67
    0xa00c4182c005400d540c440360418010b8104860041c00190703c0000144010070105034110074031295156100c40c0403105010f008080003e00c1001001c4d03500b03100005a6554000d00b1102c41c5c0c0300900901a8025609070550944403d40c10311800f03620f4050502c5005509540441c40001d03082c54507641e42d4103503000040e084103040d840403982103100d10220f000c1105c00b10b00082290340404041254402d1104146d0302c402000c040300882c42c00c0b1400243c1055090380d2490b40c00710205034800702c0d502510001840d19085a00191080c6201041100301d01c0c81a2289045035801192000c1c00c00d4136001c0010103200b20950700900031700440060170343c041c0c000c1003030710f90002c107803400d8a40b118049100100540003a02c001d034801d1299500c500800c43c01031084400340c480920510b480c08444c1d000340d80c09000040242c4450315180340c540d81d001c0c000c0d480914001c400da5400c0200030820000c1d0f02e4190780313002a110321405000c1040c010541a40c0003400041441424140c004283c64100c10a80c3c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 516655512 1250 516654262 516654311
    0x17121606060306050618100b07080d0e070e01050d020a1205010b0307120515060f01051c060608090d080702060a1d060a0903021213030308090a02040603210e06040504 73
    0x503062003070100400c003080e0401d41c4607a40558541e4100118041000059401982c0d00314050040341310501200b1054002007021a011300c026a140004060001c0c00312031264520214a4000c0340382484014000b09a46004000855071269019050f80005480411500c21000c0082c8848010b604015080d0030010307c8800050540d0042e035625070f80980141c030500c500b21618080e4000303860700c2d007029025443c041c00340901301094441180c001990030380d10110084140d01d2011501106004140c060000580791076512089a414114981442d082a1101c00c0302400071200422119541c0020500e80c081c120041c00b050300c0f0308090f0011072500000741035180c64020f4504000d00c221940c0c0144000c984250300b10b488060851481d1001070040110440c02c11050810400c0420f00c51101c5070781100410094629101050340003408803074080c0c1c011150041c1800001b0180701402c1242c03e8004014102042501c41d80c100154141c4101d0088500c00c0341e03200440b81258400011301000e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 516656762 1250 516655512 516655523
    0xb060f07031b080d0b0402032401020721030e1210020d020c070b21010806010302010c030302090306190c02070506030f04050312190b0a350304060c02030601171216 72
    0x201400d0300f001c00d010b80c40030200700360799400c14005003203a080078800c40c4d2242c4e801d00c4081400d860000805640e1901d111000d50451241c210041105422468204c940c1c02c025040d21482000501e030103404140c41084540c4901800d44443e04d4a15002c12118050350340c03103c00603980c4000c40c4680e0001d002d03c2030441c036a4401c030180410450166401450540c1e90306801410031494050b40184519003405916403a42202004000650150280611161207405d025080030100c02c0840e10308801250b001546100e480e04030384004942d031007070420010717442c800b070300d001c0c2d003480c0220702d81c0d10000e00307601b0201049070001020300000380260384003003280720a1020541414402c01c560100324080182840d40382c00041c0c0100d1802d0030718002115400358000c0401c9680202030b03d41007103840c080518240d1f1040c4c41c1c46e0038107420b10050010700b54a0300c0d00c40d000c46150042c0341c40c1a0050b0481c000121a0200740c4103140c0c000200002c201c42302000e4074ac0d803100007140c81010041800301c005d05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 516658012 1250 516656762 516656807
    0x51b04020f04060905090604090f080c03041505190311040302060c0708060c0c06130f020103020c01090803270706020a020603090a150516021b19080303070305010501120b060f0703 79
    0x8032190702003201805c49a08031202c500685607072041008440e110000105201c100340d00000c0020214800b03044004ac4040569081580c1c601151038001c2111070071200103000000c030784a14580d40707003c49940100b01d240800103030a0076020340b41c2503c82da001c003900c94140400c10702d201150410200018100030826108203041804510145411086411900d030103150005041d800c00321035244001038100441c69150030054005500940c030440003001036540703500105001c43c003454011f60140880f00ca01e020600984c0c0100c1100305880304480c0d007030780c01200c01044031941c0090782c180380f2a0103e4400d40d6035181c1c0703040039140c0303065440020840c48d41000203080d050260792000b40300f401c3d440340319080c07101d000301c0c101e803500d80045022220241e2a0b005034100c1c18800388864000840864200d43c1e540c5490215103560401c485080000e5140c50044c4980e50741710310003408610401d9010300118500388005000c2e805244a8540c1d14100810404249031061141502610071880740d0324 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 516659262 1250 516658012 516658019
    0x70906091806030516050a0603090b010515162301060f06030e100903020703140313090b0609031c031103010609030303110f0a020627060103020d030e030d09050f090103051b04020f04 80
    0x1d510a07141c806c0c5c6210380d0241400141450180c0501d640d2142d110300040c00aa090200300001e00c0034003505034903420014801100d4204d17282c074146003028003d160180400f07c10020321150161251188081030341400001c0000d01ca4194041e010742d40103060100340e0000c08400f09141181c1100e402d1552820704115109254010a044044d00d0145160f021280300254241c0c0d030341d12881680500054602c2c80c1003180340d43e40c1d403188200281c01444d03185085001000249800c021281c102c0c002d499910300c4050090301031103610440303400601058119172600d0300c00380045000d84006801d05488005c040300c1000c410303003145d4805070354031001e0380c0300c9101480080d0764890841d2030182c1c540d521482e90781205444240c2c00c005008000041015038216400e111041468403011018030400729581f04032a90140000e01c51441035503074001101e0300d040c040000c28134115146a009500480c0140302180001c6041c10202004401481c010030b480c10106000344500c8180e040c4165001c140070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 516660512 1250 516659262 516659293
    0xb0a1706130317070f14030c1e160c0801060807030f0602070203070b0f070b07050c0d0c080702060c0303100b030606040501030c120e010b0108060f031c0c061d01050709060918060305 80
    0x5c1034801c80d140e840300a40d160070360b0881041e100c02e0b81c80300c450700010300245249141000030603a40c030410034940c5017000590b04c0340690440080c1d0044881030300052050149060910600c0c004000b0640100019451074a0308560152050f0300503107d1600042c5240070754404004c060020000c0c0000300f640c500394000030f4142034100070011102e60840b0f10108540318810819180c2c02c41c100009004003100506042c0d5461290200403594a0010320803100580d4a00c1c000d40305448490000d565649090395189103220540d0700001c5d0180014024008941c98a07000d8606556081c280020076032100e220030381c0c00750340300810040c426003805d5810306403c0c810340011072449000e0f00c5100168480c101041030141e82019100c1d055405601d21944d41c5a50100808017001c040c1000b800744082074551100307a0308200c42c1d00d4111100c81ca1000020b56091090315401800c514241a00382c1c10020018400c001d41c0c41111210440201040c0229000364000c50003594030400303c840280600144 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 516661762 1250 516660512 516660527
    0x7020915030c0411040501051315020c12030a0c150e060403020c03150f04060b011107091a060c060a0f0b12071a210a060302090702010b0a170613031707 67
    0xd14080d0060b00007450440c00c050003000b0442212400040c20242840011035558026080417000215404000070304c10340340d02181107140b41c2c990b001e8400d8a54240900c20041e4400720000d801381c0c020000502c0e00e80d07101e8030340c40d1110f034007035011640746000b00300fa8000750880b07520350724142c01203100f40002c0540001c2c0c22200400d007034080d00c900d0b081a02c0c1501c6007440860b00d080310580c08200190000d00c05510074414100305042000280302481c0e2054503190b19600900c203e075a0354443d5800c841582c1c40070b10702503c0216005848c00f07010307448a035103503600a49100712860321070006514103c4c50340c00c03142c0c0398107014003001030300356015042a544283c5d61041c1d003003e2200091540c40456044210b602000a010b80380c0e5010010355494010b91030000d118020783c6540b002c01000582e50121a14001c000540c008100070540d0010003030034402c0c2ea4049511100f054a007040800c03000f2910b82e034410001100304c1e1101a440c2010344400b0151903500500f00f01d40700c00c100941d13801054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 516663012 1250 516661762 516661801
    0x1305070314010803041a0702010314010f06021507020a0f112205060316140114030f0a0e0d090b030c12070903060e030412080d1d0a05010b0306010605031b070209 71
    0x1d5086480c0d036101c080b180c482c03040303001d20034641c42c0d04043d241d01088200001c00121388180742c00680146031003c110007410303003a0030000716501c180000304126503040144480141940c2c00400803410007010103542c0d448103100060001c4560001c10741400045100300203216000340c440350000302c03140c024100c50045800280240c502c0d0101266690a00045a00803c602400072489650a09000c4000c524060480e14100081c2100d5944009280f03806140100e6a04c1c40144440c1000402c2100342c58041d0f0041000e5030241c400b406026501580c5002280c12a2094aa9075101d99124240e0742c8104900300420f0341d4004144407505030300c1603151045030700411003007108a60445070181c49105a208a4000a807031442c4a0089000074004001d001500080010a19420003103000c0416803c0798458081e04503040c030f9010303c00203028108442100324086c00b03456040c004060200d00010340010005036003911200355505203e0300f15107809400803d09020761030300d4603414110600d02903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 516664262 1250 516663012 516663041
    0x19180c0201110717070f080703080603010c080f18030733050405120a170f07120e12160602030a0c110a03020705040c12140907080f0d050913050703 65
    0x550300080107984000d50720441d0f0b0000b000311340c103003000005600c150025141910150410108500015803510040106501ca505d51441c14580a0b0415007140c2c003100105041c450b1140401a03642c21482c1c3d01e41d4403154460790080c01d0902c80e01e43c0c510b0750113400e40003004000001010b0f51250504145003000b0311008030650091202605a14161401036a000700035900ca00d89034204400c0d0b8102a111076501c510709030780f80d014010000e5850000560350650000e400c001800001e90380000b080d03035103c000100c00d0207000d5006a207540e58414005980b0440e52001c20b88a10120202d5a20911f00d60404015074032800e200d4500f030020014883384030042020003441c21a0840e010641e0b00c00c480e055000340144514103024800945010851700c400c000d4103900e0184109460311401410244c426040d00072071405049a07450081c60f41c002c101c065024202c0ca032090b036400545110702c24090f00d01b16490704401c401081712030180c6802004128107082c00c003d400340d455800400081c4450 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 516665512 1250 516664262 516664271
    0x8160e120604060c020f03070b15091302030d1103072a0305030c0c0a06050703081909080712092d0b1819050a0306020c0a0b090d080901050601050919180c0201 70
    0x400240c0c0d69030003c80401c60a1f030400c2c014a804101c2551754180d10005018245e07062034002400034010301d10850f003405405174444040300c20750404000d0803202912908000c0d012000c0d0b040019079a002e04d000c01003505841e00590a95220300c0a268401c805106000c0b4481a89038980182c480d041919071900d60703c41c0c20be480f4881c0c540102e4800444070706864452030912181c400300c881403001070002006800c0102482d40c009064071668004a0007030318503d460309018940070410444111454080069283c01805040304c0f41c0d000084155a2600c154104154160024254480c42d4021000d0603004103034800080b82c000c0d45000501e0040300c20021030802100900d5420f006030140a8000490503003d00005010758000d110301400c08080701c540000300d031384045a400d011590311b00d240c1c1003d20145001604135040fa900105070720000d2150f4034088000a106004022240f88500107040c0004400400001c14801900080b0b025510840902038940041c0c1407a00721300005600e403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 516666762 1250 516665512 516665531
    0x22050607030f110a0b0103060e01062d14060301060c050a02180414010c051611030709090308010e06240903070b13060206010806060d051212011a070308160e12060406 73
    0x1094204c2055400500003200c1e03403d46e02e03164000d01d141c1002e00f09075983c810b4040340583d1b503c80e00d440e07030001501c00c0e00040d5002054000c1e503000d032030b80110705030180c0e0390100c00c0d5a51600c2c2543c2c10741386e10b454001c00403131250420307910745410039001941202d00072806950360800740c105a44103038000ea6115840d034130411030480c01c0b140300403908000104103011014158100d41d1041000314020308543c8044003c1e500004c0c14007540d80d01503504107540700820410981c1000c02d02c0e0040070100b54000301071900c0c1012038000044101000e00001154024038800303c014401c4c0c600381c603000f60881b0705050b1610b131388020940c01200800e210038943c81000524520002c1d5480c165000b4101502107516440184485625424000c4880d4094403403041ca038450704c4006400d043c010b00d900c051142d40b605050340c0e508412500c0180001b81c0070481c54012a4101d00041d400101c147d64005521418040448800c81070200182d4089642ca50301c0103242d000140103401180549020082c07a102c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 516668012 1250 516666762 516666797
    0x71b14010f0509090708090c041b080105061201050411041d01080f010209030c0d081b0a030f09061710050a0305150a0b130f0b091f0501030204060522050607030f 71
    0x390f4034180b0b41c000d900c140003500043c41014600c0d00302c0d0100c1304036080c140360100042d00fa50300065811100b50f14606160204aa000c040c203801480b040d540c2500d000c440c82c204003809401405168001c9403220401d0030b0700e9400c04200d80040c400c0040a10030303603c03044040b00e10710200b8481e40380584a6808540300c8800c040c400c40f015404010000c1c080300d081c034420310225007194082034070550400e10165403003840c55001c0d00d02c1885448040d1000303060928000d07007000411031040c4200881c400042c0185078011683c2c40c441c45555944c51501c2d80d86030f1700e001c40c2da40300b60131298001c0f400d000300108001000502400407070384010281c585588001d060b0b001c50b0314480d4202d501c40c681d00ca1000010704240d100182c2040381c8840403d88004203008516200015108030180309044014507207850400d00740400980001d1806514191030804024401d004a5803580400c01140c8081d841008240051070010400079040e40c1e16038038203090160003c80070011420200310340f9139001040340d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 516669262 1250 516668012 516668017
    0x6090318230607050703030810121104090507081903030b100504030201050d060306110a03051602120c070305010606092c0a05150a0803040f050d02031002071b14010f05 74
    0x251180024560441404040c400e003641d0150000c2d0048801c00000f40402c0c03083c00702402660098582020038103004003141c610042e6548020041001c8620002c00102c0381d00c6c03400d21101c0308850110740d9074082d0600d1410400305174000f0707040b80304000d65003101d026500c10340802d1b680203490030800b8201d04130901546078a42c04c140c000242080106000660044001d4849508080000075803191255a00012034500c1c41c11134100b0400801d045001c0d942c58000c242e171001741d61408411118a00c40041e5a07a4204d40000c1c2a2610104144d43c00c04010403890005540200c02442a242d6605020b400d030b0764035000d800a000200b2041002c11041c60500400c2d0008030144411503a8074030b000d4100a000c0500019950940c0c00e01007001a954001c0c16800f40203428041d660719460015001e94290b000d41c004ae02a40d80304680002581d40862240c24981c00c41901690701da1892901c0c81e1554441000540300d2510148003040001f181200051020740c20380760701c0c0c0c2040d00240140da850 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 516670512 1250 516669262 516669269
    0x7090609020403023613110d020a170a0507090605030f031201030807081218010501120809060a090e0403030207110a140d0203011803050c0c010c050d0509010e060706090318 76
    0x20300e490f0f00916940300b0141c403513544100200681704d07002c0250100310b41c5415611012820440c4260710280700c503440d200700c40d100b0110792210380040141e01141c2c0014840c450070015601400c800013028005020780101140e108041d50313405070325141c0f0b0800409150142a0003403041040c0b41038541e10000440301951150519088140c0c615a41c80307000b580051011101c48400340700c94202032081920440c0192010400d88882903449203c040c2100d005074170000710072403560035404c04542e048003200c030a40c5003034406d240d540141310300c1602c802034154480030038203140204000515900d80c1c050f00c10140b0400c3c00414094107001000710303c41040c011440d601590f4072801ea100d180008160800c4e51010b0b0000c140a00b030b00f001000c03500d941010030780202c4d40c000f400000c600014400c0c84142e01090800e4801c4a03400c2c0c50361950750008041c43d00c00d00200003812006680581e035100c03809a8002c00c01581d840c030710316100002c0c2480f90783c200c000c94a00a21b5a161541c4c404050003603 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 516671762 1250 516670512 516670519
    0x30e1c0903331a0907081e13020f04062601060b130b1b07260111030c071b03140114060f010c03050f120105090f090601061409040c020709060902040302 67
    0x2110468101c0d00090070f01c0310056040d54050a80000541c84039058244204559140d00b00c007807810250412076100a900c64105400c012410440240340381324084080701d8041e00d030f00204006844c081002080c0c035030000d100c0c25828890501c0d044040c020403040341c0c0c1c0500002e000880d038400311091316010700f19000c050544000000e003d50101e19020301400c440c0b410030300b008045000b1240e41400041d405c03065448143c1080340c1003286c1c90144694204c00c0040c001c211509071104440c85600029100e841d56020010300c120522804020300b85501c108000400d20712a62858850f00f440c245400c14841035081c04542000060b1124900d803041c98050800a0b0035000d80004440c000a8814200c091110138480240c2c0441c40b0400fa040700c601d054510380c0654182800c00120040003882403007125541c2c0e0410820b0340303000c180c050450301607050103042c0d030180e40e400a615004d00d00c00c4941140c43c00030400005980010440c04540620300104a001e446144031307010303481a80800307500b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 516673012 1250 516671762 516671843
    0x162705040c1d0912070503070c0e0108160e01030201080622090b011d0106080c0412050a0b0f0c0403080706021611090106090503150703020c071d07030b090403030e1c0903 75
    0x13103020040000340400c038132420590f480c082a0b0390b990301c00440990031101d841030040005110000003000982001c21107100604101880d0501614aa6605005c000e04011201021620a48845140d0040c0c2545904501e1003024210a20300050080c0e0600341d540f0400700c40001000e5205084210310485c410408201da81e080080513600c04001400e0b000311000c0821000945000c1c03540380741035882c4a07034007801c0145200d007485000c0440c0600f492520702141030070300105030306072401c844c12070741d0181440b5103541c2d00d0b0030640001c6c010310f0b01070400c0c00e602d0f0003118100a60b2035100b1078082c000715881420350762160011115203101d802a507425922241d00320401c80d180004096001d04e06280151410004c080f041d070070246254000105070207030590f0030406d901c40d840d890368801d080d840d080055000d52800600c040901400140c2455a00e0914000b400824001491140c15544019001e030301e159000600f106070902c01581c8000e001025090004c80c82220000d803c5101140c02e40f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 516674262 1250 516673012 516673033
    0x6040507020a060e0f0d0203030f010b0c03040611011b26090d050717040807060f030216030f200c0901050405040503070201140c0a0b18162705040c1d09 67
    0x30b000b002640103e041c45c1c4980841d01d05252420403e82441030425030145480e070030700e00450400800d060304407411440c0180584e072586c2d4000010760303003118102e15164460703580310340500f0300402c91000c82071180013003a85407070b924541200345e910035548083c42d0304032100c171001d600f80c1800708203489001c0190040041d085146119401407d013144c01a0ac4000d00d081d003c240102a40e8080c0d8081682904102d03410000a90001c500e01d44031030150a05600c0c144078200c0651001954a2005061101c1440c00d0b0007010310030030004c65012181084031184c81e42c00d800c0244e41f105035030031651107910b1801c004515420140038190145900c10000d50400944d540196007110070070034071120302e90042c0150300310554100113840d02140504403100ca02d06004414000f138280c0800b044d1015401745013440f20420003c00d0600172a0740304812007103585200030380078501d044c0d280701403441c40f414107081c003003400542544241240d211b146508240b103000803816240007012103c07404e841c0c11440c0b150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 516675512 1250 516674262 516674273
    0x23010e030f030d09060608010203090a0c060903030e090405150a06090e0c0a1512050c0a0914280305010e030315010822080708161b030b1501030207050708010b040506040507020a 78
    0x640040340b064001042180c2c0381d50001c1d007260411204be6000b0b9122078444400d21928042980280125142c003084841c1151005050006000f10b810f006411600004040c0141400b4200700900e035a071030307800e0710b060602d401c0c00034144e51f00031000054a0b00c1340e9a040034100180c544010034016001a43d101d140544810620050310303081003e1002c64500e500180c80c40b807260701d11500280060b152a0401804010302c0007407182c0110007450012041c050013540e90302c2c6529220340d196142e001c1c1c8000030445c803580c0088140d000a2a40d800c2c2103416420761004009148159011103030215200e047c8001115064026521120582c8a425100944403030701240d0300211070084c04d1132850203000740d0319204c4035401072081c100e0040100c146201001281941444c0400c0401c1c0f040381401d00315280c80c1c0c00e200b07000e012900f807400700c104481910b074025019034603403036000003d807080c1c1b80c2d40b43c204601801d000b0915520880c90000007a00c581b62510695000f110035031700401d1400481e6a54 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 516676762 1250 516675512 516675521
    0x3060f0417042102041b0809010507090602060f250522030c030609060902060c0c1f1d0a260c010504120305070c030816020f0a06020a1b23010e030f030d 67
    0xe917046601e40200c12044e1003049060301000c001c43d40c0e005042d01c0d104030000c0c00c490300904914200504103a0070081a9070005072103400054070705001410b03480341009804801040501e42004c4450b200c1c00708441c5070400c01074428822107800d2102c44001d90048001c0c5501a800002c090084541c400d0000c41d55130b601451501c0d00c1040006000d00998000881c16009020041d195520246101420b410102c0c0002c60400303101b0446a841c40c40c007c00544003500c0c48103484a0b01201130502c1c48540c1d21940c1c1c5000030040d0800180000c5803007201e806540480d403c8404040c0303d542e4040c803c80d40324a00300c0e4205d501d01c0c480b0401940780356504660580c80f56005542c14030309840084042020000101080c40c400d03a4020038688a83c4140194040c281280c54414064550200401a00032840c2c1b48030035882056800c2e45540c03919000180030040d000801c074140745895a03814060a88502d0300c3c0700c03c0c02d0b01c4402c0c94405410400d40c1c2e650b00302c2801e680c0c1d40c10074010030800b000c15400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 516678012 1250 516676762 516676829
    0x503070e0403120605090c04290d090303020405040e0120031015030b10081e1501030e03070507060207031104021c0b0301021c0c030b150f1803060f041704 68
    0xc3c0032074100d03603031400121b0880b41515903401c0140001020000160030850405149502451304800080480f81100d5a4052a840901c1c426212a4000e0815100c1d40c1224098500100308216144118003954000c0c009158068516000504100047e401f5802503038800c8001411840c2c50038140003800740c10410500801c018503486030b041000d51b0b0741b87c4030701c4040136903199030b0030849107420f0700007840c8841c04048005013840f1035401c3c000340350080e800f91041c000d400c0c01c0108122b03290700303480b510f140b082500207045070244600100e551540402c02c2d0381100d004505007080e036010b5070300708400c9226100e21030320a5980c0f0800c4451585494100c07202c403440040c0010304050034014041d09413110f51030b50200e680d988201c00c0b80596014400c012001c0d8064807591802c1484180881152251244102c1000f2000c14480c1c0784d0392080b00a00d2040c180503040d42c445041101408040190542e02200c1492800d032407001e401c41074005403811140e17039028a4041620142c1e070b8103001c0c0003504 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 516679262 1250 516678012 516678047
    0x606021b06130e160f030c021009020a0f1202041109060a0c14030c0606090c04150c0606030c0312112a1801080d0e030d050f0c0120070201020105010503070e0403 71
    0xa400143d6071440d40c1e0031446202d0050203101000510b070401031428501d54020400d05191142c003200341940010a44402605054006403060950000681c828103590140c9202d140d41c400204119001080c00c04625209403401d10980c2c01581d610178950042c0000d241d00000240100342c00c4601c6000034400701070003803180b038103c404540429810769005000c0140a0b0b80940184202401c0c44013070f0940c032400025009090500b8010f40f146080a0000d8074400c01030107035079280074401c155100c107001391307400038440e0400e03036891812a00308a14141e801010614844400c602010040303103508030707480e405401e114000f0010a0175901220500402c54000704010300c0d034500703c10045c0119000e445030800074041c019121000078005514407500074000e4101c0680350300150f0304201a80c060480b02025103445018400380103005110180e004401c580c5c440c8400d07100001d250004207821381c000e038028402c50f078840c003e05a94500038840e038403841e00da11000401003880f42400085126118 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 516680512 1250 516679262 516679297
    0x1050306060901360f03030527040c1224050d143a0f1119060f1d0d050705150103050d120c0f0e0a090213090606021b06 53
    0x3d0074440040801c2c03104091300501c0d01420300402112244e0100c009010101048010a0550740c00401f60b0003003201e2010302032941c148003015034440f01c00d55146100b000e0010004150407030700040004116218a49414ac078180101c4621202001d04407001030003250440681450403090001d1098001d030295401180c0d81d000104954040c06108011885420304015110b2450031282624104400840485590004840c000c0740c110034074880b60981410701059000b0070120007810302c4032880b8200a0790395000c01000c108180b80e0300050107900018800c10200c0407500c8104100e0140103000d05ca958488400d00ca155403050000f000c4035032003413090320904040303440e13800010790082e00101d8590b0080b041000c03000e58071030854840711b44030080c10702c51140c0c020f5028010401f01d0345181c007081038115543c070103034440c201c03900d000b418200300843d69685103da030400d1441040c0030318200035052610008100f840003803581040001e8803643c007980c00d081b5080000541c082605900f441809 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 516681762 1250 516680512 516680537
    0x90c01050a0e0a0806160543150b03070302011e0512010e011e0302092a2709010b0d15050a060e12060907121703130309050d0201050306060901 63
    0x401201e48002c20800000b42410305201b0240c4a000c059403803480c2c00c200080c00011141650001030701c045a03005100818503464203030a103041405c2c54042c02045445100c40d100400a42c1007540c555580504020048414010205500c0f0452884082d00003881032812504031045442c0c2c0680c0710341c180c00d040d464049000203010b61080c090380b0400395000b00200400c040c140f00e860000e18400303c01ca8081a80741960300048545074054290b0030354540500608002c00c8581041948040c50162200c4d12080c030100400c041c070384c002000b40e4507991001d0f221102420900c1c0454140ca00608802d4100071102c062000240003e503180722060244110020301a00d0320741814010f06440d5640189071f0300340a06118050212650344a03441e4000400c001c800500425a08244c030781c003001c44420442c11342082400403207220030035400343d40700205200014244442d00c02040b48281c58403803031507584408200080303c03a8480a80410010000220107140440040070f0940050400070190343c2c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 516683012 1250 516681762 516681769
    0x315090606050d060b040308042706080706020708120a05030405010603060f0218090606160201050d060e2e050d1b0e0618041109100b0d090c0905090c01050a0e 70
    0x4035600101c00b0a400207412403881c1050702825000d01049140c8030300c0e0500d55501c0040c43c2c801d82c41035a811015078010220403c070310802400880d0740d00305003030242c5a02c03114001e86694451066001500c29030b000040e00d00300c0400c0350598824041481c6003040c07010b1405031000c0c0c0c03000703000b08c4255583d000c002c80006c5003440365261325410381c0d41c0141c4901502d801031a00f5600307030301d00910652448041100590762401203480c0c0300e1409030900e005518510042e103150044000c009907103810510041080f4038603103c2680709808850000781d04a000400c00c0340e00342d51405481c180040c0d265410710190411407001b880441c8070b5032031001c0003006803280c0b003c540308540048650168040034404149001c0c1218101c5044200d0451030310300b06561020f4404034180440c0d1b000d000080c00041e4401240d50507600100b60450030b0a6031031800044030001000305203070448100000c20400b041e41d070b10901c02c0c944103242020041c249403664030010f40d082d030131140c0c410080000c8551003440544 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 516684262 1250 516683012 516683021
    0xf1a09040509100e33220c030c1412070902180a0e1e0907030f0201121a043b0c100f021b06030604050c090301020708070614040c03140a0f0b07032a031509 68
    0x5018444409c00c4038102107100701503810a5805520840303940504410845002c40d041742200c4a084006944052283e80d0240040650040c1607000d0320b102000512456540d09042c0b0a5070f0020081007107103200d081c940301c243c100380e64513400c0d584a00010700000d4001c0c0c100e20011801410700e5030014140301d00c46410f80b0a00c482c0c103030492142c5542503c0034185402000d8228420708140c0c00500341c486503c222016550343c80c4c0e554154525040301a00c0024862490f280c50040e04010030305010070030140a01c010301c00d130f00d8018850310849904090142c4410701c1c0c010780040c906032035511a8402c0201902000d00001204a070401c514941d540c1d00b480107003c0d035486600c00544070012401c140049594105013181c040110350100000103161229007415650b00442c0400c4c99041d40500f00d02e040070300200144403846a4483d2414031455681440c410030075a81c0c02e10503115040c100c1c0c0c1c4498602c80090080043d9140e128603a14002d400c620020505101c0d640c5009941d0035034801a0b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 516685512 1250 516684262 516684269
    0x31302010c0804081c020708032a03130e060603010302010507200316030c0f0803041802070209010609082a100314040b010f1a09040509100e33220c 65
    0xa0b80041d0169504035130b21171075a100140980081c00603c0d181a070101c0d100d00c40e0800358402c0240401c1d078900111181001e1008622281045a88650354042124035048e241e0003101c07281000c0e0300000f8180d02d01501120f040c2d03a81039649500700002d60380c90351070710400768004035002c0301c13800140c81c02074174100000511620007a400e20a000d145007004403424546801c031014580442401b4440203900001301c0301120001c0b80d0103800081c40d0000c40d0000e000d17403103009500010407000040c0b1755a20840070000c2d11085030a4668040a2903032070102101c40b140701441e482055105440d1a142503090510254250f05008c08c00c50080307001c00e03401c0b06007100d04035041c0a8040051100c1c040c00e014a80c0507100c010340012038a0700d403290240c060700440300424800c3e0707100c00c00165094414445022003024a04051080c600b290f420300c0e44682c2010103820b021040b41100403804002034a00d10804c00a24109880d213032185082ea4100c030301030603485003801c001c060508000030a0414081e009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 516686762 1250 516685512 516685529
    0x3200102161208160515070e010206060306071407200a050d020f040e0111220501020718020f0c0a0c0e0606070f081803250e060108160201060f03030c020406120503031302010c0804 79
    0x7285007c140c0a4407513000000c0017811544000c1c20003038591000207040d6080000b5040420110021454000c86880f40c07801c000d00b0030880341c41d121180308500440744c0704035000700d4a41a07056120700c00c3c808542540b540207507004a41c9101a100390074980c2c0805600440710b8000315850354400d5401c1080d9000c0e400280750b4204e511032000d0340813446400c02001d40002d1000e814130f50300c3d0944c41d0801000c2c490341e000189600213240494410b05100b00d800a00000041d40c80c0ea1485e400e00c40c900c040544038134424014040001441880c01e40112022564000c60a00481c0500c2d298024560440008014480c000f42101c417030f01e0ba0100429118100d248049213400c007242840130f55641000c1c3d0011602c1d0103a4000e020843e80c1280d0368581c044240f1307814950481800e481240034251030350101c10f91004802000c014507501c520f9134402e19000f580d01f4810140d8540c000f225410320408041d02c5a00140f0104008120040e000004070317005141042d00c01d01d2541341d0030b005900a81c800c00c407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 516688012 1250 516686762 516686803
    0x405060f04110a0617010914070305061c0b091c020a030302090604080a080301080c01030209060d050402191205060c1617071506060e18060415032001021612081605 72
    0x4117007500c8031014050b107031891060180b10741c6c0a134000010304003d041001810303160b100140c20354485422001040f01e40d21a40c2d03050410909046040180944200e0803c0c0100381c1d4415009040300c1c01c00d0450300d100c1d4000c066015064408074003c0d003189200c241c2c040010000042e40e10020002600594099081d69587e075241c06446490b0605070702c40a4141801071181c4003031039a41c2400d03074a03076581c200004901030755140700069a1108004080360b00c40c0b503480c0040b42041e0640a03001c9514414821104203440c0e51105100c1c50207003800c0c2408075411107001c0e0000540c4400c4581e400d46100030b0140c2170900c665a0500d099070b482e000019150b0761000c0c00c024007a8064810f5003008420784100c9140315000540159030000200954000c40d12005901144040c6026100045402c5086442044480e000c3d0320b030340100681c0740030700600c07030078180080e0100c02006c810210b8900d6080c0d0034105459075282e182e0346e0083d00c0c00501e010085440000854401c0c80650f5110421418618 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 516689262 1250 516688012 516688037
    0x30e060f250206060402160203060c0a1b021c0503040b04032f0d0803060a03050a05070303030c2d0302072307060309020618210c0f01080405060f04110a06 68
    0x41c110744608140220044103491808915401007035040d049001690056681d2004207034034000d1148405000b0340621546d0200043c01e5090000f408441825a8070700394240c0000890302d00b00c28844c00003a40c007041041c0c80d0040c2c48801010304404a1146058900785984c41c003c103501508642d10544c1c20784440c1010440f1065009496116001001d0f00b0284414090001c609248080c42004007401c00000c0482c4260382c444825200a641c00000c541c0d181c11146006511081c4034071045002c03a0502c54540280341c09a4003030440c0c0140c0c1e009950a02f660040381c030030305206800c01a01415800c20010021a2800d88070307800016078000312500000101d11690b15106540d40900101403a1000031401a40ca0804032800714040400916050100c100040c52100c5032412900c1c1e2140f80c0417018032090030209030900041e03c200d0b00003001c96020300c015203100c0c8003103c008040d03800540026034110035164426070054058110824030b108c0b407030080f0300300d07444540001010550f821600e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 516690512 1250 516689262 516689281
    0x90c090203090f0a1b0911071101020309040c05091201270c03020a061d030715030f02040f08160504090b040212070b0c030903010f0e0c150705161701060f060f030e060f 74
    0x1c004064006e820000342c50720050f01880ea0088880040c1543e2407542040081e038801c0099170954000184200520307840ba074000b410790b50010302c5940c000c41c052220340d82603903010f100307111045401c000d60f03405028200e4400804440e1451044491802080010001d6291284a40090840e07921084480c40d1800715181d4001034510b1440d00ca80c2c400c840a0040b204c42d81c0345402460750504010900c1001005e0301c4007e40201c1c0c02c03080c444841c100e000180858001a403070f0442c000642c428041c82c2e160402e11040d91000e44000d0302100318071002c1401801c115450060301c00916040e295559200e0900007520392081001000c590f01c0442d00003120300e003c0c070850f03809082c1e41004003c01e9440c540e401e51640d907182040d81c454110403140600201e8840f0445109652083c00d8462055400704881c1b4400450b00035840003d50038a024041d1030030501c125010741d10f42d030480300d500f986050011a520940407460f1010991039120000000c1010403415004030202d0003050344526003045003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 516691762 1250 516690512 516690563
    0x515130f15050a2711040c020706090803030c0717090315100e0417090312070c090f0e1c050d0f090b0709030b0f040f0516050a0801090c090203090f0a 66
    0x1641c580c80c6800451620105884d00e030528454000b015807035981014200030502c070300a05d0005821070b041148880c5140d901060130030a607103035910f4481000f9251614030f80e60780001c407241141c1503810016103002c120545601036116010520140c903105694001c03900740007190707050046900d192810311044054405120002d040910f03000b030310b07611309900d0b00d130015403030101c013480c0040f80003c0a90030798070248046040d040c9070030106a511250792030f2041481c3c01c14421007203824648500359020710102e0150300704000034100104200c140491041804021400324241132020030000c4201c941e8103802241900c01c0e12110004480c5070328140b00c0c0c00c901c0c005040344100a022001400040d0250344035a030800549001d00c0c03002e030b64034034082030305c00003030391000d8071610403040080104203100001b4000c0da0703001e44001c80080e030703203800351800da0305190001403031042c070304000b804610000ea000e1070307110494404440000c51060805070525684050507280794400400e40900c07880305141 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 516693012 1250 516691762 516691771
    0x7030306150c08070b0411061204030306090606120506210102031e060108011a12040b060102010f020a14070804050a0b040639050f06011503180515130f1505 69
    0x14800030b014010b03524001c0901c0f8492005014080201c08036080c0140742200400581000c0d02d0590341e801e00d480d41d16554a01144c04600007420600d0100b070180507402410704031181910303035081410701230484401418004000c0c50b0054940e0340d198003808117128094124030380780d100040c0e0324281040340c0c607040c202440042c045001071205003e1907991101c07207181154036003881c05003e0101c0710b0f400a01c61060626240000402e4824401489203044095002c0c21090b0001c0210001c0c89003005e069008080b9000082074201c040842500381c00402031850714483c105040c0b0305911980080c0c480340b00c1d038103c6820142c0205042c018141c101e405401800ea41d5801c6010b01718008a4100c503200c1c0503d020320441140385450020070104103e07203951800858140c03140c0d90b8440411490066040d080500000d0601190091100f200000040484c0c0c006002c0c11810145110b12240808054800d114000031034030185c6c0840d01503041c0031142449401e00e1984001045490400c3d40d202170b1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 516694262 1250 516693012 516693017
    0x23040603092006030103150603050a03030b010f211104050a08030720060304020f2e02070519050f0117070e1305090705040b0a030b01080f010c090e0403030b0d02060703030615 77
    0x540c2c04449076180c0d0141c0c2d0450f80e014014848a1584c00d01c454041c03c25a44018054840d090400c3c0825405400424400c0e00a0340c4048411464090803a00b0001e06211202c408542d2404484484495001220100000d14400c1e00c0d081d03031032002c11514401365200342c1c40c40d003011502c0010054244007405c0d1640b0741c0c0014224044441d40010030500c0f020300000d2188500801c9985030341c80b0f0644601007185080c14080e8600841c03041014140242e031380c10340050280e0200450646480d202c42e541418010300511380c03640c02c0c00d0a00000024845016050082a40d000e9001030b607440c054070300c60b074480d0f0f9034650003410b1601400041c64050b00c403000594104003c0020204001a03907008549040310082114002900810300302000c0c0c2d00003400d030503200700000c10844c0000440e809a002548020420b1001465003100c11481030b005504c4401041004200401d210350805028024020091101009107a0002c0d00c42d42c400c890842c08a0303240c40c01080708143d00f40031032840100c80d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 516695512 1250 516694262 516694313
    0x121e0c0e060711090402010e04050a060504060611030414060c0f010c020106240e01030b0307091406010507020108150307090c0804020a090c090308030408042c0105030a030804032304060309 83
    0x40c0d85030001c95004601c43e501816a80e8005010741e031003945110125400948200041d041201d2428042e101c10700409000710b007070000000c4c280b0701c2003c44081140c5560040c6081c60304141805510740c1040414662100d000c0c40391448000080c0460b10704007640000000c3c800b0040341d0041c0c00d44003e940400c13110110801c007003510176499406c03a11811128601007801d54440c0c40103070000c022640c0d1a0750140b266040c04180c000c040e601803203031004d580070000e200796281e8004460743d109041c002400a0000c80115064103c00c0114641100700142038881c2c03191212180001c440c0d4400303007040010190024402075007004688000138140d203000500c10341080c104042d104a110f480000e00109000002070140400f501c103580c0075100c06032007040940407101c0d20078051094990240300040c1c040f40001014a0000b070344a21071541a11251190745c0c0305d48060320600604004120050803018642ea90cc400100082c0080d05e01c035180000e403949682015204c1d0800740d45201c005001c83c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 516696762 1250 516695512 516695527
    0xd11360609070503090f01020a0f090f08120c1002190f03050702071401110a2f090601050c031207110f07081908120c0301050f0306060907121e0c0e06 66
    0x408490a6010302c46080c55580c80e100c640d41a03191600b00210300c000c952022803e50038a550081134149010416500e481185840b400c0c45c2c04c0c0e032107192003800c550742d0182001c2580b82d12280c0283c4001d040301420b6a4001c0d440162080699010031a0882c1c96210300c5041d5400a80000b6007a900c000301c0d2038100300500d40340002075500c2d4241e02030600b82c1c0e61a0070703407407802ea0302c10b4a0781a4002d40360415914544030910346222101e503100741c0c00080e4900c0c421903844002440030b80c5640c5a800402d81d48043e2503103401980d01c1c0c0d1004004e5000c6000802c60030845004410f0700c280692629030798071060108004805090941c80310141030140c01c0394008000000c000542c40c3c400518468903c6041c01951910b40081e01c1501e07521001d00000c6c104015401e10000d000c0c504a80c0c068585d2100414100c0400d0780740d4004841f403d501500c05030103d50780c1e0380f0941e043e0440c520012400115040e60301265421a8106141000360039191545007070b84580c04223040e40c0350030781a69000c1c1080340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 516698012 1250 516696762 516696769
    0x30906020c09040308090c06040b0309062203030b1f02060901050a090b06060f04030537151509022a0705030d080a06152705010903020d113606 63
    0xb02502c06010017000c1000f1a070a48024800c8290015008090716070b903c0e03595156480b036070030407240640d080c022000040c000c40c8030441d80081e000c450300d004001c6044075540540040146003115034102c10920b02c42200d01904034103591101401c0e070020091894040100d84c02d45000905000c03469041040c04000150079107132043e0001c0040305c150303403201070b410320f4550b580c0034540c0050802d02c61224000145084030241c401041e840c11404071080310360140c2d01182455070000208080c0c4803a600d5451245103501c0030b00002a0038904002c0140c5d21903855082e03810404411448140f80d0300200d514120201542400c15603040181c1001880c200005e5180ca0340282944140154000003034003c256a42c0107102403c1c48001d040302024030110001c200c407052411401c200e0090660340380c1127004102c2202d007242e40580d0381d20708541c1903a007840041d01804a0460b00c0c21f140e1248035800d0340e5040558890b04014624a0701d1040180f0501e42720924540c5c8402c00718001300007403140545 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 516699262 1250 516698012 516698029
    0x2071203022502041103312111010507031a0906060702011202131401080a050c160606050303040330020c010309030219200105030603030a230f0403030906020c 70
    0xc0e202c0e80e00c110a6000780085800b8141301d10801d0648840042000514400185000d0201d400041c200101c6151010f907280d00c1d54481c0390240c03040110503580308000c1500da00507510580d80d481c10692000c40056440d082d50020b0b00d01802081d1994111103240752040501035040700e04403898441810088081076107849104406410451800040b1890440640441700c0d2107101007842c4103c80c1d030740d1303e03628205150480f40900150f100c00c0819844400b60141502405403404800e1418014070164400c480700b038001100c5241d00c80800080300e5500780041e0000b1800ba00c40203116085405810780783ca50302441680c140784401130300000680d40020070384c100920038203000030b4110395820160303c0c0031701c003502a900c60b0600e59152410482801d451410320411451104016800c03040152020f00044400c0b5030558401e006000040b03200d04600c1d5001c01d40160036180710881104407402e9580b049100c081c90a4001904000309035220400c1001018a44041d08885080c6d00000c0d1410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 516700512 1250 516699262 516699307
    0x110a0503072303040b0703151707090e03031e0103050718090210030b0901060207030803040b100812130e041110050d02070b010305011a0117070516060207120302 71
    0x21001900a0b405480284001c1d00844524091050388070021a660340c0308903811620840300b2000302e20344c01e01a00940b03002140550000100505003c0c204c4800c448008843e074080c8169407000071101114410741c885100110043c603601d14240c03c0000e49a80c0307403540e070020082c0102c01080410000b1511170240c4a07602c8001d0b00c020201d290b010301034691810082c0d4061350101100c41c070203030594009100110280e0700c001103a03980b607000b41d8840100c1e01c00a00309020800025000910b102c0a0365408054041107050654803604d0061400303821903a0303503100d1040020b03c1901600c0781d4a6000080c080e8014010191030301d513130781c4618165a04030050164000f100160240c40c066810354400d00580c180840d243c01450804d80d031180c01c288000d81d00e07035203880c0c03040400d8200c0052005413140103864100d00000c90401044807070100410880410001380003c117140d0400040d0141103a00604004d619800e450504160003409031002100b4544100070501c4040f001c4403504011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 516701762 1250 516700512 516700517
    0x103080a0e0310050109020a03050603191e06140f010b1303030516120e120307030522080607030608010c0e1e0d020d080a0908010c0903060b12060703060501020c04110a 74
    0x41600c1c0d10100f03150080804800c00843d007040d002140d601c0c25503002e000082d4180c1e0b028001915880141071f150f450040e000c06100c0f4410002001180710681203c0042000980d00181800b01e81c4408003160420b6100944014002c4207101001c10f05050f03940c00740801141e0b007032a2107c0c44142c5088a4102c1c40020103104000c54031041c8070745521103804c000754104281c000c241aa24074001c008002e0104411310400c240700d44481070542c0003080c2d031403072a0b2507100c01d80740205101013070701d080b030f0210950038244840d1000810018020311005000d0701c026280481c0442c10035008509403450900b104041102101c1c01d5401907840c2030001640c0c6808050ba0b80c0144200800320340c1d840440040650070680e070075001405c20100b50018142840c0581e80c580501c1d07190700358203003a6aa40301030a00000c6107401c040c03002c0b42403035001e5000180c0c010041e00d03225202d000ca44d810403000b1140c4c40c0c0820355450b01003159503014130070700c12113001c12281040704403c0e20340c903107c4030b02500c0e030389504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 516703012 1250 516701762 516701777
    0x10f0804050f070e07030c050306061602033406020f1522050a050706050f04052b031d012303150a030609060c0813170d0612050705090103080a 63
    0x920805100203101500b8400a81e02500c2e211000301c83c440300143c46a100191030003a10088080c8070341c0035a130254a005054074034000b4a800e03403245a40c00390006a0b4503000720030300b88171600b90140045070b0408012400d024281c0c44400301d01d020f414103034800c1c0155085180340190381c0e0303004100c203000305080d600d240083d91136180294111040b01c060090b0001000088036060050000d0707803107002d41c40740040300c001c03940b81d80c0121a80d010340c01035004541c80074041030249140c00a090741544690711940384c00402a0780748841840d9101000390301282c8000810f101d1001c5680c01400d8038507080c2881c1c41e0030440078040318800844035610782203061000c4003189040341c91740f8840541e820000d05030300030b140e201c0c1082d00042001e4103085070380030f28101410505034001c0760800c3c410044030740c0007000107160741c9a01c100407041321039031031190364204440c0354640d45511401c0040e15000090150314040e528181e490302c0180c0d00174502ca44e0400c0b004000060188003241c612484500d080003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 516704262 1250 516703012 516703021
    0x3020406150c2a030506011701060e041101020c10050706050a18060515030a03020d03180c03020f0a0f080c01110a110d0f0203071403012919030f080324010f08 70
    0x412403003000010143c0701200020000c184600003a541c3d040e00d208402ca400e10900780e02105080b83c400d0f00c0740d182c0500700c08000038040f5650740301880300c0850600503100314414040c00107565550400410011500228818080c040079128036a4400f200300001c0120080d6105010b10141480400418007030f03c480024104801c8074800598400000d4116014030b4120302d00a034540a110380c074a000070b40b03410b03980200420110b00304035500d90806402801c0504603024080b21a51704803591fa0404801440003c0c90010520000004c00364800030345014000d810006119580d8440b690410364004601e0344086078085440036844070007214010500d03c02880c00440004012a001c1d5040c0204240010700c0c1c440da003a40020544214000c000c49200e0b00700c0c0804030300400010a4460006039841800c9040c40c90310885118a400054603145940b0741c0c3d40000110300c1e040031200c4100c04000d014801000303000c0d20007610840741811015004400c00200321155040f0458108045100400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 516705512 1250 516704262 516704303
    0x50f03010908040303051c05010b040608180d1101181a04390e0709030308130c0b1801110d0309020d020409111005040608131e0b0103020406150c 64
    0x1600c00d40d0044015803030f15503c0c2005001600320210700e03108521040302c102d0804245100f2603040c0c0780c01141d5941071504080d022686000b00801c00032090740c50460144071020304008014011400c0d6951441c0c0c00407210b80785003940c0308000500e84000d10300440000040c001060300480c20001c2c481c280032aa12414407840e1100aa1032200e07a0074110b00881110300148500c45210031070744400311000d0780c0d981340f40e500e90782411039000740001c8980409000113403266840d030741c00c40460b0b85969910300c07080c0c542c2c2d0b8003102c1e26402907882c0c40b400110303c1d8020034462071404441c1002d00b425101065030b003603101c0d00c40d4810b400300c0b0b0070113985d00b95150465640c580704d14542c0b5009071003006240c10700c0c81d21000f00c000c80c0420a1103680503129691403184a082128140d8400d583d506601e5200c0c03150307440da081e12940e02290f0f0501c070f905841e031550a001c941b035062035008410070300f1194998014401191050b82000c0000c03461590b82038030441d040300414182c01da0040d0b1500d00344903a403459 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 516706762 1250 516705512 516705521
    0x304051318021009080714030309130b0a09141302030d0f02100608010f06090e0330190b010302040302181b03070306050f030d0c031b080a0801031203050f01050f0301 73
    0x20351028807101ca503410b041c2c1c030480184c20303202c81d10100e81c000354694080342d001c0d000030708880703a255204000d411039030b00341066805110119072601150f0300c44c007500003448210060300012101e594a0340200084095051115042000550740002c80352894001c00c2e20382580700c5030a0b080c04003c850411409100300114260b0b03403074203101005900e495142c510b02034004828049075107400d084010032400201c0c850413803018031840c0154648050192401d20b141e051040c0b8003030800c0d03c803048940d04011080d0540c17203080d884040c0d010f0032404034000d5040321301920900d410540306010520041e21481715641460240d01554145a580c10100d07071008242801c1c403048881003c0140100950160419030035241300b12003584621116174207141c3c0d10f004c40c00307881c40015003040394000801e02078142c50134182481b0905c58600c0b00c02c0c0d140da00c00b5510991030240003600d4440108180114600169000c5280345000d2000c0d003401605004003d00c18000d03248030311000030a03031074a0742d006d501 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 516708012 1250 516706762 516706811
    0x60e06061806041211010311041401020a0b0702010b03070f0b030705220807090b060f0a05071407030c050108090109170a02010b04060306050a0e0d12090204021b10060803040513 78
    0x3000e0f0303480f80c0b14000c0021301c030070f2050221000ea908148204d490b601030301a00005810101c00b541c1050300e0962004d400c3c500c1040c910f81503000b1240000c000c1644407403a141315602c10b0300041402041d030701c18140703080b107550701820000d0400941401034400c140107ca800c24000e2400b1910b030041b1800002c503e0000784c401c03c0e4030b40c03940c5000160709540403845600300c8517410390800185080d0014080b281c49103510000b81c010381041001201e42c0200080c004003801014150900300844a580e8500b040a400640b1140501901003145603408004190700032400c9000b40401e100690720740140c20b5171009502c2040002084008116200758400c42d45088000e209020342030f078a003405801040d082d908151310324101072040c80f2102d40080e040f4142d00c11541c800c0500d500010f1414001c3c45000000c13030307000b038080200c0d9030b120130000e20361305080c15420003904a40c80090052001c81c0c00c541d200111a4205010400c05951b07094140d81d1101c040031004a40c0c01c03003811703805080c0350480c0e5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 516709262 1250 516708012 516708019
    0xc0b0a06080604030801080d05070c0504180222061202030d0e0118090209030106061106012123060f130206030613060f08070605040b3106020c040f060e060618 70
    0x108000d061780800340c50f0484034030100ba940342c072a00c3e000031100ca02c1280300140140b80d00c0300e020401c601b8550b220000305a0411100e00c80e00c4c40c180d00084100c40041501005c54034450034040c08070362144680340040a1050b040b5010000542c0400e86880e51159480c041c420f0800c2d4a000c1c2da40641c858005401011485241958884030b05100940112800d80d009610300000810704500076071492050700c0202c0e006269a0307281c83e0b40d1404075689104200d0284110389a00b00024000403030205001d61303040401001c00d402d0030000303480c1100c010f0003245405400d2080c040100580c0c2c1020a510790103403040d82c0c0d20741d10400801c40000c00f00d40e020200e1f0340b504100042610070003071204252800c00003900d4403907680301c1c0c080391349020f14000e19a402d8010003481498000ca4501d8150f18840d0600004512407604412229140c182e0300020140e0000c02c090398040c9424880c00204134071404042100e103043c40446000b030381000b416180100c0380003503510400840010030041d1804000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 516710512 1250 516709262 516709273
    0x50f0d060f090302070b030402242104020103140412140702060c0a150515040c0c060c02010501140409050c100207121a0c0c1c090503010914060f070c0b0a0608 70
    0x10704162000b82200c82003500180034a24000c2440008401240e0045030000c120965a24203400e0b68154030003a00080c0f41c0822040160100828441031030010710151025048081d00c4c0034000034081e03400d00b40008a0140703041e010040024100d0b10130071142c84039450412030940348001c40c00403e100d00c0b500a035000e040420301d844034440c0003402d80350283c41000711001c0550000c0c00c29003914000e0350300080409188083c13260a040950040b0700b9081c03a4034042215100755240c15040311000003680c070060351200014850420002902e086003803066604000d045142d4451a45407482d500301e583c86110001c000025083c4200301d0840900007000643c2c629030308231703c0c08200c0340c80756542c109480c4106000003100b0080b11011343e504110118054800010b40320300da05920b1034540c05040038004620300200b40d5417000d108000d01c40c0c2c2b2885507103550044240015180070001000c01c5480039420b010400d510340d0000440c244682c1c02400d2007419120901e0700e03c0030300740310303000780c00c0e5441207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 516711762 1250 516710512 516710531
    0xc09090f0905010b12250b070c08071d0406020901140a020601150905180601050d0e07050406050a0602100911090702060601030c030506010c0f170c160602011401050f0d06 75
    0x203a600407031066200d6002000306100140034048181200078140c081c41c0c00406010021402d8405128038001c04417800410094513241051169000304805039244020f00d02e060160b87c00c00c11101d0098003074031030080c581d41c0c030002e440081c0c00e00092000301004e801080b076100304e034004c07080144e840d05101503d80c1c81308030030100259691801d124100c00300c00d01c42407401c40365028504003020350b40041d10710b4107203101c40c3c071405400c568040c1c05035041040800400c07102c02520b1140e440b032145079070301078181e03a031030007041205449443c1c00041c49841c55210810510f0340000700403800100e08180490003070102d050200c2004103142509400c000d000007000000365011407500e11401098904002040c10500c04800b1107404031041808103411190410100380c0b081e004100e818426510780e0000c40a003083c3e00401d03002881d003078099a00c19051601841c080040350300240c030b2548000c00c81b0b080d4048044038200e8062150a014281641101c5520303140d5002041c903c503000041481119403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 516713012 1250 516711762 516711791
    0x3140f0c0703031e290f0603010e1512070f1a0a12200702090a0b0a0513060f030305040609060215060409080c0d081b34050a080d0615120c0909 63
    0x1174860301c003840c00d0544e80d100076540340c0301c107480c0502c030800351001c1d04580c2441c111903802c01001d032041107894124002d11290743d450103511b85905105801800c9000e107002c90740f0807070a003917400c01104203840b80000b039129100c3c0e8007620144402032a007400310500700e000840062500b19540daa600101500e0a1a002e00c1c4074000d102292090754000da0654503036400c1c10032a0a451b08041e07028041e441c0c10001494181d11142c550f400140000803042d595510f92010442075034811400f103040420104142500090700c074000b003566002411040354040130340030f030150008100718440d40d074505d106414080141c0c195121000003008654004d41c1d10000606250f0302201c560091140c0e40c25811040c0c0556029200030682c1e800c4030305001c1c2d10059440040b8141601d0070101e18201000701004124104070b450902070080a01a6071007204560760415a40751b5082103480000000079014910303030125a0ba2000c003000c2d5800524070003034802c12560700e20f407544501852414042e50401100307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 516714262 1250 516713012 516713051
    0x602030a140106020307032102130e09010c09031109040f05031b1b0303180402131509240c0809122a010914010201021903140f0c0703031e 61
    0x2941034814441ea0b03a0754001240d40340b240701d03c001c0025240100d80700308000000c0b40848180134600c005803c025003c6440c1aa1002c10ba010385019040c4d841803043c844c13428860400184454a4000c20441c1561505050040c2c107140c2a030017481707500006407e201040017001e5143e03602006a9649000d60788402682e00d4502090145134003c9884610508a64240c0038003800e4000c0d01070350500f841095444e5081112103481c0350030030340030010107680d0f0150980eaa8007501900e1419400c40c21490401041e0203d25007014440404078000070701c0c1d80500340240d01c21200740e480c007c6011003061030303c09410f01410709c00a4211075010400e41044001140c00c0f42c2c41412000d0754070b06284850810b101d403201e241c0200e4081840c0c46401d1140644945480f02d0420040c00050724000e46800c0500b400e01000040310006650791100c081100c8840202c20742054071a01c1203201c030700384101c41075400d00c1018401024590346151040f104a900d400191240303c0c480400c00c001e038802c1c14291000ea = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 516715512 1250 516714262 516714281
    0xd0603050610050132130303090e131e15050108030c1002040e0c0c01140f150109032001090510170708040c03060f0b040509011d0a0206160f0602030a 66
    0x1c441161000c2101c1d4410300b94000c42c201405400c075402c800f0405d803c01000b01038400e4118001c41001490003180c12401c82c0c03001148aa030351146014a040031000a0180c013804010030b00c41c6042d040c00104840b0300e0300c04c00c120340d03d4028003c0c0240a241800d00c030080c4102d17920f1610f04140000070400383c00f2014140e000c440600303980355002015008001c80c1b213507000d440356002615000c20400c1c14414041e050544c1001e00006440c07400c03e50303004800c1c034201c40c104060070030b001c20800d1f580400142000e00c02c40c2824101c1340f0506642d1002111340c40d507800443d6030a20071341c694580e81e119280040090401600c085040e10084400609a481604a0305210702c490300104001602c02c0018a10a94205200c1d007011411a43c40c10040c2241c2c0e811400ca80380c0718210301034150307260700c141c50044040070000103c00b11040601e6003194548a15000315402030740001c07001d62541c10840b680c014443d41c040c1e521940c6c905c0d18038044090071101412062000c0304104528490380d12019a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 516716762 1250 516715512 516715531
    0x4090308190b030d05130305030c0706031d06180102041205100b0315131104021804060b0406090504021318020414120d0e03030c0a030305060910030209070f050d06030506 75
    0x24440320384001c007624200c0c030440b50903a04c80b400d0458242e11076001b405120525000444142e5075a0711642d140d9080710a1010480d04031a1003004490b030540b24000007030550f1040c04105e000e0010003da200c08000341303005040c2d1111480c91407194820b60444d00904040f00c0d07030208407509070074034556603911200b0494105190074038000240c074000408100ea00020b80c1013094035512908100302146045070300302d85011013071030303030072043d985900150604410440721190301d040703503100b00810398040340d020a00d1070808001c18420301d42e0040040040d41c07403c0e0f034050380d41e4428461561040282c3c2c0c0c0134910681c00078405285520194006104a4000309840d4404002190400800c2002003100c401d5584c0900858880b240c0584800304040c50000e041e6404c1080e101c203050305228051130101c002036968810040149800e00c1c05907001200255134425950855000c5805d2031000382200b0305002c00c3c0003c0c070741041d00c15000c0740c1030468500814031116a0301d00e0000d503a0300080d030340c0488 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 516718012 1250 516716762 516716791
    0x1603080f0a050105031c091511010c030506010c1e0f080c070501020625020f0601060504080105090105070507080d020d06030c0e0a090c1a3903070506040b0c0904090308 74
    0x40303031950060070f05031903000f00176081d001880320032081d0b9801c440010390103105183d040001c1e0382e940c04031003c44040950315a180010107801c0090f0840c0d05034106a01498035107014860745990000004807590762245c190811102040c0c0c90012045c003001c0000c18502031103011100f04400c210140040800d003c08841001c1d0310341005907147c10040725080c2296228071a60503c101030b030564920b40103050300503103c002000c00c1c1100c0c10080241c02031000b2640000d400c0041c58024800c455200c106503008004908117044010a2403040a03005800804c011a203043c6035900d9a048900b0701d118410100b0426599191003001076010784120044400c003040004d8140c0d20600900c0c56481d800051640d01c9814105c02c00e103525280b008089180805010141c405900400aa032403500142c6070650661702211030b1400506610001464a070000d010410010b4000160300350801c0c0d12200c00707140c1c3d41e20360b1001052801042507090344503090104000078180c0091006014252000c00030f517 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 516719262 1250 516718012 516718021
    0x20706050d150f05012a08090d020d05030c0c010201090c170f06040f1103011802091e090c271b070813030302071a0d0b041407020c0913110d05031603080f 68
    0x4500d0404003d02c0d80810720100786c40000a0504401003031124001046150589956008690400350220b0101c41d07640c000281a04041c40030029000350381d02c00d10003801901555519404030380391030700ca81503c40c5490543d40c0741c0c50f2410302440e08804608803c403042031900b8104030001400e07102082d40d201d03420300900c041504041c051240315210030000c5105910080d400d000e1603400040a000d81030100c0ea1401c80070300d041d1405039004203e004001c0c640c9a83c60350400034441200c403240b8600c0240485290b0000246503262a401045000030840481284541407502d104e0844000c008120010308505044d141a6001040d0b03030003a4203e6043c203884110410600989605400074503900303000d042c5032601c8a401000301400080c01c089100000c05400d00348500d030a65031800981c0180c0d642820500700f4081407035012421450322840c09140352504032000c0c04000c4641c0c0103030490baa80e44140201041241d400481e200c02074580c4080601b8010220141598a02c0d05120040b0108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 516720512 1250 516719262 516719297
    0x50f070f020909150c0a0804020f03031e090a08070e0408031b190f030506180a27060c0201020901171003020307060e031006030203030406211404050f060403020706050d150f0501 78
    0x403001c450107900c0726089600c40d5000c100d012b082c080e00190345132004000c100700c08843c0901c06c190460b04078071780030f440d00e03981c0042044490003500084030036480308804100042d010302c0500e42042e040070707040b03130703a034482c1c2c030705c8090103c42e101408000c9900090b155003006441908810a054155204122a42e600000703c0942e0310980b46546d10016104288411002484245810803642c401c0050b0301c6d00c000140e580c10170300040074000c1c0d00d41002d001d2002e000b1540181c1c0800b8605200840c80c102d400c000284c02e006105000c180c0d4582640006180740303828420350070255400030102e601d240da841000031302082000007102e0103405001c803180b240141c14000e000c16a40d004019504003814864225010494030300b01503a410300300006009150242d00c509400d41e444501d18225070304c0c0c14246075103440c0c000c8802510645c405410400400e6002c40c01c0400d940d80c0e480c226a031002c20100c0c40003e00030742c40d03007040300300212032000420341c004540786400c4035001c2e05ca40c000030b0079580c0031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 516721762 1250 516720512 516720517
    0x9130b060a03020c070e0403030e0607030501030c18090b240604052404120c091103060a05090a2a021e0303070305070504031b05010915050f070f020909150c 69
    0x440c0c00920510045240500a4002d020501440c40c203c4942d250f64030340300780b46081c00f52029404255105040d05290b07109104859020246017001c0c840f551541e980c40324600c041d403280c0c1422002c401405a9a110079821402500b80c01c4203544445051a25016500c1102114490300090050b02d140c2d10500340281a941110742c010300b44c001c4181e0310052001024100240d000c00b0344001c2001003070300001034084601c4140141c02e44248941402078060803101902000c80c0a807106104004150780c80300c15080070344005031080b42d1551501e486a01c00740905801000c624a244100a050716001c6404907412400c10740c00c641848680c0502c2d22030808480e14000411b400400001741e440d4002c4d00f040f0b82112542c90098a099070340d880d94000d0849000881c1c600520060b0100300d95070b8081c010002030152860a10070708007100d40080c0040c801d6602849000364082000f10034080450080001150040c0200b001840c11138a255141d110010740580c403041c00c1000314201e02d0380d185c01d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 516723012 1250 516721762 516721781
    0x1d011d0315161d0913021f0813020f011107180209090c030c0403140a0b09010b01030f0209030c0f04020915270a06052b0213050d02090103170d020307050913 69
    0x1003007203680f0004402d01c03240b032070010300c4400340140141794100181c40d080e40c2c00781c005000c481c690074110100d403801000c07010040c0c000e2201c0c8194120210259981200781409018242461042e642005000a082c0314259108181c5e40300c559950302c0b0001c1c0b194001717003410001114090300035624050305001c140000d1b91800ea1402c0188014400212030100c40c803141061201100c0442e4415650750307600c0c03c82199100c900340d459444501c090351300b601408044044010b800d41c2000d9030030300820f603640d00c4145a644a41c1500100b20007985071a41112907260024200c50014998665400c006912550302104045661038241000340c1e0709141000d01060014407142d00c0301d140480446407a00301150070743c04144940c0f001c0005c030001d2061203400201f00c080c050784600240c45c1c605403040c4a580803a002c0c404245500b070050351000d05240c15243d00c04807070000183d00094980c03140c0148006488482d20000c10312142541200107845414002c507000c003d004d00d0501c1740350903551182c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 516724262 1250 516723012 516723047
    0x60a0b03010b0703030603170a020c031f0b12030706020306010818030d1112010611070b1317160612050a020903150a02070b1906061d011d031516 64
    0x41c0003000b001d0340109490340c000c1c035000c02c0c413a0f00d940707031490220250000f0f1801500001270041c10250107003c0e840d140da40844c0904a000c0316032100000e00040390914100701d50380e5600860155035180786109240315002c00700c94480e026440e0010087d8825500540410031503400104501a40c03954891040103001c003650900014080c041c01900f040a44040b00d5034050002c55214440c4d44520750007018656100300302040f101d0032a508110041d00301030032080d41009580c1c0001d8a08096908541c00355000d0040030b061a811241059581d0b0300f0f040c03c0e62000c040c000303601680a41c95007202a025202001240c442060a80c12846660f22064068004000724140103105185661344402c14410151414041e0f541d801400700d0111214110301c0e101c1c514600d1103116611906010b000300e424051400d60302c8001c15800401150300e018100007041c000742100e44013460140d140400050112003104488075017100f141d150440b0001543c4100e02c1d00b08081c3ea2180d0210074540c841c0e00b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 516725512 1250 516724262 516724267
    0x41406010605160303020d05040515010b0c0705121207050c130204030308060d060b1206040b06090103032703060e0f010b090c090103050a1103040b0a1a091303020f0601080a0209060a0b 81
    0x142d800d003d08032060002d0f03081c1070303003401207040c2c559050103458401c41c41a03000e080c6210780b08159581e26041a0043d480075003090145550325880051002c0585800b180c032022031000600e50039141000c0e40b244d1521400001c541007080203400a08021022801c64003008110340e01d1131404100d000d5403001400081c00c020202c0e031941400e02c2e414004d54015100842c050710160085001003070b09108035403590388010100030610000001d0f558100b442229040b280703500d0351700c00424007c01c041c00016400030006c006074058000600a50003103520900c2405102c00b0002c0071520f07061540d020411075400c04d6038000d164680b01b441c40784600c41c0c0340d8905081001d0b510044000302030040c150b014542da200010001c0c00950009188594418804a2014070349200745509071205150001903002481488441543e0b555400940c844005903c4105c070f0503060500302e00d000701540c0240803034050f41c0008a010304000c555148070b2802030300c42401c00d48400c13090294820240c42424006d0005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 516726618 1106 516725512 516725527
    0x11030f040807120f0b0c070203010609060311041407030c0c05030c0105040c0902131230111501060509032104090e010b031c20010203041406010605 65
    0x203c10004080030759a0741c0b55003000d0032000070714050b03240b40001c1c000d040c0706094941c000d4000b4001c2c00b0241d62901c1101c010602808191680c0800740e50040391828540541440341607100016a010303038441c02c04400070f0444032403042c01c100c10840343c0750106004002800500808100004070b81c141f5251120901c4129030103c0b500b01c0c0140318070380034a140221503c088840031403280c0c9040c000c92400c80900302c800c030b400b084024100030100b2107031002c00f10070071868085512001c14403803801a600c3d0340d4200720003001001403000300c010b000380345c0702d200902029a0050222035105494984520700c042440d582d0140002000c2030070060001940a20111140780d103000708409283c840203e0344a1900130101c03164104e401c0e4543c08080c2c414000b128503210704000c9400c4a14000b841c880c080c2d032040d1425034031650140351861041d18003043c0d140c100c4204d40c6649241400 = true := by decide +kernel

theorem cover : BRFrame.Cov 516546762 516726618 := by
  have h0 := BRFrame.cov_init 516546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 516546762 ≤ n) (h2 : n < 516726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
