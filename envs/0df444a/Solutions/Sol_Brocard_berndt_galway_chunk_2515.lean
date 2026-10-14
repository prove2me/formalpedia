-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2515
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:56:10.559771+00:00
-- url     : https://prove2.me/submissions/504edc1f-775b-4700-b190-9507d66fb24b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 452158273 ≤ n < 452338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 452159523 1250 452158273 452158297
    0x71e0608100510030b150a0503060310050f0115030b10090f0902040b090f0a0306050a1e0b01020a0b0a0b0a0e0403090f060e060a030912090302210619110c01020301080d0503060105 79
    0x9104c48180007854407030806e2207034a540c1c00c0000e8400040d540200180d4480c1c40700301c01307640c2110181103c002c150354084902450184c01e220062020600c110300e1010005001c5c41d0000301010400041100300329031f81d41820200e0b0b8480c00c2080700008094540300a00200d40c4254105032822449102a00418002c6ca10990345104110b2898035200c0c0408001c540003030040c045c0e4200b07aa00708008000c0c80700125a0409060201d003885007150040344480c20b81a80203144040003511140c0100c2c0003d008080f00c55229207146182e69900c644d88006400307c11250346c0c03182054607014044070030382d602c8600c058250340400c0000c580c000c2c20700b8001660039244150f1710008144124000c4c1220b00c401003d203503001d1440b03a0325a9000da0a402902c1c8260348000b840190f800b84403846008440c1c2200e0640c2c030480001c0c069004e840c0c004000017900107030105d0380150b45040c0241d039030048211010a69404001001003030740c100105100c00e00c2e903007401e904d50306204000901520888481d10380c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 452160773 1250 452159523 452159531
    0x1a2205150901120f05100212010f0b0d0903120f0e0c0d02090714070803190c0828020f0a020a061a0a0302120c060d0c090b03061f02071e060810051003 66
    0x2408050b41c80d07138407010380c050150788100c05c0c0384480000039040340d14015181c0e04101c00104200e00c0200d040710a440c0107810701c074105111000310802508503080b04800300a42841001844c88160040b85126101c0c1100403a400654a400b9403801e04a00d0744588500a980313080c9015071660350349190855000e140c41c82c0410610021701d074082c0f0070b800e0004c050004c000700b0085221503030010010031b41c89801051052605082d011907007910159810f086800a030b151080c00402c0d04901500c00d01c061100c05402c0540100004d4820b0f04007a090700d02581281c000c0c88100009480f40c0e4503800c421640640380c80c8541c101140c011421400024003683e42d850207580050070802c141002102c000f84a10b541d46001034610002d0708100c1810804108210004600640d50b078069920841c8040e041400c3c9000b20600002d44060300061501035004900700800c1342c18088004072a103a425561010080d4070349407004111400041103541c40030300004081c4072980d184580040071a8152038045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 452162023 1250 452160773 452160809
    0x60e0f1e060c011104170c0904050601090b1801031112071203271509080c030a02040903050408030a05070c09050f1f08031b1603080703031a2205150901 67
    0x10b0041c02050b44c680500c1001080008543c0003800034003c07003801c0349003a60100c501707010600c00103500660700146540c01607001401005d0b0182d02024091100604a00807582c1a1540340c00c0c800c000e8009807020854000c200304d282c140000e5460b1060080c1e0f006105451800d4001805080c031280014200000380d4101b81c1e080c038664106950808250b0f041d02c04040e91402d8880b0307285c130304420800109048001c0000c002c3d0000c24010b003240320240142c0b1504005600f000010303c07480c24100c0511200313000200d14804100050000d0004540742c00341d4400c0c581c2440c80840c00541c2c041c82c0f0140c02e00c01000406c28405640381d8100f40082010036056803000144008908103030021246407001049007000300d40e4803200c20719030045070070a5503c00b02d0341c402c0d0141c05880901016200c0081001007400191096009014910b804181c0402d00c500c02c4001070080d00c0d000c5c000d2000c604801000b524a90382500c1055000019001203003120700d02000800c0300f10005100d40034002c0c003084103103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 452163273 1250 452162023 452162047
    0x30615050306240918010c0903060b0a0503070314010e03030a0b0f06030105060d0905070506070b0f0609010b0f0c03041203032313020402090a030f05030a0906170109020c0f0106060e0f1e06 83
    0x14540e2985c2c00b4000c0c41203050682d001800a00305200c00e555080c2807802000050820440140c190349014020707007101801d5454818903140b0403020404190741c1c3d00a58850b08500f071000c0e41c02100c8031500425441022030030000449134103101240300c0c402c20401040240d070f4803401c807014105165004507105090b030803da03003032400350307800190804000102c10080006405400e40304c0c80800442c1c03a119111541445481d0f0380901400072407a10030891089200c0c803940107840c884241c007013120325180c1c54500c4204600b0b401c10040b8040b81c0c0b100c40c07030341c500008104191034a90078184445024601000030a80186071200c020b40540e07070004a100300c2d034030b030707402c040b806540c0003a1034004284c610b1402d50fa032940302c0711010002602d100000702d00c0502c01c2c0d21181c0c0c2106c014203075a40c640d00300001c110096002c0c10000d0820700c24507400c80d072242001c0c02054001c1016445494001c08202c0900c400c0c0d0503051310b460311603072542c4039121031111112108040440155034140d2941d0100c009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 452164523 1250 452163273 452163301
    0x709050c091e0402040b0405130b0105090d06020c1c030518030417010f09082d2709100915080304030b0c210114011d01180306150503062409 62
    0x22103401900024000c107106e010000140200e400680d5280c803580c01101e004c1040f680304020b603d001620070000009146005045000c07010b00941c001031078011104136440c54120842c1c2d0301001c280202148200a940501c50f07070768885000380e010b44e204e0400b4900c26859114501692400344421701e1010015102580300c0348260201c00c904000300d0030b0074100401c06400030341c000004a02c0c0d4403003052140d2424480000c00c4504080454280b0141c6000f138901000074201c0c010000409041004282d91404a41030151540c1129042c01a090040c12003d440380c1d0291041145200c910030460b850002086030112070708840c040d0a43d440340008008203100340c1d1001c081803172510314000ca040750b180344698121401e03440c00816905103000150340b85140e80b1014900b081186030321601f1035000d0406081005c83d0300c09000501c640380d98400c021242505030f00004000c1116050000703040400c40290032554070340505169a0300888040311951000000d6401411402c010a82d141e0071807007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 452165773 1250 452164523 452164579
    0x30e01050d1401090e0c01210b12010507030e1b1507060e030a02030a021903080f070e030102180a08060408031906050d1203111e070f0614090709050c09 67
    0xa80b290042d652440c01901a0039212040c0440340140c0710601c4407980900755800e9480a00020700d1050390301c984400c030062101828403600405180d19500c100c0d2401c2c80340c02d20544041d10005024a0340310f540340d26081c1c6c1c0c801c0d0780101c81d0200c41d807c00559a04580300c510303500896159951800c072441c013032000c1c0030703041c01c0d050b810710011801a41154010015011030541c6608456a803205458051032081403e00d01401040c103100224a541e172006507800c0e4403010301d040030800071021202007401c9078481c40107003140301c0040e08540010b1030000f500344000c02c40803004162030300740317526040c014ac0b1000d840f000c6501080403651080d04000e401c40001048018400c01050007942070641c1d0543c0da15804000107450054000301c0b0b45240d00079151000c4a40e0092041d0399072106c1c486509900c0090300ba2658014102b01d1b00004900c0d02851080054101c6600880d04211802d1850f141d520b82040754424200030406c148860b160302a107200c12400c481101082c643c10038814400d02c0703141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 452167023 1250 452165773 452165801
    0x1403070f0e0a0f020f07020f0109050307120c05030f120c010e03130306152724051804031706012f0c0307033c0528030e01050d 56
    0x450000782840324200d140c2d100d0800300c20107102003c0c0c1020702100b20710607507600c240c2c1d04130103100711009414140010308180006050029001d521000002e1800c0110341c42169030341d0b40b02d01c4e110b0810150030140402000c0680041c00e00320300039401c0540b01e2000180803005958003049025162209400102041a1400a4954440403080c100c2400c0034580416030702103007425021341d421840090048200e401c21041c400055440345c941c1ea494070443d072406c1d03041d01c2c2c807040f00d18841c610401298840a8260782c3d130b204140d15280901c26510104200d1640000c140001c0001080d00500180c03c3c14400301d006400b41d5550000586000c0d0888105100c0001440101251001c03541c1c8840c00c0c01e03820004641004498504050380c0d441a03010082407a12070106c401c0000b10301024510b0006078149421403055601100a400a10404010b48003a4011680d2128030303c416444d02a0100020810280380b04c000d4170094001644ae4280030304100c4001070305544090340340d01c442c01401d80303c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 452168273 1250 452167023 452167049
    0x71106130f061701051816031409030703030c170610030608030a0c050c0d1a060d02030d0203091008010503060f04030e060a030b0f0105031e0402010c0206070f0624140307 75
    0x3442d001060b4081e240000d00710300401c100080350a00c0c4c80307455074080710310002c3c0d50b60325566008645400e4140004445044c151226203a40310ba000001401d807142c100300340210b45400300c07400c000f029110989801e400780403144101d8080c40c03000c0c8903a168400402c2d02c090805a00c0c440c411030082c8200d900c81000760001080304403c556000900081082c041c3d002c407001c0c81c4105003001380a441c001001898078544ec0c00c841a488400ea9929078441e00041648440040ca50003080c03c00314078415040041c0c00029165109252000440c1d40748001441c05401c0c1d503040c8804070365a40005032a00d02004a01c1d8005000c25105c0d01403c04d044170083d1031951100b6042902030050003030140064030403000c7d00d40c4000d1035445a82a244500409041150688000c486a900c4c009010f0700680c10003c000444d00c0c0982c644400404000c0d01c1282c5580d0703010500d040c91011140c1c0e5040b52800c410507100c0e503050300c480c40030900040e90b20700b284400f81000e205002920b4078040d6805850700030300b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 452169523 1250 452168273 452168279
    0xc1003020306030f0102040501020c01030f061d0106110a0218270109020a150804030c050a05150f070c12120e0111030603150708010b0a0c05012f071106130f 69
    0x810340280d40900303800e80443e44d1001d50000f501e8241c0c040d5001d2240140c0c0310000d030354281d40c03282d00b14a403000e84032200081c1040c0c407100700608202c004004c025403030480c04010401960302c05100304181c5070b9000545084160342c4d0015405909200d07040c2e0514561601181c3c001c03d6000440d04003c0355800e00404800744010740c10f0180003a04000d0303104441c82040001c80d5031900c201c00e00784041c260b441c06101d65450b60250342000140c1c8050340c4a100d101114400202d08000102c10520702a000c81c100d454080c41c032030540c910013031a1004000082034000c00040448621421000c4507003031030710003102c00c942020010030400d01640b4407582886000640c101118000b140a50400e0f42034400c100c40d403110908007414241c07040380c00a1a03020041007440301e040e014220400c020728000010b0485030316040d096800c00d4012402c0f403503444488281c090070403400c50060f0010505081e08025080e1200c0f40c0c40d100f5070303003076034050302c00051031074001c102c50000c2002804540b500e04c011181c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 452170773 1250 452169523 452169527
    0x70b04031b06231504020708190504051e0a06080603010e01090b040b010b071703071707171303080105060304081c0c1b0b040f0309080d0503061e01020d0e030c10 71
    0x203650001200e2201c1540c001181c1e540c0768103d05100c2e1140760001e007043c203c8003050000079405040203851000c824807a401101c10807101e260008006961015125400c01003000741c2c8240e90ba85810a030280740c150b0030000d40728010301d001120920306080c201680c070310780807030301500e681820201c055180c01802e0080008d20b039401809180604192036042c1c1e219040550948501d00c006081c920fa401094410f0f20481c0008503444055840c00202e40c200c1060034240300381e000d803a5078012924814215550081d4410f0440d0701c10804000c0c1414007003603031006080500b060241b14051000040014280884d20b000c8070070300031350807541100c0c16844103401e40c0104211400c03440081e662a440c3c100340c001c00c021208071150020105082d603221071351100c5c5520030301ea00031802d1005141c00019452000d20850208040d80c0d25034541e00d2030108104581801200007007051103485940c00c080690b4000351803010030104e810000d040107800310019243c00d4540310240da010440d00540d030407180d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 452172023 1250 452170773 452170781
    0x9041410020414060702060f0a0201061a0c060702010209060901081003020a0807060306052e030b04021306120c1707050c1f15080d030b0409050109050d020f060c070b04031b06 77
    0x60120182000c0c0c0f0184008000440c80341501c0039500000a10210840c800309800400301e00440d0f00000600071750355501e0000d0141320510b040724400700800c1100588909001a40d030002e124030085240c40031a034006140c43c01521091410080c1050000310301c5616501d40502441c0c00821002e113a43d502c01d49655a800207000d85d2000070f080510010301414800d001c2d011440c100300d0040344202c452819149090002201882090344541b1408151340f00c40c401443e5a00c40103500000560810070007612061800180c900042c0c60400b02c1c1c400d00ba400b540c0d0729803500d01d0540c040466240d6000489160144110b206258004d80d0540f004c41f194414800c00d02420300c603428401e424041c40e4118890441c0e100b0f0350f0070b68109541c1b95507003600c20303442030328066001000082c90407007541b06d41d400c43d001d8102c03c43d210b60000003040300483d01040801c003140307145030040009107015040711810b4050040d0040c48581c0e0f81c0f0215041501412109040c4c0800d01c2a00540b15018200f803c054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 452173273 1250 452172023 452172029
    0x105010501020f060c0d1e0f0b031204052407210806030d090902030709030c03050312060904170a090305012a170c0702151803120a0e090414100204 65
    0x54440e040c589030f82401c0204005101c0c5101c1429107080c24441c011960140841041d010204810700300c45090b1a0304510502d90444070401001075000b0081007810700e401000341c0c190704403901c140000c006503512500341c0031076150016001c02081c0500000c004890148c584012319208070a52030440030901c0400c5000a07251b282d5038416543c440c0024552100c5084a0000c0010100a010b000d1514990021900000d4510706007400325602d0701c80042e2140b0b1074100700d625410000f081c1c070184078040c503035640209080350680420b04280e07a50306003030804035842456404008c0f0754024414041d820328002150004000d0100318134400c42c0c00a060001c80d035101020400b04074803654144261225100f0070a0351500c9a100d0302c0e045045140c0380c0104a040f81d20046801002110b404c801d0060040110400314034552280c6070402c050404030000000f00300c5540038410305a000750303c02200d55114100360340200701510360b030030000351380c07803800d00c6182d964400c41501d0490f0b0b14050b4014421 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 452174523 1250 452173273 452173277
    0x50a0b19060b0c0a06050402030c030f060a0516080106032003010b34110301020409060e0a0c0509090c3403030f050708010317090d081c0c120c02070e090105010501 72
    0x10291103240c0326940d80034034004090240d010b00b84c0c035400903449034400d540090000382168140d06103000000d18214003e0300c5600c15030403280601c81028030900034950000401c42980b04d41c14880480249a680d0504c039540405d9140c45001d8880c0301c01c10041206100500d0b034450b565a16681052002e90000c40c04020700808801a90600340d12500039840c00020b00b20244042c50301900c454003042d6050043c6c4d1b0f815503080200084098841c4a40b100409801d00c44040a15280c8180d10844264144d0403040c080b00700044843d070365602c0c0b00c032030740f0440144440391280d20540d181c031030081210740e9640300307a10b001d010300d41c5003140000505074851083d5400e01600400d6201c95090b1201a6141c1e00400c2e50f510041c40046c0300602c0c002c4015541d01c500d01d00300240c1c8000288000301d100e40545e01190300040720501c6400d100d11140002501030b40902907520700404c01010507500e1051240207aa81c0c08491400c0303842403150a0007440f95041480103410001021030092000307100b002c1c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 452175773 1250 452174523 452174531
    0x912060e0c1207140103020912070503100504121b02040e031b0106030503070201080717010e0402090a1505040b030f01020d0f050609040b060108040c030209040f0c061119050a0b19 79
    0x8068604000c41c07041c007800308409400720300e2400c0c01c99140f590700701131004d05240e024800122079450301c030702c1c00b4451145800204200303031a2800b89418040d1000d04000041e041c1010400800c0103200c400d40d801d41185456500b02c019885401d140c0e003540c0500950041c10f101c03c40096030400805481e074100c80c04072105013105401203550032070761030340310040168206105200156001d5049a540301c01941440a2055007401070200d41c0e0000741c0000c2802c100c441c05000960402020140c1d1081e02410704102401c10340070182841c02d11803050070710aa4503442221031a450070f00c03c00041d505420300954403900084240e1020f84140b08001c1107081c607082c0090064078012507118011a0403140003c02521140011607244800030010b450f0b041e14000b00100503120b001403d84158010500e41007018071070314000d034146130281c2c4003c04005108545604404000c1031403c0b002c641c2e147c03078a61036015403070034904058107048003401c04455076082084007407227440308556042d04c002c4200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 452177023 1250 452175773 452175793
    0xd0f12020706030e0c0f010c0b090709050703020909190204230f030c060318190308160e1503090c0d050708010c0906050306220507051201080303070804120912060e 72
    0x10300b2555134000500050f40460781c01ca100d030a04050420100c18180741c409091b4030b082c0c54031a44d41c0400d42e0340082e10361108804201c403040c2c521501e41c21100314030b81540f070700710208005190044003800000d00805078641c0f90003100301503030458004003449041c01060800114135011102074086c141c9004a28003a02640030349004604d01c0c800f101c000382058159110001001d40a40d1100c40220142c03081880c01c445200c03000350840c14440c0f082e5030b001d0091500c000011049114495500248840080000d9465030b07408000341880881c102c10903140d58841c0e000a103000803488031107410000c2041c091040c00404204c1c00280e60352480240b240e8031082c94100c5500d801c0b0f100c0e6800040040c40818514940a0b898481030070b02c1421100c4c1e1085107200b841c080703c105807045004036000140c0d00a500c40801c0d8000d00600d2150301450440c9060304000d0200f4800a00040c4204145082d03244a603000e503100300054144040e050301103240300d19110000b001c10b031641136500d100720f400704 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 452178273 1250 452177023 452177027
    0x2010e040203010305030319090602040335040b0c0304170d020d110a08071b180605030109050a03030203061c0b01060305180a03030e03120f0402011b0f0b060d0f12020706 75
    0x42c0d04880c0d003c0002d5107955280c0010320b00940010310300f000a1500c4070202c1004c52a54000740c40510b003c0d0b1070340000325003c40e034101142c0710102046840600e0040080e046003100308103440498481c42d201558400717024510505504c01d079000000d102480401c01521a03030b0000d5150314007405502159442e49240c90140c6000c0d41c05804004030380c0c46500240c1c0020300007006000810312501448841190b04240850000c0c80d5400803200245082e0344260031400c00e00524009150a5008000d061007540307546449142d03240c0701800385900000420303001d44440310784c00342075101403155400800c034a15144082400a1148a002030b042c40d001c03030006580d03010002c007004180c1009011800c101c0e5020341c060808003c2007005408240149000d203101d0707003112845002d01c060001e00e2441c6c20310004d401040f48820121090b01c00303800c028002251b08036004402508240000b807282c0e15000043c10010036040000c5c01c03040c814420780200000d00c054840340c2c1e501602a5007a090b110501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 452179523 1250 452178273 452178277
    0xb01121409150f0403050a03390507030801141203070b04020f100f11030c0d0207050301050a060b0f1812100e0d050409110403021c11041401062105100302010e0402 72
    0x20408040c3c981c404500080e00420040105c0e00090a003c2004014803003400c104440049001f100a440107000c01811094040202254240c0d42406800d010302c580b03000701100014065651612450700e50010641d5484078054950030103507007101e5a660b00d520701460b9501055038100c2c0280b0307400485817030516000b02c1808814515aa40c0070300942c1c00c0e0421941914030aa4601d0035000401c4aa138401005103c0c4c4228000f403500201011440c01c0181070840d10001d00d540e1007145480800e0003210080000c032203000018880c2d03691142161303141d5403a8030f113520304082d90102401d1080b040d09000858110744207103036160100078242220314641e446500000604000500400091000100c10303449110880b030840348043c145510703580071440a030b0181044011403949840d0400404c038030b2414881d140c040a40301845100c0801c0074405040b04180188400d01591500300d00481c8204c83d1140c0803000c07000d00c1484541000302e4110681409030000382d0016042c010380c40510b0902e402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 452180773 1250 452179523 452179531
    0xc030c030d050a0903120c03060f060e030f0312011a04081e100603020f041802060406020f100608030a030e10050c0310050d0b0402010f0504030c0b0415031406040b0112140915 77
    0x190540103070708040d0454007d110b0b1802440a261380e460380407030f220300f060300000c0203040701d0f0b00e51b4098940058205460100078906543c040e0b407042262140c4101030b861520304449410a46c0c2c18a46540a51400036004903002907070b29103e07483c1880a003d201880c012030880d501400d60f10311020500d5010180c0e5101c1c0006500150034400300d030601c4c1015400714000b500001e2018607034046035400920654031950002005900c030880e444914031061061050f2a01159070411155152514058907406050101000c1c1955207410042c880710074024504418141c1c141008039203456015155160400d07194080642d200c40c030042185d0a00c00f0352100301c15042959038020b680c6a90044030316030fa82d00300c0d4408000040c0300c0000041c1070020040054440301e01a5a2240d081c65049103880c0f500c2e6021904140c20550b0005e480a00f110690703410010544d000300c0c00c400c0d2140142d4072159810380c503160592414251001c00048043d00034000c90545098842561094405003d1203000765 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 452182023 1250 452180773 452180777
    0x3140307050324090402120f01090605070315180c030e0d0c060c0e01050f03070e06130905060d0f060c1404030f0c0b07050d03050a0b0a0312022506140c030c030d050a0903 75
    0x4c400f2901514006917402110b04440e0115000c581c030b950303902030079100305100c1240c2c070946600501181c00d4140c054610b1182d80703400b0200c0a54542640052400d0711a07010494a9944e203244500c41e91081e08100b80140e01c00c0106d41101c6c2040d03000034005030315003000f41c030200c0c68980c503524042c0c491401c81410945c141d45440c141f1201041405240d40054204010300040e150245881d4881a010301000d034110b50380c2440701032420404600b074803c024070180c03040400010980000b0701800c00d0406c4290813030000620004240801c5d9039400081900003a10307840840c000080041842c1a1780845114140704107040e40da4241c104840e000c0d41c0c0d07004003d43c1112404550544c400c0d800b96a000503040e070f012800195000100b40510a1b5400949004085c0d05040f11910f404001144040099615090502d0540c41c16986100600e0090000700701c80c84450b00c00009842d402e441c4420100d1095030794410b1021a115640d0b44501a0610118104030003d44070210310b101d80c0700255056 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 452183273 1250 452182023 452182039
    0x30a021e28021f0b0325120818030c0a120320070b030a150b04031103060c03060d08090306010b0910090510050706180c0501030f0501120f03140307050324 68
    0x1404044100c610004003914851303550081c2502503503040010450051032100300d50246a180390120030200581e4115000b425800c00700d0100140c0000d04894004000741c2c1c0079800140c0140003c1d04020b04800501e511901d07034100452081e901103a20b4003840e103c0c2d1210818054040942c460840500490b44d1042c1c2100c04204162456a0001d55109400507400100512035000da00140030301504000b454240200c1d0900c100b20407104050500c0004800038100c80c42c1000d00d01c100380c800101505d000d01b011003204c40401a481040d0b880b407a2001341a5007041d070b100c0e1800b0406030000c140407481030307540348582030086000394110402d07241d000c8d10760180b0001410080d41c0540c0619011501181d44107019110307e0b02e40071500490603ca000342d41d869520f0940014107958646003401d4849103008010054800c80048820207640c1c0480c2000344901c180c20161b5051083d42000d6003200d030000200207000d54800025881540c05c01304103119210350540418060344500322042d0003140c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 452184523 1250 452183273 452183293
    0x40f02090418320316020f0d0c090e0f0a050309030706090b0a030b0f0d032118020d06140f0403091205150c0f0d1406040903020a030302030a021e2802 66
    0x114612019802624084041c0c02c41501183c1514560040107030810384a400e0f0282c000314a002c03130401c0f01640040750307001e0341c41e01e1980b41c0c0b0309140800c0c0b00e0795001c0f40d5030b008019503000701841000c06441c5030505840000550741009601ea901040076944640106400480c0c014000c00410303090b035080240c00740c20541c0c840000d8000b080341a1181d60b110090440140c1e05130789190310984220700c0307655840348265103490340d020002d9600d601c2d00c801c907092201c1110003550360f490a208650301103414000c40c1c3d0701414920014038078000c0c1600c3c0c2102070740400003040103181d14503000b40e10964501c100766a6030440d85040e07807a0518028025041a2541034000d10b002c22515001a409006d0503d06580803420b030071181d01028500d003c10b522200da10b055450f41c80941c40e030040c0d09031010b001d0410156402912102c04003801024198007002060200b5064ae044d41c4191902030a16911184407007080400350308180d00c0f83d1001e43c455100010202c40409244030746c4503290b001801c000d42 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 452185773 1250 452184523 452184563
    0x302061801110f070311191707080c03040e090109080403020d020307081e060916060c060e100902040c031505060a140d090212071d0402040b040f02090418 68
    0x1109802552107992204030824406040000600c964208a600305665010602d400707032000381d24410081c0160040440b11078201d404d18003900c2680e80c8011141c0a411403034449680c18024440044c000d448081230f40c0c020080000300400540d04560702060036561800d544e030703090301c502c1880100303180707401e101c104014107101625011451000f41903c00080c3c83c4c41c4114542039559842c1c484140003203509100c00740c02880308035000030054024225001129442d09000250703403281c1c2c02002a400b0020060050640c02900c501c82c45030142c030120990030172141c2c0030b4441e1401c16841a0326049400020318040e00c41c00180d1902501403200040c0f81904000c006d410000d084014000885010003000169070020403501d0404400060b588034a4018800500f29801354514158030600781400084160380d121015020110344482d100e81d51403000c90007800002054580003420306000b11456002c40d00605403208082e20104000444661103c012200444014041c00325000709080300d42c0e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 452187023 1250 452185773 452185801
    0x1e060414060702040524060f0711030a050102041e1403070302011d0d0b07021203361917040b0910090314060109110a02061302030c150301050a060c030206 68
    0x6100100303054100061070f00070074203407003007120042c0c09001c18015407007050450035200b12140300c098819608006803802841b0301407040c1036004c0c0421824201d940e0007a501004031034041a4091700a548441e6500c2c1c0c410300d00d00c20507012828007440d00c800881c069500d003100030204000140104001403554006446e41a105c01c0075060307010b0840503403940b50f00c4e00341c1c91014107440b0380d6001603581340441c0000e04080c01000300501c2040204140600c0c100403c000c00543e51031041c0a1094118202010612255010306403000d402240401c0080542c00050340021a010300d41608a00500e80c541c4080c0d07200318080c0e210040d800f070126401d80e0410151610700900c41e4241900110f0300c9403038100900c00940513250700c545c4600300500c032083c80d9004648061300b06108503400c0650465000e502e6010041c846031031205034900e00015940c0411440e58200c00103450707008003a04d201d5621505038003d00655024052400b0f00080052003448803003452600b56000e000d01e9100c0041111100b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 452188273 1250 452187023 452187059
    0x109020c0d1d040204170601080607360305060a050105040618020f040302030712050c0604120308060316080a03110607051c0b090a0903030f0c05030711030d0203010803091e0604 78
    0x40c5090b038103402d45803440180085e00411080505a0303061307040152902105810040031504a0018800c0464010203180105200d1a4002c423a401503200000007100030304461199820b6841b00010501c040405c24900880703080c6000d000680c2c80c0c038240400d8418501c02c0040f03503039800d8540c0c1407807412640500319500100c0f0040b4500355480e000245041c0716174200410f64190b210310b040070040104030022400b2010742d0400d0801f072a084003629800d010060103000c0c086d10400160b11980e041c0303c0c210300304004401c1c0c60301c11511600000d0340c81701652802c40c0401c031440703100181a00300107150f6215501d6503840618000100e0494000d8501140302c0c0b80c0c1564843c0c032007401c15960500c0092090001840004900f4140c1c240142954440910056443e00c1c081003510400e6000040f0707580700045003018012100c4c000340301e40c654803c0e5488000044e2010001107000c1402000030190054100c4850540309030f0640c1d4200032941e00352030594045001c200802070b40031070020351350310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 452189523 1250 452188273 452188307
    0x1080d0e120f250b030703020a0203090414070f08040804060e150c031201090207151503020307141203040623041d06040c0215040605130c0f0602060109020c0d 70
    0x1d0461080201450107080c1c04100059420689200d0031a034140c0c01015140011204404070305454024001c10314400030380704104050300050101c1c007c038020001c4413940c11000d40308000c0940f00109180758002c2c29540da4001441d400c0c5c074603620358404c0652a0042d500161560701c0e0030f150440650b410304140ca032040c0c01580702c0171091030b800c55010140104100c0b040141d40e80d808a0301d0704501416050b00f02d14125803041c401240030a4400c410b600802c1c004600c001540c44100c000880103115650000350305100e0b000000c00c00850180c0b01c620949004e0f2080c03001038203c115103e803640594012240024a001c80c086840000000d006842d000e1860386141307881c0c0c4030680c0030b9281080980b406001e80c56502403007041e040c14401c00c044058148050486404407618110340c002c00604040c003540d44840101e4540341c151692502c07169484458280050765408a01c086040385110f14005070207134500000b0360000e1402190340c0e0004010140031461000d8005441c48160607103c104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 452190773 1250 452189523 452189539
    0x4050603070f0603051f0b0a030903030615111605100c02180a0b0a140105070f051516030b010e0d1529130b090112050f150a0c020601080d0e 62
    0x60216100d0a82d00261003d5940440c0d6440d1541c1c0021550460007440c03165001c82c0102003181c2c11440040d075206584070314010a03107820508007140641700c60f40060705034007108442d0f501c5054110910301240c40340701059400001c041d1000d03141081640c402c1c035400040c11514407604601c640c1c520104a84003d107401c0030044c0608002d10506000c035035184020340d039040c024071240313003030703382c48000f80143c81200140803440742c002021801010b0008010100048020080000c180266400b0035020f02072000b003450304c0c0e60100e0200f070355043d012020a14002d0022005e512555111703503480000fa01000c84540159104001100c1004032010b040796521014860600384885054000a8000d902606051300c241002001200f160319100e84920340000c416a940740c14045504440700815521101240f50404a0511081500c000c2d881e005803c00c41260f981740461103400358024034001c00c242801c1c3c100907070b41c2d03031000c0c00b4240300c0d98040348002d24068072a0400040710140030f0a038038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 452192023 1250 452190773 452190779
    0x1614030706020a03091505070917150f1008031908060d140606010914090403050901090909030801170105150609030c0a0b070501180305040902030a1404050c040c0507050c0405060307 80
    0x4070403608552800f10001c0d40310a09038040c048443d1440b40000842c001c10459420003207409000340105102e08842c1d68040d0b03110f20b901e91020f1011600e2500d4044404065113025200c4030301c100c20486500c0c1c2c0c2d40c40046008240c0c0d140010075030b645041811070b040c0d0321002801f026280070f0001803034207174805000e40407000000c1c01d0a030458a0031380d1402c010807480c1040da0006d4400c0100da00303d415070340300c0070802e0902da0b07642003401a00039416060040da52180000100d44a0b007040d001200014186500c0e6400c040d400880d2604070758000c074074180b09030002c0c01c000f406d80d034042d80c044148140540c00c2401e9460030000401805000908071040c501464021982d000b06541c8102c02984000c6900020b0040070b02903914150702034503489441c50350595000d080307401580190300d102c41c7d0200004221030201d5101c44404152000096600e240a16203240c2d0341c40c00324072603030040d07041c000038281850142080d162600d81c4040074142c0f14108a0a2000034034000f0b181950502c2580400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 452193273 1250 452192023 452192033
    0x312091401020c07030209070c0317040606031407090606030902030c0121110c06071e0311090904150b04050c04120204180f030e1f120e0319120216140307 68
    0x3d0002000d510054114035180d40108003142a0041032072061003816501140000d520841d4488502018615003165440d0b60500703100800554000400002d1645848007a601000600008448442600780629610340344214151403103058000d415034040d030440e40c0f596000d0b0141c500785a0001540520718030215040c0b03c25550640030b119800034000400c40b0b80759400f8882103500404034200001540d840400d40103110000d14240b00c101581c0d9003041e0f03a689448001c5560300e0a004260b0426400c050a060305c2228600080c2010f0070320300281102d050409008040c45464083c1c2c1180c201844e10000032159140804200e07030091342d5500ba1410500840701c4181010300079418100c1c0c41000e4600600340c039140c900468801d01038101c01c036041c4414080e8041541510340760094041382c3c103155020203010166980103581c0004038042c0c2140d1b4668840c01000c0985588440c0c10a0264245000300d11a41c3e0240181307510100b02940490140d0340c600d916605520100e81c98031249440d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 452194523 1250 452193273 452193277
    0x9012304090f0b040b0f01050a0c0609030f0206100806160201090606030c360207020409020a030501050a0f06050a03020132030709050f031513020306040803071b031209140102 77
    0x49424995210b50b607203121800e03403080f012005010b44007008400c804400040c200492045502e0410400054044050384030740c40404250740c1c800018070071440d40345030107814030704072107102d00051013028000358031a1800c0b440d41049a1000303003c0c0140c0e4985070f01503a21008007000340d10540d900ea0f60b00900050f414810f00008500035145101b5a90520383e1044c10217400350a000308920400c0e181005101884801d282d03c01e04151005a49807100d101040c0030f403540d0000603500c91160f00002080c0101900301905c01d45005104100201c142c0c6103050813180c0500510b030300710007511000d1005500074103814076060642110710494060100c84807121710b1140162126a1602100784006103404c04a40d1020b80030490b45200c140c3c5001000c01d82da800000d10480a07400088003298102c5218891030b58042e402a054800c07501d0325091800b03a039070082d582d00000947c6600d0000c2d07419450f2000d4030203503601d0f6561012008071101d100e4041d0840c5642992010700300c1c142c10a03160340902c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 452195773 1250 452194523 452194529
    0x10e0703091a0915152403071d370f0f060e18060f04021b0102041706060d1b0b0406080702010b121504050f06010e0919030509012304 59
    0x2022809843d0042225041140100c00c01e00c029050720144488034290740a040d20442c802e9801103a942039402c510380112103c8250602c980300000107010070307558098403602e40c200802c2092182407000340140030f00550b4101055007000d03d225844155403407a2800c502a00e01c60040002115403100ca00c0392001203140e10456604050394400c106080d00507002c070200800c2140c2540c0c0380c4d5004e072869502c441008001c0361050018418030700301c0c0d98659054500c0d003020301e401c188098102c110954004d40c41805200949113126054061519000078004c0c031460015020070100102a5520a10300759001c019a0084000c501e010901d51000c201800c01070119956150290034107080180c2141d1052080300d018421070f100002080100040c0d140c00d13400c6d1b26030f21503050b54840c2401400c01112100c000014019030f000021009841080d0a0003030766001c1c15503800385e001c039400c0c20030381010006c01070103d1400d210103221980141c1071409440b05900588540382c4802c040100141e000360 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 452197023 1250 452195773 452195813
    0x5100e0910061a0306101205010b0403050c030d17131e110a0f14040209060c0102130602010506181e070207090b030111070b130503070c090509060708010e070309 71
    0x60009103003015000301c200500a07080c03e1002c100301c84104040d103100092070580580d40751107500c2501403161640b610901c464080070880c0356103030048035800d94018803040d40e1a03c1a094031100600e4041000d400944c12510345810420306a642e05104500041c0b401008411101c10070021403071103400341c040350005401404151001d4948982c0002142e2402c600644001d0340a010110040084c0030130340700c001916050010844e0005806846842071241d000745001c2112a052340b0150041e00c4101d42c0e000e001c8202c140c40303070700490032204100c3d40c0c01d500c600b0324031041216039034407040f007500011260220600c2a0051300e140d20040401d64503000160f200403000c1042d600103105851500f10210700908c0b5a603a890f1002c8420b02841e40081c00928030080401c540d58491030071035a929901005590f04c1e00e1240c207010403450b12500c035015a2070701340300001300c1d15800421100e00c2004152202030707160b4205400490300100041950703040c10369640216004ca820756100340340600d0a1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 452198273 1250 452197023 452197033
    0x90c02030a08070807020a0201080a020d150603050c070803060f0402040801090c170d120e03040305240a050402030a0605090c0d110a0905040b07050c070b0a170603030307050d05100e09 81
    0x4a00700602039000100000100000759051011196000c20a1180d00740c0900e4103007a50b4507280540402403007440c202117202e914111000711106110043c000444110340c408008660304c0041171410741c86000d0006218140400001e6854680302c6009a60301d40060001410552140d03201421a00c1303404041e1400340b20341908004407288003000c8039030f14240501504150f001c01710003410246405000d9001c4903214500041c69000410540b0002d5801808842048611411038903412142d03141066040092600150801c040c40c0502806240e01030010061500c803500d80a000300b07805410f9540c00c0c040c68400c591240d032000c01d500c00301c900400f1389010080408081122009041d80312000040c00e00342000f001c00d921940e01c541c48034040c140180d03600d00b00b444660403d442500b140c07441041c00710342d000e140c5a001c0403040410b28404a003088139240e4208044d543d000c11144d00c0300140c03003040f141c1100b41103600415000600600402c1045448113240c114540089030390810342d61207 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 452199523 1250 452198273 452198287
    0xc0c01110301060e0a0f1203120b1801060215071403040201090e0a0e010509060408040510020c0d030306060e0d0c21020a03121416120c1506080d03140718090c0203 72
    0x11241640062035442c0740405030b14031f40714481c4c114003001c400143c10301c41480d0101d06820b000f03400c00b2500c0b980081241215203814414070041641c02e00842d0018030510290240c2103c0d191000c038010a015210b56050710031820320541c25501c014001c904104951600045d4210303144031444c05012035240100700d481d0110700c82402c50b140100320200c503a000c0424807010404040495042e103d09403002d20f40a0308201060340b80040c034541141c0c101207406031460605038141c3c042010380310240c1d20745503010f07010010001801c2b00502c018104880106d002c100c280032400b520520758944004a903000c3d1003540024028420561050f43e50703501500d0555800e69101500b842903e00221195041560350186440f048655840c0145030154031100d401c2c841d07002d143c0e46540154483c141c0390001c10841e8540d4090001c40c42042c8081c80b45070b0b41d40602034064011092000b1482d51000c1c00c2e59100c020446070076040003ca80c09007100d40002255104950091a0b03580d61b480d001181d440e00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 452200773 1250 452199523 452199529
    0x9010e011b020c0a050a050402070206041206020a0905240a11070311031203040f0b0a0f24090c12091109010b12060a0b1909081501080120030c0c01110301060e 70
    0x3d0880035041c441c080103c1c091200740d542000881c1a50010340740140c032050f42c1c1c400700b5001d100e142c000090000c500da8a20f07080050a4004051060782690b501c000e0a503588203002c00e100305101c0030650703250040180700b69903581002800b4a02e14528103a04d00307450200358107050084680044d42d001860ba08007503502c1c2810801c62420078000e2004528601d03064495090200c500c0030014815014000845c0f0307400d40507003100d2004601c86908001881c59045241054140800103d00d181c1e030f40f610001d541d00c058802d02d003100c1051349940e00540c1014807694020910b03240c0c101c50005400e1640030654075682100e82c040c1202c0994642c0ea8000064444490f00b4001c0c0482d11501302030300300b1310184c1e20203429074900030b40800609544246010781a210805142c200002510490900484000b91824000d0480d440722008024032660706d20350421034010204050b113000c0e030810109001c1c4240f0802000c812403c0c40000513001c090320313494901c5a00c280d0001000031025038500b1100e00d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 452202023 1250 452200773 452200783
    0x905010e070c060507050403060e010c0e0103020c0d0305091c0503180706090e100b0315091014010c0c0905010b0304050c04140112060f0f0e06010e0c070b09010e011b02 74
    0x116849140310100d141088004104411521000b084240c448010811450080742654003a6030701c03100911400604c08441c0b4003d2a00c0c141c46000201d110310000601e50280c405ca03619140d0320170182000179043c500607005003401500c01c010600c00c00da6850710100300100149010301441c0c2ea42c5a403030510010f41c985c4205116488612174209410412603136401200d03042c12944031404500aa940b81107240790ba070040f030ba2110304084000801c2000b008032904940c40803a40480301c0c504280c5131410301030041d0006004015240381368400ba4182ca6008094000e0203512a030f200e03087c104c1e101c403040d200341ca5003070b409407823007450100501003000401d0000807000b820665040103443d20170f0540000303100c0107100318032500c4401c2054005210007038202e084003003c440000c2c8840008400148003c2c1013006409001e40244400810610940303840c0f40d00034002c400b04541800041e44680591050140c41c00b881903580d0000801e0000d402c0c000c0c2844000d01040400e880003500c0070180c184 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 452203273 1250 452202023 452202029
    0x20d080415023d0903390b091f0b12030c06010506030c0903060c071403040f030204360303061d0a020901111b1c020d0f0c1707090501 59
    0x550072450202c40d05040448048401620400c2c1d104000210f60000640d210b03040c030100b01c0c5250810a50800341341d00700b00100c0d1005144415040c2c060440400d51045d01300d800109110551030005c07400c0402c05242090340c1002c2c940301a50703d580c040114030003107014400400048507484260350601441e25000b4030000c10f070400051454055841c00030b60711800c0500441d44035880100215088200d0310b815542000d4000c0c084444500b458040d082917a04000343c100c540c94040040500e420740c0c084243c40890329149010b804140c00c5900300b00240c0461016403810b4415264601c2010642e1340301002d254051002c5000e000030340341801001d4600c1e6800560740102d9183d01c8001061003098075070350280c084140142c5420b11100100c543d146901e440e1031f02c0307114151442c600d0f240d0003040d40100f1402114003480c00441e07803540c5030258089070f00207540483d40e480d0340f201080d40003004410740c0303200c1c0c10444002a26240b26420721020042841460b61004a00b480980400d00c07500d405 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 452204523 1250 452203273 452203277
    0x80927070813020111070f03030e0a050102070b03190b0a12030e0603060a060c050f0115060e1c02040e0106080609150a090b0105061b060106170a0603020f100903020d080415 76
    0x540c07a241d540c801c010000400024100b01054001c407400d0b00c0305028a1b4007802d01c148500b282c03140e503820000e01c5000341c410341d45d01c54810241c1c00122507000240c0c0da011204094a83c43c1180d580e000603000130030596000c03160726070312941c446000303544154102c0041d140300509070303503000443d0900030115400b0100301e50094004100b40724047c2c0e0303a0740b40c05084410070301e4000c60000f0f0380d00c2e01c03504100e08051080c3e405d6007410118a18010080300e41d206503841035444100c49140c803010441c904030041001c52010600034440e40c050701b02604558031207861b0304000301c1c015945a911070f24050044940603c1c80e041010348013181c0441c030790680e41002c0d5000081c080550700c0e803a088003c00041c45554401d41d40091403800c2c601150100c641000004029101f843da0340b0700c0083c0c40b4649507050341140020b108001600002c0c1c0b403081d1820ba98015096080c21140c85c0140101070241015000900c800e00c200007005030380b01080d81c080c0c1403058141c142c540c1c1c07a0050b02c4c80002208a68501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 452205773 1250 452204523 452204537
    0x12120c09060e0414220f12140301030317060315010303210e030f070c09050106020a0201080a152106022a0a1505150603090a0b01090603030509060708092707 69
    0x1807480c2491803680c000e80c42019085c40c410624849141498612500130403071500440c019061000c071b007100000b030300019202e4480d0324041500410b4144401d0100030081080e10b614012810208814250700c0b90010702151080502c5501b1410030038000d038800c400042d541c007100c04414217500d88181c3e0480544906201c2c43e0000c040003074490140c0388440e0803071100032a1a905000901c3c8036540201001d0070201311658603580700a44480e02810300340d02246600c0301084901120b03100d610344039860201540c060900708109403115541880100008003064020304004c59030398402840204030120031207020621903000b80c4425502940e13440c0c076076080174480001040e5044c08050480e0b00710000060315945516502d01001920048150840d1005c81000240a00003c8207030754035000c2c130144805607a0303410090050b1a42c038007000b000200113010107001400c0a0b005000070602c1407940906001c8a01c0228041c90740d02400d5001e0f00300c8100716a10341ca4440c2c0a007d0704002c09181c484 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 452207023 1250 452205773 452205791
    0x72c06011427031e100204061e05091e0f0a080c0d15060603020409060b0901081b120f09100b060708130b03040309030308060915060706060911040501110601060c12120c09060e04 78
    0xa420402c00c0d45c2c1090300034580020080e2784910803c211070301c4840040468100c00d58414051000022009405c1e00516200202d005c040c0390201d01030b01201c2c034590082080039800824070000c01c0c2c10490844a0f8200c0b48241d0805135043e00a11000d014582e0780182c0321031402d6054400e03101aa4800b054401c1e04000c9079030345036031000541380d001943c50740c02d0a0300c41c64017110150500c0340843c0c4101903130f4100c0c1801800144802c10900854015040f1520141c00c440c2c01c80c1101ca014082d298000002c000c1e8800142c44400907140e80080d4134202c031036065985100821540c4121001c83c00507502050501c04c00d60000b40302504000169030349107072031a0610200b042c03011a4a4907078440e80c404514841040300903041500035084410007884004018403013054140c003e801002c1c04206080c07540c041e10070300056258100c41050fa20b44020040035120404408505114a820004501c00128100701d590080301d032081a030344e542d0440b0a01c2e004c40107007200d2102c60041e00c1282411109 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 452208273 1250 452207023 452207027
    0xf032c070f152307080405040510050102060112050a020409030f11030a020601261005061804080a050a02160807030312051302060a02072c06011427031e10020406 71
    0x80c4203800360070204100d40480d80c3c1e03000f180e01544801c0640e41ca000030000100300102010740125017054078107110380d403503042602440d49440c0c0201d90050744400700410018201200c03840540740a4015583c000c5405d802003007d0f0345100d134041c0c2c08503009440700445113900880d41e000a480e0000607500f80380c498100203446d50030601c900d0030540340c0d00e00d440051841c0755005104551089003140d44880850350400047d000845a445c0f041c0060482002c40d8505e4028550bc03981d0300c1403009140c480f00799000d0ba00c94108081880840c4120000180e0000341881100060050b15004261251461030002c3c405900e203010f603500303541800144002092000003440a0a03812079900380c4460000e0002c91502d9207a0b40441c5045941c06008044104101c442890084001c032110f5810307039030703100103645540b080702c59030759a10000c00110b407213001c40711b007803640d10515001c09100210282001a203490920314040c1c0d114518000500000e080800079411041004202036051514201e00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 452209523 1250 452208273 452208299
    0x19050d0c12210c020c01120204060504030206070519060f0b100804030f0e0d03030f18080301032004111812032506111206040b0d02010f032c070f 64
    0x907840910401d100808010440314201914840010380104040069004002d40d90210440c1050201e500310021090030b69103402109c0948a030f03030312414903141c80c640c00d02003d548616000d845c60b015100480070781702c00c96500c0002032402440c000c80d5165040000208407101c0181061082d0306001440c2d54440d049504158400d40600b0070b00100682600107a0b0702c2d12454040f40c2d4446454020750003019090340c816074001c0755040c03080007000c005d02c0a514911900e010050200d50003400100009440303102051000900d604d803900d2901038803004903040da0103801089003c07110101c1c21200004680607a103080707100c1114004035440210101c81d0301ea10800d41d2400841840685400c100f05244106042c410b5001c03d01b006004030080d80c10b020350704120f00103a0104082000b181e07452419000780c0d21009001486200304092560040d1100e0584d401c8100a0503140e00d010440d110100d4100504100076074a40c0c0d0401508403030150400041d030b0007191414002d0031044c4010031a101c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 452210773 1250 452209523 452209553
    0x4090b0c0904060509010b040303170705042601020d02041401210905070e10080607030506030304150338010302030c120402030f07181805150604020c19050d0c 70
    0x612207540c0c1c40440086009810b03250095500210740c0400051000d50344001442140d01a0b601c1d101e0011801c01d00304140c25003a0360388030005000340001e010340c40c1c0345030103210035142c02908031240210000441d42a038014074030040186501207001c01c001002d5031296407028009203007000d5051100c0707076000b02003080c1041d415901030b92604618100f0608000e0346000d0985120f02e02c80d00e10b040001924000d0117805448860f0003880041079005000f07000702401144020003450900382410321816001b00007081001c10113032a0401c030380001c032609400e200b981102440b030100c10b5041c2c1888109520980310110304262040003000200e584041c2940c03810ba040204902580d225400003d01e4032058190340f451038040e419000500c142c03884600329094040540c1440700d942d180c40741c000ca00e050001c0242c40c603001494005405183c0b2a03511760b004400800040c10b0401000303482d0310700043c034050b51a052031034016901c1402020800e004483e400c1e8034180c264034440b640d6803540704c0f074102c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 452212023 1250 452210773 452210791
    0x28050a060e03120a090c150804030f1403090d090f0e040f050f1207030206010f050102100f021615060905040804120503070206070515060406300614070e04090b 70
    0xe14060304401d0520494201e920030501112003811310840c3c200081c0400d207000c5032242c0002c840010268242d00750801041c42640350072007d9030303c5031015520703480440540410030541c6055101e188210001443c026442d00c401461405120080a03001c80c1c41908210038221440700104840345100702030607071145c0e03c80c1c126918818103241c100d180c00e821540000c01f0340201d03c001c4489180001c050141a800781e401c41c0c071143da8600000d8030102e154001d150045e00800320780400143c0039004500d2030707a900d00300180f070301c02110070400b0b00d0601c002d0100c2c1c880080c42c400c081414030500070000600502c0004000c241019696000a80300b14407841c0300d082c0041010b507003401014400e0b6040b45030046c00080d581d42007031070065250b00000041c800c22105c8480481e550b07003001d1181009036159900501c0396002040040480405103009510308500301c2800d0500107030369805912060107502c003a49050b810b00c5d5002400808103849803600036131508015001180e071a485683e0401026 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 452213273 1250 452212023 452212031
    0xf070f17030c06071205071707200303192a0807020a0807060b090702011506031104030203100e120a14090613030503090f040608070b03060604080f28050a06 69
    0x6818081c1540200a46180380e4090682004081c81d0010342c89000303010303465400c1080d40d44049040d10404011841d0a40c170000036000500041e00540b102c642140e1010800284070340d17070647e507034595401101e03181c81d00644107601e0204400300e40200080403484201d001c2c21350510b009010100000100c0090820100c0ea010038483d500134003189140c90303000048250790320f1045c107215010304644c00c00c0c980192580400a1160b0b84103200c1c00481418599080d00c6c024036005048000d06004204059240c90401c000801a0742c20040d15000ba02c072440c01080010211580c2403c003081190b640c055007508111390045640d0154111301c551003200740c1e403900da4610402042ca140114061807449800b40c0c0760100c1440b030004060020f41504030f178480c8500c40c55200784402c0e14103134810390503207078442c15081c4082541d400c05158030500c003810003810155202c010a00e400381e0305814100380c0c8c1214112030a06080c4440c01c40c00314006688440c00e50320182e8a00d607444e9040310020740144d0341c0f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 452214523 1250 452213273 452213309
    0x30a050c19090e0c1518060a031d06040605010e09030a210e070e0105010e03120d0905100b0102152505160623130f260703020f070f 58
    0x200941d074402801011404008400c1c64000042e034400100c00c50500c00c5a40b035500143e910011790440d20501c890204200030300c0d090030140b041d140c010100d09000e02d1b483d0400d004224122441001d00c00c0300c4071340140000d04060038030800310f800c180c01480380414071208002d510503000049550516030380ca0901012611000403244c0d0160140c141c40d00036062201fa5002c80700002180d00588a1103100c05000380d1380c1c0c500655808030502451038250300310580040c40c0c210b90030050001240c6030b090105191115075203a508148401c0c0f00c407100a6681c0902540a5904100102c0782e60319004001c41141401207840103038103403212104818000007161002c80c148500285c0308611401c080c42c90100d1440d14001006d40300300b0415601c4544189407040003200320f0711545000c0c40001c0c2c0e0176000701c0d000b504c81c0c901120031050b00341c0c0c01c140d001440c15076181d660500b001154410004076070319043c60349002400d003508085108555440f018083c85030b030503c85014011648203003501d10007104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 452215773 1250 452214523 452214559
    0x60b0f0a0311070302010c1710090b0301020918010305191a070c0204020c031e0f09010503040614040b0a0e011a13060806090c030f03030103030f1103072102010b030a050c 75
    0x1d0b66012420302d0010120311601003540540002c0c842100e580c03a0008a05200b00d100d2150010440e2000e6802c82d0416081009030100e5028103070003d070240025180c401d1040110741c220780703051004128903180000410900800340300400104005c000c0136450081552648010a401501051502d200050200e41e49602401f6100c4599078041c005545a0014461080c1c603908242c2032441d0850451400703d00200101c1c0c00c8880c0219100352050401e115440115403541000308202e80d03e603691580c42441e40e03017400150b44124810900122146490700015003620b00c0d03a01011000e03810030160150325524003c1a017404841034581d030f80e41150010043c0003500325a401040c442c095101030052500000c1141400064141d04482c20590741405403592403000b440058005145034130160800c5105445558030700002000302d0341060300342e4864803015449111240c100b002011144501d281d020b01665168120032005802068480d85619483e4116809040c3c0311318a19108101184 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 452217023 1250 452215773 452215781
    0x30b070509040c1e11071e0b070501050103060b0f0306010e150406030b0402091003031e0509030f010b01081323031608040303140405010509131e050402040609060b0f0a03 75
    0x1d070010018070154118100190039000c400340780000f103040050011040a0080c2500005c3d000c0c03d400070100c00d4500440e86146080500b01c0e08844040d5000000303140480b480a0140780f400742d00002044d500d5498404100e500040041e40950614901a001e59402140c80d41c11990380c803030340605980c0c070003c1d034040c120b10620307859500a203055030100511020b2041d081c400c51080d07a50440d03030303210649170446032000c0d07220040000701489100640a500202615510029801c18604010b0030400281c2010380d0b03803682891070303907540e0781d80080e96a00c1003006400c842c006981201c000caa50321807a10f0305160010640700c4004c3d44d0200e22100f0010401c803594081280400681c42d00706141000040c0e101d848194001481000801031440b0f80e50219411943c05031103042c80c0021000510420343d0394010190301c3c1340d40e2080e101031900e8444c4240307102e813820781c94001402c0c50107204200c111099904500c280920b03003c418001945c19104580c4000803000d01282c480700d0740203086002d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 452218273 1250 452217023 452217037
    0x10204180614240708070501050601050702030a06090503070b0c090123041211030313090b03010213051c05010c050703121b230415080a0b03030a18050306180f06040309030b0705 78
    0xc00b00013802070a00c1003000141000c0392041c070080c8555200c40004540c00d014440c00654550040122500040c030b19501c0b0328003492250068904084442d22641c000010071250840c3c4001e0009101001d51380c42200290045104070107003d464140456a080d81d001d140503942c500c4420000b00c4082c0442c401c0c020030b02d500010122640c1d10360034881300036088000d01c1a0030320941405103d504610303043c02542d04480d40c94208101040c6010308010604002d080c41025800d070808180340440e85c00e000e00072400000341c940310760341c20191600410b001030007511036070214a4a441070301d01300c078410000001200c00b4502901e80103c104000112001a201150900c60000a001400003100d185103c0c480f0400d444d20341c0195111809501074400036103040e9410f400c108100d0841d20301030010719545c50010b13510380a8a60700c40010a20340041902d41e1403100c0800c4c118038140090800c41125050075110140c0600c0c24582c0d00a001d0031194000101500131a2001501d05171080313040e2602 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 452219523 1250 452218273 452218339
    0xa0b1504200c060709050607030f1b03081504050c0a05091908060a270303110d050f0a0c0215070c0f0501020d05180a021305060a0e040302010204180614 67
    0x140d10503044040c1c8603845038802d0070080c050300000494260180140c3c3d001c603400a820399103005070b1680c048503442ea080250005100c40d0900f5806140005400c10f40c68a109480710000c41c20076a1803004d0003103000c0030742c0c1c0c807850800c410031200a9000b0150390039414182440c985480090001941310355142ca17400c500c08606150006440300c2c00120076024100c0108200a10448841c18403510000340301c00c02e500030030003941000068801c0d400300c4510204200310504103041d0341c0d403a8083da6002d560103400f80c0f00d0034052018203142840740b8840c482d4280020079038807000101d40304000038000c01081c2400702c2d0030f0102c001e10849080e401c02c1c495204008640e0340000c0a0010300500068030810a50b80781145480e10f1004001000e5481ca90003c00301200c441400c50400007070180100041d812074000342000800302001c6002601407032082d000942c03a241420501d0691200010501010700d0800e003003004a01320501e0300702461441519030802401e20f184034103811071090b054040c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 452220773 1250 452219523 452219561
    0x150203090613090b040b0303031b04080a0f050d0201021315170a020a0e19030b090f060412030f0605100f030e0d0e011403010b370e09090a0b1504 64
    0x181440c182c5070070050350159501004599803038800d010459200d28003554040c0d000b00049140c0d407441540c0a0070030303109000c9051400d45c81d841654140000703200c0456690380100f0040d420000c0c14001c20340000150301c02107041041c0384814160790111440340440c0c888440316022120f03485240f0998524595016020040c10a050300c50001d512007034444000402c4c40010044e01d15183c1200b901c1031180000c00303211a411611400080400508103039100e120300c18030052900b4042c420948940c1c0610b50820f00390010100c081e00707a620704e40072206901e203807a809215540d82c0e40c1e807024040d4000c1c50011420903034004240c00500f5a400f04070300c0b5114402c86542034a0307018040c03103418035003a6581002c0101c28008040a4082030091055030401401541000f110f180702c0e40804030030385040202028805034400440c1d04020f22b0002c0003400c00524aa960305150700103e0304070244500412000640d03841d800d108110150032405a80c4d40101c149459945507000003120160a864105c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 452222023 1250 452220773 452220787
    0x70506041101110a03090924060806090901140406020d200316020303010e1602070b160b0f070804020f010306083309100507090b1603030608030903071502030906 71
    0x944000881081c207070003e88503070b0041406480200b0100c000c0e0b58991101e40c051340c00c1c00f006001811031010031080000701c001003011003a00542c42030780100b600d41c4400449082c01400d01041d00c42c010003580c2d441e1f060006041061001d010704940c440d82020006841d498001c00900190009601c641c86010600c4144c1d0306019030b0340001d6004030034155020710860703101001a82c89000034480d030140198414001180154001081e80c0c1c107500e148186c42100707480b002641100d402c011044081415548a034404204e110f203021500458440d040d003d103031410f142c00406c602c000170030080c0a00d450079000703501c590003034001802508409003078450150241a424140341103402e220342c80000b072450016010070050442074000c2ca140d002174140300d8020704054019040c00341016041000c00100004d80001c18000b40007170b042906110038241016080050075102d86800a1182c1e4004104007001a6400501002114076101c1c08042d05150300100341e0550095040031070704a1000265a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 452223273 1250 452222023 452222033
    0xf0e011d0a080f070b09011e09050606270f0103051905341710091203020a0e0402220b03060f040b030a020607080c010c02030f120a09080a0201090308011a0306060f07050604 76
    0x2d00c0c4050810808c50301041040d8500c0d40a0722103911006e8926000640454154189420f0001050302202e02d91400341d0200000031f0f45600080303a02c00d0a200b60800140108641403000300c0311035017440700c4025041310680780c0b9074603220120b160070385c90308003404c0c5508001498801e107447e41c1e103107003081524665640f001d2a250502806840b9690103410110071001640784980c0d12500d4200340001d4005102c40f00507030081d4400c52100c000e03c000014840c25aa849000400d800001c040761211311450040202d48804002d4005940100b001e00400802da100c00f411050102021a0040f480042d04d401084c02e1619410b80a90400400607510042c4116040280702402c0071800030807940b00b141e4001c0b0f84a0041c030918006046e0300304182e041c1c1c89812034119800c20a0f48100203041c00031940e88040039403103004d4000140c4d465214071400c0c5038101c15001d0040c083da0f641d91500407841c950030756a0744030003055070380300e000046200d401d44420042560945ca030300404644550500c2d00f01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 452224523 1250 452223273 452223281
    0x71a09122803030501080106120b04050f061503060f0c0d02090a0504020703030605030d0e030c1e0a08011a010804050c0d0f0f110405150f1c060f0e011d0a080f070b0901 74
    0x141d01013802d02000164000d4144651000c070b9108240c0804540510f50b214940344901800503603070340c80342441045802000780700c01802910101942e9803c0c84814040c54240307a0002c045191002d000810850100103e40c11501400c000031b000682c0e41804200084109034150402e0f50001d202044403420150143e04c1402528003c80c21221443c08071a021595642020615a015003026041000310305150342080002c801c48088000c10f070900c05d010440044d2140c0c01900c0b1030303460b140e0b06a0107190306c40c152581d00e84207190940c1117241c6511450303960f07014000750718001d02c0041d24102c107100350203190a000a52150202028510724101644c4100f240110148103900e81340110ba240068030364200c0c01418040d101042e200303401d004201c110006013101040340494030003a01c001954034452681c3c03440d03d45000141030022407a0040c2118086400c5c5031b41409243c602d0f41c40030000280011086a029240d29620258480500c42074000c6060041c01003901340309020b034800341900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 452225773 1250 452224523 452224603
    0x40c021b1216171507090302060702060d02030403030b01030e1212071b0804030302070b09011b150207060f0605030a0804150c0c0e09060c03010b0a0e03190c0305071a0912 75
    0x1254a13140104444010390030f030a035000c6011600c261400c0005040c08000303094014001080ca6061019100c0200140da00450307080300025550b10107000d60390b81610411100c1c81c4000001e01d690602d079400147d0fa849184200c0e051101400e00042c0c806220b154406141100908080e0300d18a85282030030094010b400b04401501507114040383c01000b4400360740c4000b5059450710703483d03074bd241e410090b120380130901038622400c1c003442640e181c5028001010201d10030070b000aa0392008402d03030001c55110b604110710030b410080c070f1080800d8184082d42e003070742c50f00c185140c1d400b81c20031401d6801c101c0310030004240c2c0c1301e0b02200250f5040003003000c4d442020070405641d1242c3c2c40006501c0c81c0c1c402401a141130b440103000c500c001a110b0090b80c5c0d000d49000d001c440383d000160071003411000d150b61b000c03500c0c0020041309100f00202407100b80002c0c903030310b046d0203494851140074803071600448049500a041d41030000b41a40400c105c81443c840d0517070210100e2001201d440c64540300c01070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 452227023 1250 452225773 452225819
    0x70f0b04082109010e12010c11190503340305070b06030d12020f0d0212061f020601030308090c0405150a0f0308180d20040c021b1216 59
    0x10b50074080340314401c001084265488803010b25100422005442007940d5907080ea411020111400b2050202442200c015034207a45a071360321390280000c123510b01085d8012003030186c6480b155038400600004151510107185a40c19501e41e41201e002400540314402c40b01340d4a851440880305164101d0010803c050050340315845580e142c40500d035592901300c85840004484070000d44da25511030f405400120030b000c1e051454401e602a200c0c3c240d030054204d5040c10407144051244c1450000b00c407a40e103a29000c0307241101d030001107000e03440308030510020341408440000180c0e803d600340320414415000a10402981c18035460200c090300b11540024020088040e0101d0040d9820341040200c03079002c0039291400341003da07002c41e04800c046503182c0040081e40702d180042c5000b50400390b40d040e20f02407000c0c080364038002c00090710b001950403010354003c00749036400c030700e204110016400700c20348403a045800c07681440c80c54a500b0f21260318003d600400c3c04580d00c1a10850b10050640310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 452228273 1250 452227023 452227033
    0x12030207290f090709060306020a030e0607050412110310050103020f010e0a091505030a060906050f061309050c04180209011706162c0901080303100506030603070f0b0408 75
    0x1055501220803030004400e40059070500000b0314102018041c01e520058240a03290030307554454805050380d005400c221000b46d00030800340c44540d030520074451001320300c0d801040d881c103000c0e00c0a4000d1085009a152160720101c101007400100d80c1080750040303001c2c04561803030701084060030041100f030008030b100d8465802000c41030740c800c000308005250010600448180307000c3d0554001c240b0302240c0554101c0b0040e0010b60342d60288100c0c003200b8001c00c804204000d2514054040300c400400944a00254a0034403055899074200d4503507600480301e000402c0780035410075034a03002e060003d0300d03845414100001102c00c09040f4030062540300b44c40840099888050b48000395060b144144065030200b000641d0354203001310306920051550422032100e050078015009220040c2649156010160026032903038200a080e05005001800280d4150304041c04800b445540c188149841a2800700118003070b55002d000240052214211140a09540301603040340783e003082c410320300c00f4050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 452229523 1250 452228273 452228303
    0x8160302092b050703050609120a350c041409070f0807050f0f0a18030302060a0f0204080316031407020906100201021902011a0102150103030e0d12030207 68
    0x3402900c00c852001400c1040080300320341070128111000c0c61040a0311080110032000c15002d021070000755000d00c000c1c09052503d004024070b008072412250000310404c10200d41c8480d403241e625000010424034080741e035299508003c0071390024804498410a130001070240d100c1c0700d200140212807403407a01d080d5803c0c40c81d04000114504a0b000000308507000d0030008498803507500e035a0700030054241203042c00320281d5005c015030480716000b02154000a100c5002c60742000c3d000c8203468180c8043d45a050842d60002e44518001e002c0c03070ba1494461614040200e916010713a0050300707501003100c5e11ba0b50140102c140032041d8039020303404210f41441483c50088031008072858560040d0032071110341c03106401c1c40304001c0418050003c5541c213001a07501d1401e0340405030800e080700d5001154424040c0c001c510105860030415043d9400120341d1002041010384090440c0d4041c00c0c4141010104000f107442c00044502c000c000d43c0c000c4400318552901540a00012800341c9940452000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 452230773 1250 452229523 452229527
    0x10e0a0f0b070f0812010e010b190f021e06041703010b0412020d060c030b01080618150103020c07060203040303120605010806040504020613060e1305010509070c210816 74
    0x429406581038140160009004007500c15000380055403269061580b50301d5a030702d5918403038102400c014000c60300c4100400c1000c000300340301c0e4003400810070702619100d0030341c040b1024040304000712010312400054980c03201c2d0003031090300e821144e201c940002c2401e0040d005070315103a046404441035000e4200e081c12203030b86081500c0c107903141c6040c0a880c2a00344942d80710044480074049034010340140c40d80000490b02e0050100d00c40d425140425440c00d54400900611402806640140c004800701c0800c902c80020382c075002044000031920710010800128080c4c07007082850340191155090000e0320039030010080007224001d58480d1344006001034034809413a03c921030030340082c0b8880041540c40c906a4451500184018640c6107052000040a031241d41c0e180d1155010a80303152056009003400144e03220b00c404c1c520030401c0107604220029080581c0505018208013100c1b0f00c010070400e04d18070342c1d084081107034540c0541d484959001081a00300f260540040b50b10750684402e424 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 452232023 1250 452230773 452230789
    0xd0504090f0c0c06090204020714370308041b03030210060815010315090c0f0e061813050a2f0102010c050423090a0506030f0a020f0405090319030b010e 67
    0x24003d030340d44040010140c40b43d901800c5625000d987c016801c20220f4009005003072222811300c0501c000d804220001501d040d0480f510882c2e601a2071034180105c1015111088484816031b4076040c0fa0641e501d60341048034001058540c038910401c14180c000c01807540000d20003140c0c3c45522002d0002e0303611002c81c6520381403403c03081c1340324512200051001460b491000700150141d4103001661052940741c08003450040da010b408440c40400301407020b10000c00c0c0f0150310203000e03544280c010b0a880c84d44081c103900182442401101c120b140010000c00744000391a0381c0c2c11010222007402d2240115189580303146d02d511603240d004800001335401030143d2902d000b00e40c3c8401e802c141c517095842d460f022030599900291445441c0b0720030184d85000204c2d008016a2200080a1402c8003e0603d0b1103491a0407640300e601030b608e0a80165100034107180f02c00c10603500412640c84a905092940c000c0451408011b030581a8440855906600020180400360f84070300020000c0300034850a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 452233273 1250 452232023 452232041
    0x1305090a0902031e120d02130e0a0c050306100f0c0506041212050403090905060a0f0f06030b030f06070c1a0f060103050c09060d090507050a031109010501090e04030e0307080d0504090f 81
    0xd60003203940e58030031716520805898000c00c420009458143c011007a011046035507082190b000e24420300313110428241d07203e04442114141011455810310100003005074126404010400403540703851200c0c1c074411030800a00542c081c0855005013002d151411405c80d806c0d203904005400c00545198020080c018140100d0701500e0b81c541c141e0034208801c015140041c81c80d81c03c00c03020b40c4001119030390040c44e60020300d80f44501c0e47c1c2050810000505071662408150b00c2030f404155072010150700410010b40103069405c00d816104140c1c070344590440c5000c03ea10548519100c2000004040981c1c00c42c8a00c4003603070100519664000011083d004a1902c41d400c418180304c05240300d800759000301d49450060342190081d40c0c3d40d1307000a482503d2a0004c8420b0011040c00307040c64180301800340e02404090034550703181030030085040e4558500410113004c011107508501040c1c0c80034030460010f41070b0003040e1180c1c0c44c502d11703020f405a4820310440c0102032030915040241e80c418451b08a81c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 452234523 1250 452233273 452233333
    0xe33090402010305070e030313080c1504090506210a0317010807030f150e0a1e03141804060602010212130507180e0a0f050d08060a0b1305090a090203 66
    0x6503031500d030011002003000422040c203001d102c0301074102c0c5540070000391a440d102030a5240207941443c0e050360801c1c00b480141c501411419280c0c0d1440c02c9004240c6055030311090000039a542c52030300146804190402c0d11720403a510030841500c503c00400c0b11080d06d4029200c03410860148158165588403d2040d0001600f2040043c400a4224410340c00054002c61814485d54411641c441c201e0316150b440c00080e50200030084100300b00c0c12a200f5403441d1000010b031008940b0340300a0702c14611a00c1440d091040020004039001e0b403940e14003c4030202400400c8601e803507040290007948041070302c01d02d6204040c002650b010b40a82001c090551040c040c000342850700302428807c1d400941041d4995803500c02500743d12500700b200d0100d09014030840d004801c02e81c1401d03414407441e4a0ba1800708203041c420003c20b92134120a410450b420035860070303650b0345852110020049140c2000c0c3d4003030080c40500141500542250b030f140e90003142a542621090a00f80c0031440700161003a034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 452235773 1250 452234523 452234539
    0x150b040b07081b01051008120418142805010810050709231809071404020f1b060c07030e040507030b0d0b010602011107020f060a05040e33 61
    0x1080c840a100640401d911501d25a03081000700000d120750f41840705420b1150b0ba5417081000030348071121005400506062015000412040400b124648a18010051020301c6000c507152440104e0748944c4940c120100c0d02c1c21a820903c15182b400400d241d60002c0441c090250091490703602d20481d4101c41240b801090152f030b09440b000041c080040440d001d00105c2c45000541c00b103108030400c0032400c00420841210003900030020000100c1e03916003903882c480d40800890040014841c401e603900f2080100c001c01480b0006806441041410910f5000201c0d03020f00c0583c0404c0d200f442d40c3c40810558a546ea210619a1142d00840c00c0241c0082e0024541d4819410158040ba8014950389000304420483c64040b074a420300001d0111403c00f503c00041004690a1241095604005414900c0c0004a030002907111100310281e600c1107400142c41140503020300206c4005200c0d4411005542c03030a14411504030210780c82c0c0006016100b456018502031603545500c842000500c103170 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 452237023 1250 452235773 452235779
    0x1d100503150604080601090203041a150d0203010204090608030913020a090b0304020d0f050d080f10030b192a02060601080c0d0b03060c1b0d0f140d0906050109150b04 73
    0x780000d2441d030707a400800c104000710301c00d00244000381c041c0078000c6001d6900d0406281503c0780200c80414040684805030601c6141c1c011460b40c0303240380d0030854101c00017000500019009214640c8803101075454044005500e0b070011000d48881c00b81156180c00c4035402c0585901030f40b088860100000e0f401e0380051081140000145420a0000d041c0080704c0f0b20340c0da210030200034072040a90385a803103110095500c951150384103912900d60011135890741841d51001c644010507000041035240304c11b0014000e034840000c1a44800d0101d8814424a04c10781c0d074191b18040307840d201ca41400400fa8088440c2400001c070796025240680d0703120132956501c840007005410001d120381c286911103040300d425031b400f040351500884542001684d50004110200c100e04024000c003000381e0071103c01c4070040f40c2c01080c190760240030782c144507609520680351119103100350010300348103614082c81201403203281c0d406507060b2926080d003003050003180c540d54241d00c80180700d4401e00e080108424 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 452238273 1250 452237023 452237041
    0x6080706080a0b04020a03091e15020708071a010305060a020301060503062209060609180510020a021c0302040306050a0506100302130e130201020601150e01030b060d05071d100503 79
    0xd0340b000a40800140d03803060040003d040ea48400399110010751903200a00911074030308011000300940d0034004801005540d47c19112500c11002006030750b5011540c0760501c1440740482c0c07905a802110b8030b44600108011100804c02804156114071170030000030b0040b0301c01c3c400c4a0688255032111070540c1c0c0c4140400042c0d0321511020b6410510780c20144240115600800003e0361107a400401c0c400d04005004c421141c1d07a03001e4400900b0182c00d8000415400b05581f81550042c01340540e0700c00c5100400ea14204000002c08240d851445020b2400307a810350207401a0780c4100030070701054030b80c07461400a80d9003c2e5281d80c2e0200c0c02d02c0c800d0526034042d5004003801c04109203440c020b25500d1524a01c041c5d401c40700d40c21101d0084060b5011981d0501078240074183e40b503105101180340c400002c00005002c103245040c182c0d50340200401c0d0f07807442c090b2206040c00081c00e100034988a2402000740c0c2012044085503400c1031440645490102c3e82d400940700c090791004e00307540c0c0b45010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 452239523 1250 452238273 452238287
    0xf09061314100506120a1106070c0b0406050304060609091e05011d03070203120423010e0d060b01020d080c072a0608091b091602010e0607030b0a0906080706 69
    0x4101d8040c584221060101c8038280044a80b50142540025840c40d00c3c2c13091155071031080304a03003c542c201844644c0020045202840c0b01c010640b030b640e44400e00e030b19166040102507040300380d17450380218000400e160b02000a62060744121003d000c290341d00c0c111201620b03890200200500b4550501d0390303104581c0940120154040c1e0008500203034841070182d2903060707a2800c0a801c0e000096200c055090812070480d03504502c4140910f0030b0b01d010280216240c0101d00a620070190448494040c1e00c04e010350030f04c00748000d0480d11160b00a20300b9000070855207080c0e50250040190b070b08602c60040300c0280c80303a0358540b140c0d40f8101c651fa03607282009200c015251110305204c980c0c1020510402141b2024061a80b64210141403c68000381f42c101c1d050307178907400340210080d40c08140c0c4455005503008110a800d001200300602e2050740035050101d210000c500c1404100b02d042907040e04201c50342c0d0010748802036440d840c0e2441500b583c4489c01143d84651050b041001140c1c402c0c0c3d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 452240773 1250 452239523 452239561
    0x1b0605071509140f0601080c0a15020a12030203091603080315120303040506010602070e1005060d1e1b020f060136020a0906020a0507051c0209010b0409050f0906 71
    0x1600314510303580c3d01042266000e02d10704940c052050302020307001c104440350251013554000e05800d030020b0001000c42641e801001c508615000c05110054000c2080d188025800908210084020803004009403c110392503001c9114841460940750115000882903903081290149941e82e0b10700b4402103c0401c1149980180742c04c0088481c5210500c00380d4000c0c2c1c41500a008503514100d0300a242c820650042028902258144130350100e10410101c22100b06588040c1c80300d1045109000814860b03241c1d80140403d440c10030032200310381d48885000c0d0309000c4100041448501c0880e0340309104e01c5c884131503074071a50051201d140022950340d08030101381040d500c6281c0000d507490f1070030000c0e081003c14580104220055035049615032000e48903a00c01004040b0352902e03030741c0e6240c88900c07a80b0b0082c4050141444c0ca00078040c3c1d00288070ba0040c01500465a4546101c0040d500c00d2044103445844c1601103003c0020943c00a80076a054000030b119540344d013000145c10011000b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 452242023 1250 452240773 452240813
    0x30d4e290d061d150402041b0504150302042d080d1d060702130e0c100c030e0105041e0e0f040506070509180115080906090d03180b010e041b060507 65
    0x70b0b00f03034500584108100000c03d0b07100c0c464440c050404e403061100356134814448410071031005200e141c03090782c400c09840440d036000c4103061010300310a030198007c0c442c0380c1220070f0001d00e92308100c0300348843d1780700091041030310060100d400c2e5950038160b17140c40c4a0305010000039914a4500d840400c0c4441d49040908010242482e10f00b05034001640d90202e1070611040c1611441d481e84081410300000403091410388001c00d03074030311031000100501c1d03070310400400344040c00120801991140080d580030b443da40c0181c103604807481d40003075501c01310f44c41099003d803002000034000352003204905015607404001413595448051050740c41d0b40040c40d2032500b00c10740d5070401080ca059003000500030200100e1800481411000007008584001d0101c3d119611a80602069a20004280c12040750364a000525003000c400600c003042c600c04800352810072500300209023002d00404180c0198410f039010003030b100c441007410182e4546445034001041040c001c50000c50b1003581c130410018054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 452243273 1250 452242023 452242061
    0xa0801060b16080927010602010903081324060f0918410c0108070516030e04090b090624010c0602160302010b030d4e290d06 55
    0x1600400c3d0f807507801e05c80390307000c0c002c580061070b0038160b41a41507805800144002e0040c07004d60384016110300400303001d43c030a8841c81805203040c0039107007440d01407502d04443c5102c92000c100d4180009000030703016680c49071a10010002e03400c0010b10030780310b030308588814503510340740305449514030740d07459101d21086c06454441e00c00e224195145900080c160a001510082d806a00198a403c2801340040c1c184080003080c010181d4000041d40c01e074506081365094502040e01e8200e541c0688003032000d0300705003064003500030041c00032940303031150003004226801c03a6540c020700080508034203d48007002d24030900399031841d4800e811140740039010b110b002d8680341c40c0c0b01c40004040e44075001607005075592410031030203203000e001c03147c44000325103403407101e0304108147c00d500360281241d0049101007100e84111100c00c510015041015012a88500401411403510203000380080d0b44040100300070031258100003000443c810144050b00b404032000c2640d44240c000c0000d03809246c100307142 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 452244523 1250 452243273 452243287
    0x5030307201e16081609092102070305010f020901021612110604080d0e03061003051c031409010b0108071409010c0c05031015090203010308030408090d1a060a0801060b1608 76
    0x542c049000101504e2000b03250014000c0c1860701509015004104050705200c1c0d0319002c0f41880c2e0341d0510b1044451002000c4065403407007645069101d9000404550800245c0707210384003d540948150030081e0292610b0021042101c27401403154011182c0c880422407020303010516444517100c014078003074055031516880b039000d5868a90007290002c0050312008d5055050704090000e0794101e40c4030003040d965282107035102500c5003502c400042d1114401c6222003443c0c0c0c80b80e08982d048103500c0041031910f0810f008168060804000d03007030301081c1c41034041060b80b4415450190810160381c0400d0a0084180044910641d45031040d00c52907807481000c51923075024411a468006101c20004142c030020f008007508030a00e5100c045007510520040000c01d074400d0851360306c03680c40015035507140e0a0f8000525507803011640640507940781c050403404110810201e6000e4001160b410784010707a6803611a00741d9205000300c03503500e04188030100b004c2040c0b035a6141d43c10710411405040c082 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 452245773 1250 452244523 452244553
    0x2e02090a0f080105090c0102160b130f030b011703070f0b0403020c0915010206060d0b061003020c19051b100f0c06110703090b0a080615090d05030307201e 68
    0x80d0b0070160b00c0d43d640e04280003031a2010051000b000c01c0c2070004e4003081a04055000700d2040c14441c140302400005209001c040c41c140451002e050454000c600701a105c4c00c01c401e404d079090103480c500d48450705240c100035000000717943d1070641c0412086442070056407002d20020024108a00b540300303148004c00d0566990351054411000341441190150340c03e1300080c9000b03405407400c0e0040031025803090109103164002a0300600660b41c6000f00350614008030020b10800d80000c2440c0100310303000300d606160340b14072a01c0c40e000b03400300c1d003940804410300340b030041c0342c1034440e98031032103824400000380d00480e010002c8000340c0c10444083c0b541070701d40109907032030328255007000c000000e042000c0607001040c0c24040c00c1c44604050804545020245c55000003922842c400c01c064a00641460140002c5999514018004103181c240c0b074544690f41e90001e88108010480e00846690007441700d403254014042d13030748001c003c00001402074030b81c5004013415100700da00039101500c405217 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 452247023 1250 452245773 452245799
    0x18140f0d050a1b0b09100305220c05040b090f160c06021201030b090a0c0603180602160c0b0906030103060b040b03150601200a02040b041811032e02090a 67
    0xa0300503009400803038940210700154140c25003105103038907824412400c1c10f89945031b991429500760f040001e074507113450102d0042c180c014184440178120a000040402c480280e91900f1910107840074030a290310801040310703401c1d003224545000c140c401c00203440c11502c000348440300c0c0500d0600c80c0d0303404055100c1009076800892264801802400108100f11404490692104481e0060452001070383d40309101040e030361140104240d11000c04110394055400042c0c105075015408568030310224462480d45042d214054030741414144000034a065200704440c5141c800030803a0b40396a0866640000508180040da50442d6984100c984542c5081201c0003085001d03503d1001c1600e0010001403100f1100700101a0702da0360103100c1003d0700f00000d18440c120768116804245d1801030700100d00140b840642c450700d0000a09250414020340c40d0580f0700d440015415240203400328001101c07204a400d8412a04110a444915401c1d03d550301a06000f10002e28443c80e66542c0e00090f0401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 452248273 1250 452247023 452247043
    0xd0b0118030c030b07030b18040215041701050601031b080c0f0f071101020c0d02130e0d0e030114040b011802040914060414060f060706110304030201020a18140f0d05 73
    0x3208110b1043c002d1100d501c0c01a80d004005180501070f20790990007280c003101504008404802d0014042821565500d18400c0c544042000c502e48550ba07a100c0c03440201c0c10180315000ca03520f44404215035500c240070b01c1003694100c6010491000c005141110240c400410200318044c06010303036501a8551001000e00e0641307454091303120301e0141000848030340b01d0344425040d54030403d80300d03886803514924942c1c030680440b6a20325103034088103508046d1407400402c0010340038800710170074480e8110310ba421884000340c0080242d032807070ba843d0f43c0c0420710035107003c0c006400001c010485501c01c5040c031003940d04bc0041c00340c1010394400540c02681c070640c05d200f407540300c01801c00c940c2d820705208403155007a55202c031007030a050050104400300700c0707510032a0082c0b02c002840d005228a50300004110040b0101c00c0d980e07840d0a0800a000790048a81d140018401390402080710400c0100101030b2403141c009070745810354030410007400d80f10710038506c4e801c88008506207000c14001c0c0101815 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 452249523 1250 452248273 452248283
    0x20405030d0c020a090e07090c020312090f0c090405060a0914030f070b0a0902011205060a0e10080d08090c01050a0c0602070c080f0102041410020106080a080d060e04080d0b011803 79
    0x380d12240f04100e4410825085030600a140c4541d0b50043d420000d044021641c40880001e188102680c1c100d055101c1d01f107013100c0c00e1081c03409202c4000c03000a02403680500e04020b4030908681c1a040000300d5605079030140c01d0303900100210b200051150f01400c0503a109a03508051081e0b00c1c000c40d419500844481740e810307503000c241e500038000280c6059178410316009040003000125400a00051740c40d0304040d1500390b85100040182d20303680a00c0c8050141d1a070100300c1e07454103840e80002c21482d0700410407103004620509410a02502c2002d0240c090381c2e0181c009481c0f100700444080d00101409020058008850070200f040703032000f800540c2c0108a0108014105400b2614051102502c00d1181e0700c1000204400d40220070201c15260b0100c8a07010b1a00b10500124050400e541009540f0f0080030444000c218030388000f44501c0c11000d84c2442801d50300c11101030b90050441d000341c52240c00f01300c3d540e074105503035001c0c22011005052141c4d5407406094a42c6501c05140c0048030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 452250773 1250 452249523 452249537
    0xc230a0305060f0a02070201020616051e030a181703101a03060102010b0a120b100305190c050103050105010c080a091e0806010807030c120305070501110405100e1012020405030d 78
    0x1c2d10740303805145640c4800c001000317502d06141580000d580c0e10300103040302040c0000c03038010325042d445a0110303a500ca00c21000d0704000d0340d100740707100d401d0f600545403845994a003408104a48010881c00210039420080d880e41102200402400d039a20080c420024041c6074000490b81580800d03c9402024800d03400315201e250000019003107840c00030300d05110392012030040200d1070094100c464101e6000c085e940c1d03a44c8030803401c15000443e68000801500984440103c811100c02d00b180c6480c1c09070b10903482b0644c1e0f41c0019012107a081c01401d000030044441d40e4003045002c4001d00c0001c05518211a0707041d81c5a6000d1404407000390302950b10b40c5203180030041f0020030800c65001d0481c1c0ca002c0c1000a1440e626840d0000803842035110f803c100000020525000d0303010ba807400380e00140240490300400000a09590190142511440580840c0341e52a0300c0340340784108640c0050304460b0f4011041100380c0e464840b8815804942d6000c00c804980d98506100c03128a0100c1c40d10b4035a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 452252023 1250 452250773 452250781
    0x1110091508040c090b1801080a0b1308030109050c130303020304090c110a031407080307050304021206070f050331051509031611040504111201090c230a030506 70
    0x41140c04045010030811074408140000b02d950303002010100c0f070604c600095084401c20108580c0300300e1011039038048041c01e000013003c1d10040b41c03040c442e51242c072540c91107580f4a00c4086600e03a000034050400303103080c401400001c5041e84003075040b9500000d4076007043c45500210030484001d070003c60058001240c104420501c600a804900792a82008104862140300e200d503524000e03440601002600400380e1803a81c1c0101c11a0380954000714500c1d9681f9000768064100d500c00d8801320b0294040715800702c3c03140b0012403d94014941590f0791030841e4481c60044820b0341019003114030410b55243c0c101014a0280d01305400c09070038455447e01d0040c0c17424040d00346800c203141c3d180f091682e50700f0061a44004003c1301c0303000b46040103074085619241440218030360380000003500685088244424003061080143c1c00880495841c5061140f0201c86400c3c0c61080300e000b807030300f584440305014924010211924050b01c248030248022401400600c0090040d03009540c3c0b500401b080c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 452253273 1250 452252023 452252039
    0x20d0606080618060f011e020706021b2805130e0106140a06030e07090906021b030906041404021608070b0702190303021b070b040f0e0c16111009 64
    0x850b0320075000c650001c400305070324142d261140401041c4600c15a1403160f281034a031f01030740740c61800c0403c0c0013000030142401d0f0800b968a80d4203014040262141c0203c1c441c0741e00c1b00715260031a03030401405020000491242100c0341111501c161900c0c8294044042a1a19040c1400e40e2035001d0140209448961500107403c480c0036420040d452000e4581c0060b290301c8030211403013246c07a030780b80008080d00182403190616500350043d00f00203040156400902c00c460700980320034168815001400701c2e50400f103d960b03114a42c0240e41150081c80108848452035282e44020784015201514000005a4403042442600011500450003151810038004291441c561001143c0024562040410804400030780b00310001000c15400058900e04002c14606070101800c1440c12500343e55211b1032455566041070017078400c0c00b024518001802900104118000c032a100c20540c580740b100607420700d805010410685000c1234a550805a40d02d4900c11041d000701c0c2542c0b05a040781c100035213 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 452254523 1250 452253273 452253287
    0x9080d051503010507121401080a08132102210606041e05100f06080114040c0201090506090f1504200a03170405130207020306160e06040b0a180f12020a0801020d0606 73
    0x154164461f50040180300110000814043e02d607040042992101c401d0680c542a0b090a500840c1104002c82c11034441c07034264005a150551089404481900100c8002c13400c0c100411030b0010a42d0100000c1421030078240d0042c60b100809056110042d6003007030000007583c0d401e44600c1d9441a0206c02000314448a00070040908041c0c6403009207945001c81c61916131100751202e9100b55070b2041c0342000384c0e000354807255000d81d111041d07450790b01d089102c1613201c44001ca10607110f07009090000103c0e10055505903c034a601a110003110b540c100281700300d14080220098005040101c0800466001c0032020b111035174509010784d4907400c18080c0982c10b80c030020500a80b0b40140100b00c0165008908554402520700c5a00500b0200703580407200101450f13001c0350401c4001501049040302030303004218006061310340300070100c2e0111844926055510800400207035030034040c0304c403040450383c9891483c00205102d00041c0c44c0c0301d8240c2264000417140c1c0085640d08402c02c0750f1508800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 452255773 1250 452254523 452254541
    0x3e07080c0f0d12031d190b0105120303133f0c0816210905030c0303040e040b0c0409020a0201050907140f090a09050d080f0a09080d05150301050712 65
    0x603448244105a591040d0f040541001d000a054440d61011100b0340507400006858011101311174210b8000c036196402585c0c40441903a443c00c48000119860401c0151001c20a241d140258a140e44200c01240c507403c9000c070881d44852015070161052400c8400c04241050010016007104442a06c8105014103100c600f82403049a0081c000403507068408d40b403165504882c05002c040640c0b8001c01c3c2c034640700004220023400b0100000000b43e001d80b886013520350075801c44001d0400d0744c007059540d0180b8412100b4458601002070001503150007002d4110b003072110000e06107a1110745000c2070360080d90210006070b40da0f00401080d200e040025070003d0404103030f00c0d203011030007074041560b0380750000f0301c40c0c064505c0300c0c0810300703111240c0c1c02002c004c0d4000e015943c510351545002031a844096400c0b02010b680e12010039100380c8948908080301d5888a00349140800f0007405d11b01400000300500d124150001c840381154030b0070302595120b880e442e591242d182440302d040100b21a039900c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 452257023 1250 452255773 452255779
    0xc05040801051e130201030b040c05070605090307230703171801091505090a17011b0314070c11030a060b012312060a0909030302193e07080c0f 63
    0x30001c03030352091080c0c1100342c2100051385800b013150100d000507405030148400d0590068030b40000c8031710940c1d214010308644c0b48600700078440c944907070034103507a00c1c0281c00c0042c00d4040da20942c41807040803049000301001c906020380f24455503c2e1a501806a0000c24804a1120020304070700c20240320407120005447c2406e0035101d040c100a894000740d400e080c00e1070300340314001814480507644c002d0084000c200d114410060340b41d5656182c0d01910342c86900c109105413221510400e01d020b801058000301c503451a000260741c40c11001c84901074400390035079540c040e62140740c01a40b42488040a00da0042c1c070b02241c0f04240c4000105001c0750704081c540440c19a002031581e864004080f25000041401d461943c0e44946000800d40d07040340d841200d00c14980b040c424201032305038000e0034400700c0c80c513522000d40c80e821900307a5a4000c04000700c0000300c0505110003168280714040f41408103e404841032800c56034034990700e8820b5036003214216034480c40c01301103149004401d200401e0015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 452258273 1250 452257023 452257051
    0x40b180108033a020309010605191d150907031d0a05060603030a080408030a021902071404091208071e0809070f1503020702030c04060b0d060f05010504030602090609040c0504080105 80
    0x100407141c3c49225606002c03401c4540010216250400075001070014110040042d111480d200c048441e0040c000d2040250a0320500450b200640706a40030a104210750f403545070703903a00b54200700302001d04001c01410505607262224201800c8000391303442c1c41210703440181500c1025090040c41c1c1800100160f203c3c1d0310401611800550010449400503030085039903490741c4400000101030f0195070110949024909400d0b9011640052404100c034a011902d0f40104019000c1c0000d03207442d40d0001e0599943c55104010031391040b554a54010060702e460340e200a032044840d1171240c85001404000345800081c030515038420b01c56007004100c050f40d0303142450301e40143c41c080c0076409402d010501d031340401c0460542d02d080c0843d500c41c24000f007082022a403103112001070350b048201d001600f07500c0d203400800c000018204d1841500e0058460905140c40c540d10b03417010b540701d8440341d5080340d01070000c8101c03610740d8016040105130340d80b5960344903420b0003203040c2140c100501d100c444842d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 452259523 1250 452258273 452258347
    0x4261b100503060f180106030e0a030f0e01200109030e0303190815130e0f0a05030d18080408010b1c02010903110d150c02070e0408030105040b18010803 67
    0x380c440041192065400c105459584100028583c42842d83c0c00b01d41040020140300403600d2080801030507500140c03000c1014000390348506560b0169410000c0216014501e80c02c07a6501684815181d510145003200d510a07084001400c0141c114151000c180c3d150441742d000c00d60000c0c01c22040030000d03030045081440c8151070400040c0040c50510074000c0c820042100c03110782589805240700050310300f4a103003400c00004001462003503c05411409072545d101d03103800001c58402c1c0c001c1d4000b0001e40c18107003101e242c40d0040000101161500d072903000c1203000a801880680700418101c03000003044a8584180580a0841484d554000101900010041c2e07004580003081e20b070800c214200c202040b402040005403142d030046d14100c02c00314060001c00c800c2d0001d00c20840f0320f42c2038034201941e0b10300c1415a610b00341d90051223444c09100501c40b50a00b640404e5542400078055484109015540700d1100004c0e00011200e4000085120310f15500d545400c807500c0d86c0500750992150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 452260773 1250 452259523 452259529
    0x5040809040c02030705060f10080d091505070510051b040308030106050904021606061a040e1302030a0b0a0c140a082811030604140613090804261b 65
    0x2180142440c401c99507001007040c1d01d8401c0068403c01c0f80e000040b5020340c140400d01484070002290b1030364412152a90200d80d200c0b021800c1142c4003541e443d0307800c400c0d0901c142020403083c00d0300351508108003031000c00d01188007002a014102415200002c4a041607a103c58850080340345903014003208200400004140f00c0440b81140c0c506c2c64a144c03105e440e81d00250107845510324810010740d5004800081c0601903200301c084031070003160745080c0384051081e00c1c000e00a81c4904c05607002c52100042c00390700c0d580c2c20b0111045c0b00074107444183d08a40e03a0794040001c2660400070281c1d88100440040e40c102000c80d00318840c5080041c18141607400c000c25100e4014035807240c001e035000c0246030311001e52204861280000e9001c3c4440d2000c03000c0700521b0740007120101e1155007040703034605000b00d1191003035010390800b40201c2c0c1c00c045a030f42d54001411204000312419107041000003050043c41d2400c110a40e4044490869402c500203003602c1c041d80e00d030b001e5900301006629858681c0d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 452262023 1250 452260773 452260777
    0x11270904050718060909210e1c0f020607050313060c0f110a0305030a0c0203120306011407080d0204091e0e0c2107030b0402130506010206040303110903070b0a0f03050408 75
    0x1a601440c40d03203d118481e40d4000290600354000b1030b0103410000340f102000281e410300e034501714101d1900300407200c411a0845281c00085652030300442030003c0e200c509058200d80303008680c000c5500100c41e0707005601013000c83d0f200078000e8520f83c2010442d4000301c0141c0038035a00070456450b217442c1d40c20894464170031b2a0a04e08004003a0700b07188080e000240c4a64489c00300031038002007980c0c0c550140c10350152040a221070124400e000e02c0d01d00c0308150000c0700c1541e010703180680d2555884106883c40e6801640185400d40349a0410b00c40001d00c0c00541c00244042d00d148480401d000510848200103403004580030b51000341491100041590300140038400705900711559841003400f40ca21151518199140341c2c281d0281c00000b1046c05182c0c00000d0003107109640441c4400c5403900c44c0300c00c840058070841d005800a50215000c41e2198001080881c0210b00013454400c0803800680303084483c1e40030300c1c09500c001c030b09110680d0b04402e03481c0f29107110703050900452a065136609124 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 452263273 1250 452262023 452262029
    0x101103191e020d050c010b12160b04030f0201081803030103031d041b050d0612050c011115010501080705090d030906140a020303130602040e040b15100819112709040507 74
    0x240108201700281c20035040740f030340d03404091300010300703400142c9500d078442d0b44280300354819006103807002503c6501607040f14210703a0000300c1c05001240d16401100e02d1500504110003403621130003d540a07507018802036008500c29210612002c1c0c1c40e8800951140403c14001d104529114886c04003d06420407550f2000c1c0074503185580d144c000c0c68030030080c00513400c8031040303011590701e0301c00b0800d0010b400110a90700742c944064044910800315074803582c05054190510359038004010300e5008070a02c1d600700304282042da050000010109003007080b8910298005000ea800400206800011000608041c0702040d85400d4011001035541e1001415981b0001078885600080c8542d90f81640c01a0811031254081800d050030301c808107030401c3d02c1503a030a0041c10b200514500e405c202c2c000c07441d02c4036202e410243c0d4910600d0b14000e45101100e520396521614000040802d4500070030860701d82e052075a01030242404030b0000190f8821400b0b00400000003800040f8500080820407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 452264523 1250 452263273 452263277
    0x306090b0913020a1a18040204150f032007030e100c02010e030a12020d11031c0e0c0301020a020114010e010e0112030905030d170f0411101103191e020d 67
    0x4110114408a80c0c02c10a55128000401c818505d60410100400041c18010569008500d8024005041208910480c40741d841c4140202105201c000c1c002d2121003003071602ea080c000364142c0c5040a01c4260030704a00040b0700d00d01c0c001003c00070990081c010054924050303842e541101c60f0500301400864103c3e90281c14040d00b00521410340d5820000031300c89591101074140b980b070441101940d81c911a000d40000315040c120071540b401c1c1c0000c103442d0182c0040031440c1a0507042403504d8010700c43c199030039120b80150319000109840900041c0100c080750340c00000c2c807a100304a08049480182c01c40c00c08001d10400411050399064481415a84101c40c081010306c140e01d0140c1d4145a41e60020307806000c0d8440e40c13a03100e40c02c284000c4103040b58401801e0159510310403c040080c00700d074014a0510084c0451005080001c155450780899003001445140303c0c5d1226807654102e2216648102c1e9548114912580d108451502056070404002c800725810b00c2c0280d10369058640340d4007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 452265773 1250 452264523 452264551
    0x1e012d060906031514041e09050c030d03090b0a0504050a050d050d0f050c03010905130c0612111218280c060503070507110d02060703092117210c0306010306090b09 72
    0x4000e581f0041c0741d40034500070003002070318005d181007916006010540d5200c2e0041008a0002500074090100d0090b40b198585500c0c2e514a2404002000080c0056506115025640c40068420001a8100001512201d03203030282c0d2030300c1009642c8143c6032050301609181c1800f98100d0a0300540e03040da40b2480c00481d05a40d02c0c6020181035510300c402074111b02d040ca80018265030000d841070034805003640107001032078241c1c501e43c88034460700398291049000d00300050145000f05550a00030410038080d2844001c9201d5102d0456000348641020402030440c41c40070002e0030078901c2c0040078a17090041c21480c2040700a4994050b039100607000b101301181c803044640e20f42d54010b00199000b894a034a600042c280281072411034014840384d44086200060024014a0840320b05035101c25001d0f06000001d000d40e0080d04911401d40c2c00c038013403003600380704114103403002c0e482008a140c0590f12232404400060035254240c0c0010032103450300901c100c0d07640b60345085c19405544505815 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 452267023 1250 452265773 452265791
    0x1501030f1b0b07060c05090f01120e0d09090e0601050117150a09020a0801050f0a0303030905010e010612030e0a140d03090512030d051e012d06090603151404 69
    0x155403440d59129001407a10291001c42d0300780003003010f469100c4c080c1c00c04010b5400300c0102500d05100d0340c1409030380a840101c04c007110398803550307404c0c00c4c009103048080381080d44d10400c10b240030481c5418030049401e11340e041c004003a90b445400f400585020003461154501000601601100a0203141011414002a02411100150b40c024010180070664103603a602240402508903020a800007107130340c40001400c1c40e040314690321120004007003041c598507564041d0000c2014180840315035494800d02400c2040a104107002418682d010b2a101605807800070b0560180428651040306500e409001012040c440b0b516240b50984945010901509013520081501d070b2219074002118111181400c201102400301c0c000689010310880d200c403201043c688060362200305140301500d004210100d44a160049601207107184580c0c1d400100300c07048400c0d10309411210116208a508116450b40340c851460034020400311340e0b034003d040c085558203d0b1030030858140302e1074032506c080f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 452268273 1250 452267023 452267033
    0x909090c06030f07110a0b0703020c0705030105090a021302040b27040c050d110405030a020d14060a06060909020705121804020d090b07080705120c1204060f0b031501030f 75
    0x60300051500411494892411114041c14200c089030444000b540e50f10780c3c44540d10780000e0100c6e4084e03000901032600d03514400e04070000d4000d404002d140f03104d25800018291428071510380512200000750100c10680e005101f0600c1042142c0071886104020811021102c03105507503c1d0106a0103803521281455190818101d084543d2903020f0714110f0002c02c401d400c40002c005203420b14006000030700d900030b00d500b41801544982c94061b044040228014500b8510754002144079440a00d16038484074540761420808854800450303a441005010346504504a200240900034083d0700d084002d0b13541d03a443d01ca424204001c1c14001040c3e000401300202c851024842e0003500c11901c40101080d59405008010819101042c400001c03c9181d8801c4000501ca05d540ea10781c5860586002c00d440c1c40306c035008103003101880e4103020282045a00003500e6001701e008410102d8208111500d0a040364050030344148a0341c0405400c0c0c0c000407001c8010350440380c1191680c0d9100c00c45040c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 452269523 1250 452268273 452268283
    0x11040806010303230307030b01110a050601030b2206020c100c0c0303090321020d0f0b0d08030c0f0c01020d240608270307050c0126130c0602010c021c05090909 70
    0x408002c44c1c4000c020070402a91592282d0100c0000340d84464841c0c06640170355441d1407100d50094815000140188080307403030001ba013074110300d00c540f81000c1494241450820580000c20407140646c00044525403504200a803c0c900403c805080041d00120b020141650541d0301d801010305895020410502d8010204c5800c1b169061484803401810002408025072150f81071035000340ca046030f280d911140718860451070141c09003d8882c410b020f5100c0c0c02d02074000400d41015090108054410700d200321700a400c2550300c03400003684a036582e1169109942d426200d50714940803d980300603207030030040b1a400c200c60845c10040103d441c1d15640c0e1a50301401c10170030303001804e40404c0089c0c410000005003036860103030082c0c0d90a000703a08011070350940c084541a811010b00b0b6068600b940000c02c0581d08204640c1c0c107413801c0300040c3d450000810665001c100541d5441e096041a2a014490303c515070b0b011615140c807000403880b004d4950300400000500a03a100c10000d80d03d00c0d000c01c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 452270773 1250 452269523 452269577
    0xd0b0102070807080d120b0f19120b0906090a0201020309010c03020106170706020f07080c01050a0c02090a0501051e131d0102040b040906080a0f02151b010501050411040806010303 79
    0x416105120340307075003103031782d031198841c103c000091460344000c0341c00c0a00d442140080b940051441c1c100c5050841041111403011030342c03500c205440c070400250360030300150118400344aa201141c8625061015a0900340002c000207401e8000600d2580140c1e804412203d04030400d0815200140490908034010031494120000007840444180e402031400107015084a0750380d8225501c0c0301c0003075580740d1101d419100d50b10f040c1c0c1c404a582d03541c960050000d805020b4040c54405490b0082d0303000a1032010050703c06941c0c0b00c1d944c40050002e800c010a8034008030041a9589084d116400041814000b22019042c0c3e05543c1d403900001c0003008004205440c10751000a648403500c52079078010030f5009120741030300245000d0002801400102e0270b242201d40107803a090808105401b40480810302c4040700e481101e00300002d800d10450350b05460304c803040341d2000141941c12719003030000300d542801d030702c114042d0244410441290700040c940d041d01d906140c4090409070f400041c016243c0902 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 452272023 1250 452270773 452270789
    0x5030105090f1e06011511010c0f0e0f1c0f0807060606030b0d080337090b010501030605060d0b010c140105070e0a300606081506030105010b0d0b010207 67
    0x2005000c52030100080da040c0c440034503000c0d1a41c66052000505000390348011035070044d00158010094507610344401c2403514410704021021031013064010f400c4500500e03492022405046003002d07507690120344100440d806a9507410441da1400000d40c500001071056040ca2443c0c4c2c000808000b907034842203540c690b02c5840d2581f00c25051402c0409000d4071b001d1600043e10f42500b00e00d0502c2d090703071060ba0240c1c002030540e00d141c440c801c02d240b00000c81c100b411224095071800101c81d880e04000da14041d05400b4001440c80ba252611040880040c2e020318101401d0003020b0149684110884080c54403100001406103006001611482009007001c2c01010441c042d800b110141900310342d11403040d0399101c80d048040e80381040074281c51405421100100100030900d0802c40b1041e8038074251019140c0c142801031030303817058142c403e01e800103030780c035004610545410342d18011002d80150084000b40310741d43c18403000301c080d801140380240315682c49040c0020710381d00a21809010b04851 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 452273273 1250 452272023 452272031
    0x2104030f1a010b0c10140601050705160f14060a051c0609090f0b070212090f0303040b030109060f0605070b06041805010501063b010834090503160b0f04050301 70
    0x14046405158100305002d14190144002d840c100380c2c003900c074208503000ca0208050070340d00c44900458052b0003200003200c1510480d03081d4a002084140c0220050464011404080707041c442c0300e24401e0103520f4628080e0b4001e015882c4419040002d64000342c052001c442c0003103040384007106c0907280036400f60209620f85070018080c00f81d0002404c040601402510001d6100c010080fa038034a401c002800006806106030140c41c905440503495029000b412a82499190200521680d0003030b4001c3d582140e490340c0400901d64140300070300080103c2d04100707041074825115500c0781d190003070000748216079030320b6807a103105240e4100100d803d80200c000c019668480b030003e0300d001c41d446094450000e6502c1d003a4070842c2c000350006408040c40180300540850000151141c81015104103182d441c50001030f800d000c00005a51850865080b00c10b074504c40310034001d40381d65042c1e008075010380c010380c4445505440100d10002211404250259649945800c00f2058000e40c0c0001d81d2550030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 452274523 1250 452273273 452273279
    0x21203090106030b010b0a0c080904021c06060f050c030301062a0609020f040603080912120a0c0b060604060806090402040e01090308010e01080c010f030c0905150a022104030f1a01 79
    0x540c010815a8418129054940d0700d0746d446000364040c240280b800900441c2c06000020300349000342040c030401500150800e44143c00c030103860400f18101c44c4115a03510070811030603621000d61512030b1940d0406900c2c01007080c10554813440140107000900503165000300d0010503001500014038280f15844140500b5807404001034070701728106a200e0b05080813081d2003031405100301000c6a0780710301c2003890104040c0a10015141101103e85140200ca00c0c60000524410042c910000e182e961010a40003616044480c0e190142829000d80801d020038403107540c2200d88160409000c03101e103505035a035880028040d101c8100814210350802d51400d042640011800e4142c502d0903c1c1e103480342c0e8841211a580e441030296080c000b070311420b0010141c3d4020350194882d03034060701e003a040964681010600f050020b001a030441d41c3c0004040c10070641c140a41070003203100500d038a5611a81b41e91240c400d003c2c501011740b117244038000c10800c118160004102c1d40c002c007054100e5a6035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 452275773 1250 452274523 452274541
    0x4080a120e09282f070819090b07082203060c1206080c010503190902041104090b0d120f030f0507031d03030402061b03070f150e06010b0301050907021203 68
    0x340c1010743c01c510510240c00081e032184180242030002540c2d000e900f00c1040c0c041030a02c9030005907548421100e00c00c100c0c810104445a00405084054203100310080146502c01051029a82d1080c06a16005d2100c0c4001540410880b610002200905050402458507403502c00300f003980028012072404e90032414a81e04901010213001110904020307555454034001c1c2c9511000e074036540051400c01c002140b0550340c0c0038200c00e1000032100002e40340d42d00e078041412500000400e650002d004038040003003000b1070003080c00c40c06003900c5150904d40b86aa500d07400440001640d0b0074040016554007159120713511000940c5001071041c0403d0500c0d510240080c038040d40411083c1d188100b450a03c80750010440f4000d48d03015201900d0b014003400c0d02340001c2140c4000a03064041080128045034208a01c1680d4501911144001e1941044504222003044090580c0c68100704010018800c0400c2641d0440b141560350f9001640c6200049003004409100400100004028001898 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 452277023 1250 452275773 452275801
    0x1051c0221060f01140a03180c0e0a0c030b1e15070b01060e0d08040e0a020c0d03150f0b030c03060d05071712030906240a03030e090c04080a120e09 65
    0x403600f600c00c90000c0400b00700450310745d20b00c0b00340140c00000c1042600075280c82035102c02d0341c0d18103440110100049558440c46e10f40c80c164083d070f40c0c00030302c2c600307000e480c40c110300c1858095186802c0c03c10942c00e06201082d800c000114090b10000041c00c05c404075a125030740746610201e40510586e5541005217000080310b170303003800b41c030700000d0a10b01d41080608280000e0343d240f5401c0342e000c3e0f0910b480c2610081013000000c00300103496800b44083c00809100b0025600305031425100841c0066020f1244011032020350700903401d100c1d40035401c001036002141140d800c80a2a070315140e90b80d942c0c0c40484c8203080070000080c15849119400291900800701034403000c013071201600d41d020251440b50002c1d020985011590743c2001b008203540b9003501c1c4412404648140c240e100903c00307400058142d2401e03074025004a040e05800030102d1800700d08043d0312030354810078035081c2804c24a40750341d910886140140300031815005070603001c0c0901d102641e4003400805501c107502d001400c0390709407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 452278273 1250 452277023 452277031
    0xb03011805070203251406190902180c0a020d0e0a09230f01060210050f0610030e01110c07091b050c0c06070827032d0102030c121501051c0221 63
    0x4500164041d4680010110b9440d000d400908d0740b0409041c1d0300b8200c01c00901039103030120703484003042019004452a0702e9034140326000805c0040e4075003541c11401780c10040460710480401500c0729410826030b55194030501a2001140006048002203c60b1011030022002c1910b8164441c0c04214030f84000040b41410380b1590f80c01c0e10038102c00103c5050588900b40c03403030140250400001045401d01380c001c6050f0312950b26003c00d5107a04002000c3c01c6651007103075100180e60001d4040510b0074204096002070a500008010490030b24880312180c00300640300350100100015802c480300c400b00021400d0030b400528660784c45001c2d00d4400f4459004a0100602c50b5161b1882c901084115201180d45080540034200184104880308001088800c00b0280124400401d58004100744040c2d840f07882d4003100c1760350b614040c02036891003900007170001088881462541e081d913641310068803508040c880040c6407442130307141c44070068040e2080f19004001c4003071040c00320040504081e401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 452279523 1250 452278273 452278283
    0x306070f0203220f090905030414041d0d1112030c0901120c0c110d0c170109050a3e0f06040e2707080a0809030703020306070f03060b0301180507020325 67
    0x1340399a8040342d01520025280509070f5002400100807081d14410b421000c1d050003023000071082c00c0d0511318050004240c0b2030020a600200003800550380105080c0810b5501d003000b06080950030040707030842e00c001000c1402c0140045041130f13143c2d0160070640140510340c8024002d4800302e000040210000031800c0d14090281441d094850904030513601e5001c2e0007800255403c1e040c158002090580000d084c01150740e501c03003c0001c14402d00912000030301c1081d058400d0504000988200d0701442c40c60407681c90040c084800f009404407041d951044140c1d607604c2e00c00c0f07105000034994010341e48045290001541006010242000207408007542c05445510243e2500707841d0703a84440500031a44c8603400f9087c02000318141402620009500404550049440e036022908003001500c21101040c5401c20314a038081c0c040c01204060b01e8000e14035415985094440c816202075200e201444c05c0da5540403a02e8184240100c03004044585028801c07102100101c6000d810703040c4090718 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 452280773 1250 452279523 452279549
    0x61e0307140403030c03140405030708010509010c09060906080c1b0a0201020d0207050a0614090409120806010215010504230112020108010f123503040614060306070f020322 76
    0x407501001a6025a0340540c0c0d082c440000030341c2c042e1090940c1030503d0f503800c80700380030000785540c007000680d02a008040001c035541c1490005030342900c42a1110380140150908103006c16039100000508903483c41c0303003c0641ea00c0d4103001c0c0c0310328414600051400c44022036494a801c6002072620000c074801ea00f220122042c1d070004070703203440042c020240c0c8103c072032008201c51441641c45414175102c05082a24004aa40c00201154071400c0c089275200d5080f105038080c00e03001201103500000030b001416103018100030004114905000729442395541b280e40c0140c80c07410f000c010070104e40159603054036585031150209040c82c4841e0403070001c2c00b840c00200d042c05802c602c2004680304007140460b020001d0391500e04041d402c1e481900c9403c0b411885074480e42240b440501042c4548100a5aa00342428400e05680c08490032401c4418904140a02034070b0000d4060790107440c52500c443e00b03030718000040381144141e44015a100d0070010381400c440c6900c801c0b400444500b040c282d9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 452282023 1250 452280773 452280797
    0xf171305150103051c03060b12060a08010506060301090c05070c14040f1803032301030b0a0e030a0f05032a030703150609030809010e0405041b080c031b061e0307 71
    0x66044009000040a44e0031040016030985d03201d52246181100d2400c0100710b007521001e098845030481030748502080340701801e004d21800c3c1400c05d0b00280c001c0c2e0000380203070314100020980c17511040c42007402541d981c2c868030092501c80e10940e2032995020349103900c5c035030340c0300340041c0800c2c801e0340c070f16100324034141c0c0b808903040c035030311645070303070384084090303007400c0005500d0035001816021824102402d1100441d0100900700c10180c0c042c40c818400750009041c02d064803412201c400b031102105038000c2200c4034003a90828003050081c4001c1c80c0c0140e89645801d411001e2103000100e002c0b07000c1c2c003418a840c0d5040e0400145110b02070703a5900300602c005150010342c1042d018410382e004203102a90510210b000900140305003881070402c0e841181e60000444c0c201c5200716001c3c4c4907030140040d5100d98180d4070041030300411164000342068091f00000a4941940c110030390500701f40000d020202da11104140c7d0402a07a1401382084900c00c4030030303490241c1c01121501d00103540e2104c42 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 452283273 1250 452282023 452282053
    0x16060b010c0f1401021c0213060c08070b09070b0706020306031c05070813270f0507140c0a020303070309140a0b0318010906020f0a09051f0f171305 65
    0x52a41640c114a0514002e51a81c58955500704031140b541c0b0035540070002407007003410180c0d8251580341203640040c2d50b940384000312040039119402c10000c010640c000000450120b0041d2032203c0e4008107805456120b414065103040c0140e8440d5030309801c0403840710700780300160b40514490041078050300c3e00f08070301c54160207035294000c04110124106100181c08201507001900390700d1800b80000e000180c80d108106511b080303c224200191250380748040c402040c0b4041c45800c00345180050007142070042c03014107038001550700807001d80301c01300380c04409840070802d141e1410340140540e0340d0b500e52030400500030800c0c0e00071140030601740007061005040102c02a801c03034038081c407400d0039607c0d010700a8410749400d03034100709107640301c1c0c0f41180811886d2000b001e88107021203000d6503441d40d6541c09400d01c3c016910035840381c1108180045017800034001303034420310042e00c0c02d220b18039007464068503020030307412941034040e0108040121100c8000501903029009000b00d43c20601c2c00210 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 452284523 1250 452283273 452283287
    0x1e1517030403030f080414070b0307110c0105040b090103060506070b16050a020c0607020d02031c02011a0609090910060f060905060c0706111203150907090e130f02030316060b01 78
    0xc010001401300340c0724900d04d031286407a1600144a202030103d6540c1007a003141c90181d20741c000081d80c1c80c000050001581d082022008508031b0761001c0c0801c2201840041c007140070358030604400c5280001c1034681b0360302c2503102e90094540100000e480b055507081c51803006408a85000e14040740000c080010340c0207070300342c2c0d15907807031580103103000183c00080c084250003410307040745c120b4928000c890041e5002d20058050030440d0700d004190441441c4001c4c02c0d514045020700c031702e1100f002c1480d50742d229030040710710090041c0c603900741c06c0d264031703082d24584115541a040c86900c2d0640c049031140315521503808894150f5100b1284588400400c006845101c4070810f555104c0300c01040348a004134180745030b005804046c0c2e5821102410300600301ea004032403488844842e0b03240003610340342c0140c526800903664645641c4507410080e0107a8042005000e64601d040c0e00d5201c0801c009130002078030349140d8040c0030f0300c2e00c1c0d00034242080300161044004490607401c00c0c01610555215840b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 452285773 1250 452284523 452284529
    0x30411030a080409020f091f0f0306030213110f0304110901050604050612100512010f0e0c03100213051002010e070e09070302090a020705070e0f0c0307121e15170304 73
    0x200b05403405240c05000c0740250301501c19003c17040c0d0144540c072043c1d6912200200540700d03690615645581841c0010035219000c400ca10030f2510b8844c3c28800350f200d5031100c0c0310b020b802d9040052844409400b100703850141c1840c07050f221000000304001c200c3c004160300402103007035482d034401d6600c0c0c50400c071301400b45010352500102d081c41146c944800c00306c03001d5009228501850342480c0c46202003180341c0f0500d83d2940c0d07569160404442c04040d20b00c240d10f440d03408000079090b2202c140c000241c80e40001841d11180d5600810716040e028182802c0c04002c00009001c0384450222030006806042d03c180c1c02e45103401007400004400585a248600c0b904e101e00142441360308650810540c0700010300340d801c0907a403d105110000b44208805809411458003000b102e281c40c41c820500940d004280308941a01841404211034200c80c202580c2140b69101091003659070984102c000403001c1d191400a0600000300e000004a141071000d580080c22805007034040360141541d2440b9901c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 452287023 1250 452285773 452285783
    0x1008071a16030c15090515010b0712090803030406051f0b160f0602070602070b090a1a040305070507151d1309140d0e130903140901140c03030411030a 66
    0x40328407540144062081d040d48241003440c0c1030721460301c4181c0244ca101c03050410b0325540d0a180c0090000410080c055180c2c2106403c4440d81858244059802011801000c44081600480c089802038203c80c01603d500001c581c0c9a00d800e0400c0c1001c3c03e425514001402c050862822000d021018520143c41407005003e1405110b0300000351803000c41081030f83e03404040c40c11100020110700061480034005c4002503103603041c6003012424644081d060750b4440e407040045a00080c0d4002c900303940110000d43e403024582d43c0b0308003070b0303418443c2c41d0000b0220701600c10302140000f0260942600c5c03003960794a110760741040e580c0618010b81c921540c0e0360722844106110086c20003640100a2851151040d080d141c40407500540c40c0410170130b000d80209098007a95070450800300070104103036204000c14004200191006000d24211035034030258030500150071200359010348500314010840c1d050f0700f55502c082e81e820a4070ba41040d2000c94071440203030b40005c0180340004008002607005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 452288273 1250 452287023 452287027
    0x806040327080f0a020306071b02040902060d051e01080307020607060e0a02060a03020a0e011403040b150a0620010203012d051309021f02030a0509030a0b1008071a 72
    0x259600303881030312401000400c4110007400115008100780540d41d0164400c400400c151049881003508145000307040c1c00030040400c2d5072503002d40f2a8121400c29903016100001c0414213400403410a204401003e4201030600c408e21548400e0441c0b07845010104000c0f040c2682d80300c804c1c0c180c50384910705003c0e500500038000080031482e1540810036000004003121a005001d070b02184440c0c000600c10008a9408170302c040f070740c6421016811140340246048102801c251102601e14040940f0242507140d08600044100c8407008200c01c4a500c002d041c801c45070340d24400104400642c0404980e4844007041507588041c0500946c2d05880400d82a20580d03000021114403d2001c042c7c40d200381c1c115007070001b81a44070480001c44d980c0140b000403400080c50700600500301e0303c80c2c6a4003003411184036070307615113540403040d03500b04002454020747e94024070f0002440c1030009600500704c5007088040c46241c07110090390308211152902580d074155564401408686800344100301a4941 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 452289523 1250 452288273 452288297
    0x20a02010305060f190603050f0103030f0309020d06020f04031e08041e09050f06010815130b06300a05060108180f070e01050f061e03060d0b040b0f0108060403 70
    0x2039001168400005000411318030f1101d0000b1355250114240400381300a4000180040c9500d40552680302d149103030910460751450341e00a290981d080c0d540c1c020143c1d918043c4045586d0352208244041e003114095403a0000b000c00a0b03d41d0384144001c0368203400d08240d5518034410302c00c2044260f0f8220f502141407514108442001181c0701c00c200143d0342444101255441d01d912039103006a19210203101140b61034000500200c0c4080c144803011095080814400e03558801040445400c2400c049418035581c80440c001d40503c0e020703400d0040002e00c5642e07801d801070300c500340011500302c4d2424503030b287e07240b601c422140c1c1130719110b0014052030001440c86001c810030741d01c414078000499801003110402c0303034102406500020318116035980100a07526100314403002000007100c940e0328104c003170b4220840411001c850002402e00200000342c2d50b40d9540c0d60740c807031150400260302c103610b894a0a01c0000c8000c4465074940da85290002c0352400e030005146205a6260f203580c403007c48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 452290773 1250 452289523 452289527
    0x906082109060408030a091706091b062a0705090c040504020a0c0b07020c190e01170a0b1303080c09030c0f130606021c0e011e02071203080a150501020a0201 69
    0x404259015000001000006054002000181401c51b0380ba5901d042071414a421503511800e40c9100b0f8056078411000c1c0100d1031703c003103244034010142c9030610115400c990f021550758090303440e40d0315030300211000f400d644008030740007094800181001e0710b0016880380100240c220043c1c40110207440148001d10090500f075000702903001c5907007408055080075659005640908460b00c0d40160014503440d02a420040e20103170090170b40f542880d031507a0400d08810b024841c1480703000920302d403c41191580b004140502000160406000314451800341040d001036208480202e0000748404000348802185201341d45013000028050000f01202400b00080724884140503940070300d59200c3c45108004074820790004103c03e4014000d01000b0445048000740e0200c440ca003442800c007040c0311260303130165240c41d214041510420443c034920600305c1c540a0039400115408580c030110390207051f00710700001d2180342e072902c1c180200c11410382003a1001c104d91059078056031140074130900643c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 452292023 1250 452290773 452290777
    0x3140705040213061d0409080702030d0203160f0212060403081b1606021b070602010c12140f10090c050304060b0123071b09020304022b0212030912030409060821 71
    0x2002100d141600213048170018080300da190100321928000001c0800c01c40c20140109220000c460025504201d10350244110308190b0600080406403c21901700c115a00c6603001111a403026046031080c0c6040d20f006011060103070390021002d8496840d0401c1d800b1407004481110315140004641032510b50b5402029401c0390610594a11400c0c0022504007020022603004001d00da00225048100d1030019109280700c48030080c80e141414400c0500c4031543c1074164000b00c5002c642c1007981d6410241d4580010305401c02c01c8141d0030030281c0151281e100c4080c0d40560301580303040100c008100010342d122a01d5040b032411540001104030000d10501020b048201d0040ca405040c81240e070001d045645410303000442b0f0545d011040c08154200b61915514581d2060a2480d4800c031003094100400b04000009105916601d800c03200290309100ba21716144002c0c0c280c220160b030b0f960031241c880d00b10340104401d1528100001031000400900c1600c3e016150745140c9040b410003040007015 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 452293273 1250 452292023 452292047
    0x909020a0c050f0303060f040504260d020c0109030e030109030206070e0d020612010e0c03070c1e060e07050907030b060405040c0306120f050111040e0a0c0311040314070504021306 79
    0x3101c12425201d02203442480000641042140995500d1038000704010747c200b001d0322103500891034002008000355001c018512090084524450b0038100c0340f1010f41c4c1c91140081c8a0f0741c203400480c030784a078400150000d1f41d0052285e107a511f2119901010706080300d065210180041c0c0c0040c01060045014102c1030038005c50241c030a0f0022907654000c11060340c4130b050022050126400104101217903600b8454010780ca54043d5455420141030007071642c1031610000c1c2c040d100032602c02c0503061904c0c00c0405190f901c4a0103202e02d0860402294a031981449410b000b21180d20000e40d4242c400d00c254050000028011400c0c10308050601c401000002080c00c18181e450001141c803c0489403109100d5200d951403130304184881c40c1050a481c0c25003840681100e09120920080340401c60391035000031a0705c4000b907400c9400038214041c010301d44120385070900009020080c8940740c80d80d01d00d080494000c4036141c070340c1d03241032000700e120304c0141188000b007011003480102d100d90941421 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 452294523 1250 452293273 452293277
    0x305040510090b0a061707060503190504030206191b080a09140a0501060e04030e040f0f2c06060603042307170c01030507080a0b1c0c03140c010909020a 67
    0x505110128040442e00c0d4020706581c1c6030075141c1080104c180c0c600135440589101003c04507880442c000a03503035021107004040a024020000400350b0780c1c4528441841080c800050103103007007900b800f075110407080e1201e8141382e403140c800b400c1075001800b80c0a80c80282c01c25603010121002811600c4001c054035105c0750a072a0b030801404143c8450001d00300400314000b5041200700391604030700310f134440d0f440f0b89c02170b03c10700b4108004660450400100100c0944002c540c41401c180c900303005000260340e82e240740d8502217408030081c1c42418003890702d03a4212101350002610b40003203a5aa003080315403a500410030800030b0700090141614160f1451071003601e4110b00507412000d410302c2074540044c0041090820580e81d4a02c0c204420b90300200c084c00c08006c0c0b0300380060014403028005250400a40c1c032144101965101c0054410f5543c4100c092021a446645080e0000ba0000e1009840700d150f076076004840304001051148141d801610ba04400b01d14010854000c1d410503051401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 452295773 1250 452294523 452294533
    0x30a1109090421080702120c0115031b080f0a06110d38010c0303020a05070c090e1203010e13170a0206190204030503070b060a03021c02040c0e06090103050405 70
    0x1019268105481d010360303c1000d9819141c00310240300751070881d0340318407102044440e03030910071031540100d02445200c100d58441d640c1d40c00400c3c8000d02502069000d40380b49141041d0010a1004051011010014403040440c0b0103985003500e95650b030200b200700029410011b80f030000201e065001114a400c00c11a130b50824640f501154100d89004441e02c210030fa129802d0340b19610011501142071002c10741451010200e400020800f14000c000202419400108201e1041c020f0098500065000a0146100f5100c2a01c60054a12910030303421a20455010110100d808402d6a040c1ca448400f0610141c0e240390074480d0252400c0c2d0f040c0d0b581401c00c1302c0300100410560040154014a40041c1000c1c10441c420215615180c1001c1050b03901c10f01081c0300007000401203400580d04000d60040c20344454001070f4507400345074002944030500c0c50105401c85807010060341124000c5404202e01301684d42c3c21b482803500602c429910a404119030203156019a02094000b070248080f50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 452297023 1250 452295773 452295787
    0xa14130b01140a020601030210030507020c010818030a02030912010203010806070c1104050103110909011b03022a0d0f02060601080118090b07052502030d1101020913020705060615030a11 82
    0x1c500f035005940c403600580101c03005205505051003403588880e100c0c5008c0103285820040291150580b49040d4100040700b03000c142c6142034080041c00e102031100c140da6807001c4112002c0c4d56540200d020501840d04080420340041c01842620b040b1b49a14000d4102c656a0080490304802059000c840800700414001001c1d1581c1c82054043c40c41032004602112040c020800d40200041040c40c0582c10084011600c0e4420f051024010029040142c4c0340e03c403c040014085840740c008410680c18420484101d41b000180e050315035640f500c808441e5140340c4000c80c3c075a0b1080341d0742030200d100c5400400016010741840c61500c4040c40000480d10415691111142c000f0798228002481c003040300d00321580c041010400c41a44540204080103040d404a62127280071031212040c48500440020880300c00c0d0100d0700e41c4d032070041503181000c032110f03901c50080d04035980984485c4641000540281854004174407030b4003840e84124119039403448000043d204002010500007014400c00c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 452298273 1250 452297023 452297057
    0x1b01050103060207021f020304060e0d02120616170114030f060106050c19230f03070614061903060b060d0912034a0303090105060a14130b01 62
    0x45028600c00c01d800344e60741071640100020004420f001000080d902804612041c3d000822101101c00c5418912514010364002680000c00d03104003a42002e4403c04481011401040780c0b03206980d02550546095800c0758110380600f030f00c509074042880343c900180b101d1480101c1030504160010300720b40d00140c1c1244242d0a098080e4004008590041020402c8082c203000d000741c403401018940034200681d44485000303190702c0b1b030905102406418070042401c0d041c080480170041d1041202d6599081c1c2c605030005200c1000011014101d0001282c05c40c0b4015084124618000984031141401c0d502c1d000300070900f03044c9282c3c0c403400803c522980d01c3d42c07500400c0c1e0090b004810404800704038040280030385101d8481c01195076001e0805036900c042c4410302080964060301c0052503030741e130590b1251300147d2000411680e440044200901401c054100768414101521a00703586a90340c1240c803c40c034010304c3c035030303a00581c90030000540301610307803242540b01d00502d03000740780d0403040c044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 452299523 1250 452298273 452298281
    0x7090e0c030a270c17030d0509032701020616020a0b09010204052809060605190912051c0905031f18030c05150c040303080a0e071e0e010e010b1b01 65
    0x16203403601407003ca40c00c0c04407000d11000240101142c0c012280c545080c2c071901c0c2e10500700c0e01d81142e81d0f9000032a07910003080055551107000710341e440e21a039007650000380b81601c0070703c2c03864014400c40b400110140d004403106d150030a0795800428000c0076558402e60750300c0009244018566090000041559500004110710a1906941c0b007150020481e0480201385035000016017500702102004882d40c010300b206c0c0704400c454240c1004156203001110f02c00000e0f4002c54554504842910502c200410f0030940d020b011020001c5046100d00c081c1c1e042c000d1171060f01ea16400401e4020081060966140c58403161510001500e00400015200800503c1d0781500050612102c0710304201e0b08100703007040c120304514820702d5840d101a107107440703200e40d0000400b008404000315070501d00e00c0c0c021800b680041402d4901060322030402511007040c1e031807070f4050003240120018498082000321810384403e0107803480d5683c00c1120a03601c90380b100c040c0c441c00503408400c510390b1440c00c3c8a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 452300773 1250 452299523 452299571
    0x30b070c021005070317060303030622090803180a1515030b0f040b010605041a090609040609051e040b0621030d1a0303120105101b0c050907090e0c030a 67
    0x40f05a2500d05500703004001c50010f007004003010b04020140700c0e560741d001090b69400348048034161402150070303481d00d24007021240d06524a905044405040184001c0550300c41c4100c2d0b91a00442c0350445c0c9015618211040c000d000d01c030354005646041901ca0f007016401140390741551108581d00d54400e04005030032035402d040042d410b0140420001d82100c1035004189901c0c00c0c0303040a0528450b502c05160030001c05a002400085d00f00168030380c001500d01500c0300500400200b59584c804d5006420100e6007404c1c03980f8026415940daa640c5203c01d0302441d00440d0a06a40e51f490040c44111140540d40d4503103846100801c1241000400007099040c1c0c2110010903504142c0342030855010030258541d01c40e80090100702d40c3c605100320600d04440381210001c0d010442e950042e110294035a0004918200c03401a280c1800031001ea5002121815100f0707030003603501c0031021180780c20203005280c50345103000c011440340382044000d584c004541d000000345c00000d10288107140340c0441 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 452302023 1250 452300773 452300777
    0xb09011806150f0f090c1b0f030e0103090b13081905041a1c0b12100b030607210b130e150a020a090519080105100f080c0a030b070c0210 60
    0x110010304030b03070091800800400c20707941c9490b0940d040c00300c4205a40454010a00c0c880d0362079001140540c42a251003003540100c142200ea903407000d003400a0b041c152150280e0116144501644255119200742041c4941081e601d003607036160000da119404000d400251218041801080c07400801c000c102d41001e1480d4a60b2540d403441c0c980c844030402e00180a03450948810704c0101400100c0640c3c00c240003030030000024800c005040011116858480740140703a20419003e0f4002c00e0042d408020550012000c0fa00c0305d50760484111922b03180020f0000c0b103003000c06a81500102d80d900004101040100342c40c6140000702824001c5940c003a004601e9944500081100300d01400c000380e400403000390301945018241800544401ca052060500622805003024035001150b0031200c090b0520f41b0003030049050009201c8410482c900407102e02529182c80051034420000d060a6800400b80002000c0c81c99521340c000800c000800c0501800609810440180c1c0c601280301d00240d095 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 452303273 1250 452302023 452302031
    0xc28021e060f04210b04030c0309030b0705040303090f08070b0309191a0a053102060d0b090901150501050918010f0603110c060f06030f060c0a0e040c08040b09011806 73
    0x2c2101452001d0304004c42c0051220f04100e100046000700788055442500341c1071040541075035142c104d40b4285682c1c400342010042c1824842c031a5404001001102e0103580c5240d13055856034116800d003000707845140c0480d80001030801081403480c0c05141e0260604040e503202e0b141601d15000010f104000c1210200700f29440301e00c5640290b24245c0d0020100b0004101601e094200541c9410760400c4401d184480400003c07407110a01820701d0200d54060174407502c40c0e284100c1e010207000c110801601c1541d40720002210b50170140b0800c5480103590418154851601e00103607915030100c0c050302d41141c140706071140840c0402003a2802171130511440703070300c052030810002d003250701034a03818807101020072501e00c0100000510039000020034007a1050703512088006450203101c1d141c001d005000324010042da11030510043d11550360b031501c6044491100c4820442102c109001d10008101804c0100f001305030b4410025500018540000903c150201b451501904840d10100c9420b519 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 452304523 1250 452303273 452303279
    0xa0c141b1c0b010b03060a03061d01180b1501050408010e0705130603080409051e010303090608010e010308030f0604150b040504060e010806070f02030403170c28021e060f04 76
    0x40352000415101d49100d840c21010240da507400c1d4110418461940780a0f030100109106942d407501e440001d5900c0b4904100940801c5611003c25581c010501c4032546060240030b41d04401d00c51203030400740d02001400c0c09542e01a0b00341044061400c480e41040001d00c80407401c11000d2040d00b203411000e800410702607180c04104000b0709252469000840c0c00c0c0101080001c907840107035000d4400100000c6450b55980c1082e00020700c180c6d1045880050075000002851380003c5a01c0030b82c1c2550381d0311580c81c0e8850720140d511080030311004007000d000b0000581c8089a845989421510060011404280b0328401080c4010a6080503040410005082189241610031782d0300900043c04070003019850302210329110400200707098184607140a07564401c520900444000e5544801200784141081d244904103070054031510a191260002201146d16121804040c02e9011111212030400c0c940c02d001500b0354100111098065280c6040c245607a00e101408020608078000c07500c583ca = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 452305773 1250 452304523 452304529
    0xc03050a17090a15180206030a11040b04061202070f0f020310050a060512010606080121151e0e0c01180b0a0804020a170304120f020a0b031f0b0a0c141b 67
    0x2540c03130004c42030036117080010a030b12152141c5503004650129107182c1c403542e0b1400d054024151085800e41641400940440c0c900340d4600a0400c0d03031103958609540010b508140e40407446400c0018144018038074050001501203400b440c40c092001c0e0580d41c84459190400741075070760a8512401c89515a8001d000c1d41c1466000500c2011040d0000c0c04150306c0e1210140c60f1030301c18041c01007007807055404010303803150049403105a40d40c44078058501000e020901002400071060300f01d2a42000c000d102440c0002e400b0f20f40d003400458014060b99070b1464019160369910212258498192000025005000a0140496000030b03110b02410b80ba02c0d1041002949554201510101c01c1d01d4086250010000503501501d4034030798400b500085c14104140d444071b1000f0000d5120407a50004100b824517000030b5400781c0c0b01e0a80340c0c00300e070703c0d014400c45070360400b40105a40d9000a04c104a01d0700e1195410aa9250040030305425000d0a42400c46c00d115000a56144196101000c0c4002d41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 452307023 1250 452305773 452305793
    0xc0906020f070308030f070c1509171c1a19290412030908160905340923030d1b02040c0e1c05010b010f0c03050a17090a 53
    0x441009000b01ca0306580d103296080c0400341c01207215500d40000901e049005595000d0302d107412141d03046c241c00300080701c440039001459003141c03885d124058084d2050711401c261080c0c588001c080e00c200c041071866850051481c3d51007041c00100c98500750600c1c1c0c94115004200c0d840c9101000c003064241022558551a800349412140108103c0c003500c4103580c02c16502079950040001c0302c0403400782011501c86039241c203c503009000d640114a031445900c1c50789411240515000e01241c1d4071440e2904c111000002d800c8040703804200c04160903207000d0109140e4601d02e04100070a682c9860b05100306c440c94444480031502501c040300050f20382004101c00c1c0d0030f00c526240342c0848070361500c1e40c4962282d42000340aa610b4000d040340302800b03071b80600d0162700042c004080c080c2c203440301c800440c1d001d42c90684088d403915254405c81d500c40d65042c01401c40d50707121070085c030705141da04540c80e070302181c2c0c0c0f08108050101214403102d88046054005c2d100800104039824503410041048 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 452308273 1250 452307023 452307043
    0x3030f0617070b030601051605030f030a020307020607030b03030414042d0e011811131503031407030509090a020708040b0a020c01020a1104110c061303080703060b0702150d0c090602 80
    0x3c0418010040260781c04001c5401100d40300101c1c0740c1050f040e141040c80d40c0907441d0a44842c00e008000c00001d82d19907405984103080710750031a032042e00d80c03d000b40c04942000c505a9056001084184420b40c00491540c1d00b0013806800051070b1b00841d90312003440301a0000115000c4800c040309840707001907000e02c420320344143c4020007400458045112500403101c034010b0511882c031503040020b039221442e2100307007681c154041c4080540c1c141031a02c4201c0c2030000720049002e081c14000c22540e4402034444099140d00c034240b41c40b81c07560411201150040203c00c40c00c0d000c1250702d00040300c3c800070300024011284841c2e1601075601002c0d00701305001c41180e0440d400300319568041100e60142074100902035400046a84404030b026003148034200041c103485c8950400c1c0081c00d8080c41c40c1c0802c60380640d44901007521205030842c10b4a01a02c11044030500502c0030101500d84101c800d08208041800e4a203820440744c144c5094801c1285601c011460102c0200051601800303a2410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 452309523 1250 452308273 452308289
    0x604061e050903070e070314040b01080f01061a0c07031b05010306091b0e060d110307081e07140904050a14160c080a140d0504030e04090201020d030903030f061707 72
    0x42c00142800300e6a218500e01ca44200802c400c03011500507030180d4024808092683c221a0b402d281ca0300b44502c0c0241c081c80707061040e1240381203107510340b1410b20410050350440c1c020b5080c2d06c8048070400380d56400482000c0d1250140031800030002c0d800750382d000035061004070203800940c64040054100c87d041d070300c011280b5051841100c14122051744110690142d41804460580c1100208100e0f02600c002d40550b00e10303240340c0400c0c480c0108091485107041b83d5404019540d00c0c490b680d0344402c105181036201c00604003007032401c0d00801405614120304000d450801c0d000d8400103059590654907945440d0750380c0075000c625213030642c655600521660b43c001e06881e01c000003c0c2811002c030005060f03034001161049107548521081011100401400c0761241500442c80009040554080f404541a0680700015040600603a101075805801404050304503440540152140310002c0302010780d21401c4c0100f2031014480d51000d410320001030000c6500c8000194a0840301d6080040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 452310773 1250 452309523 452309527
    0x150909160f1203030c090906090e060c0a09060f0c08030a1a0a0b070809180108030a0e100804080328090c0b090d0807051504030c050606151b07050604061e05 69
    0x1042ca0859281d848100381d0524000440885011085450303100c0b60f0841302840303051403c00030303406425402101800d107540e0145d9503d6140c01021100302e210f14850080840c200300010042180181c8812000001c1c0c0d003840b0b0004110396131a60810b81c0210b40200303102c0d136182e05c1403c010020a0a46000c148140d0302c5a02050030000b410905006140c0300400103403000400b640300b40c07076001703466001c20708145c0d0602895845155441e102e801002d940d00000e0444c01d40b00d0741919001400c40c2080b03d16444d580002d03241c54440481692005010407803681540102c40348641000c0401061001c2e5010000b840008514041c000c0c81c942c4e5000c0d651501061005e40b109980b00500c0506456103d00c80c140d50300f00078500035050a0300d21a4104011039048200007e01d5000700700402c62131300c2181130341d40d41d44d82c0380c080012080452040441c00c0b2070601c402154030703035003000c51100d00310b20204940c007081e5140f0015001da4000c0d0424000560b41a000303c0425168000b1038040780402e0800134 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 452312023 1250 452310773 452310779
    0x9090618190908041205160f1703070b010306140c040303050421020a06050307090e060307120302150a0b122109010309021309110d080904050a0b1c020909030c0c09150909160f 77
    0xc40c0c1d14405016045440d0219140d135100d180003041115009030380305425123320341c0e5a080050040210307004802c071051192002640038a20704040310184d82d40b40d02c2d0681803a081400c10a01c03001d883c00016a01d0103400c0c902000760b69002000001042f483d540d0f01d07528600060f00070200d0340070b6485480d9403c44441440955900405c8a03025140080d070786581d28035072400e080780340c243c0800c6400400114881440b20110300d0790054031142405440303402d02114000c03501e980d58030120340c0301e001900c1c540e8045c002c0685417000521482074145801b00c5d40c6103440d00001d0f1100c034040c800752411507541400c40100840810a81c8011400f10742418408250345ca40640900c20750025510460780e9200207018000a944044030042d0060115480c84103100c407a45c60300c0031003a0082c1e00c1031600e0b0000504011001007200d1280403410b01415082032124280140b92101505208014a0078001038015444040a81d48906011300080c0000c040b280e190f00c0340b1207002c0c1c00002015074421014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 452313273 1250 452312023 452312039
    0xc0932130f051920090109180501030c170a1103010b040204090902041802100f1418030723090907030204090803041b0e01061209020a0801020909061819090804120516 73
    0x2100c56541c9071504e20b03555102c4031004845001ea0b07038100041500d580041c82150300e246a0129050342d00c0365001c240c845403602070701801c5400c1d80103d921607900c10021040060f0b20304040214410001c3c002040c1c0b211a03030000780aa8110b40c20171003806645903850401e614003806010005440b550745082803800c1707500407034500d409000551050001e81c0101180451041862031000c1e084291056107489021341001950440d129010744244580d0740d02182400210401980170750211440340070b0042c10000348804000c00401d2400701e40a202000009a1a01d00410303032100c0c4030301c4c1c0c007076a030386440d00d841c100640385200200300341c41191000f8404841c0c454119410b40700242020355400103039440305000741180f0980207401186ca500001425081500a4041580102d0300300d071050f40e8180a00030000c03401024141c40e00064004140600b04024404045491885010a07010899164640e983c0d1150b480030756040c117441054414004103001e201c0b0046512044058820720306586 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 452314523 1250 452313273 452313311
    0x20703080c07030512010f090c110613030e040c180608070503040209090a0212060709140607020105091801030c0f050303090d06050907030f060c0932130f0519 70
    0x590002110000380c6005241c0154141d0304c54820400d07503031203c0e40c0c407548071f41000c90640c403503504c913a03052201c045844d42c01042d0081c0c070840203d00801981d941d4900700102164603160940038000e0316405201180c545000b1110600004d8807400400e88a00d03007454100130741c5902810400a400041c072003081e50010499030042d404440800c0c1c26202e00310560704040304041c000394042e42e600c40380e01d0410400f180c060700ca00440d4a0b49480c5543e2226484403001e40d038010300346e004c001041800019070141000d01344581c0003034130601072101c4010b0070b249425001c4c0c206a4240c0c500034820010100071110550107803e0903000386080c44440c01c0840c4603080c5442c0d0081c0380d030ba100c07800541c082d441081804000c58100c00c4140c00c0d22030504008001340225641000001c860103000310f407908290448414400740c803451080c003107460303c8000340000042d01c2990341c0214501692a136181c1c0901501c179250315107010010b42c604001c115403510b100c8140c14040c416040c040300c1070201800c0b040d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 452315773 1250 452314523 452314531
    0x608071a03040201141b150601020c010c08030714040303020309040b04090807060506150a090906060905061209070506041701061e0b1e07050a1719050c0a020406080a021302070308 79
    0x20700281d039a0b8802403254540c002c481c0c06e000007041d06110480d0110700010603441d074203883e0342588581d45410004913100c08814200c24089201070391040005864a402140d00a81502d0060380002c0c50402040c1603034042e6100350016800806c1c00701c1c03646000e00c500c0769021340489040164141a5503242254040c6000242c00c240d03445001070f0583c0c95041503203d4005102d024265074051550020306400068020b018516203001c0d40494258098007041c0f00b5107000505103401c003d031003a0b035480c1c4004000c01d10116070094540000b02c40d160100070788098003c24491041c0c0454502019003192030b02e078448004500c0140b401140300030300700c050909840340440280d54400100081d84060080f582511410200c00113012060040205904014a10442440d03020910f0b0762881d01042c098981034024119840c0a1544180c1c0904c000b0300d000640300c41a0b988015044c0c00284c11942c50781d20031203080c0c005400c000308614107040c08095060800b041107003881680c0d01c0003060504020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 452317023 1250 452315773 452315777
    0x50a170f0627120a031a04110f07170304060c0f0e0f010c03020313080303040311010209010e040c021608010b1201060b04050405250915020a02030c270a0608071a03040201 75
    0x380c880b6440b804140907100242d0300d44243c003651543d41c110018001e20851101c3c466243c4010141c10340d900e007a0180140490340c031707a41d090625001c2508800c207907101c0301b0200d5440c1400000c00f1349d4005408041e6200d00c2c010807000500740032840010300140d004520034002c01245100315881640c5249410180c03101c03e00e81905036507070910707003645144110303070100b500c110340e11b2000501d80d08e000000b0b6118511a50f0f481c0e02e10049116030310700741c0c020001c26901050351203000181e18201070b4001088809036104a40161010407001002140030384c0000045945032004080142060200040c5503441c00c0000c014452420f8202c0c5c1c041d0003a0702545205644540c08203104d820892400040b1010300180314260708014600541081c042c1e2141074401400403030940d10780b034004a11344200680240241c070912a4050412070900d41580340c1404030342c21404c010a000a114075100d11844901a00062480c200703204030b1324161859000100340441003c116640c2c2c0403103000e480c0c0190b828 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 452318273 1250 452317023 452317081
    0x110606010807051804021b1221220f0b01050105070201080415060f0e04050c2d130c02010509060c07050d031802040f1d0c010f0e0307050a170f06 64
    0xa03213003032961462115101940240049a4010a02d0a010454440e1480a02180c210a091601617403160003030070986000d59119a84901e0140c003103071041907204c440e02d4140d0000d0603905034070074440c802c0d8440a03109052445904c41c1040352040c0e205014000c2420a01d0500841c0d6000a14621004000602c503150080f280c5808070300580002020b4401545495280b9880381a014010b40b4110703815106442415000907290502c07181d640c0d440203800703042681c3c000440c140006c00410845405801116020395001c64804070f1150903030114403a40080f0b02c134103200a5591400c4409495500c820074200081c4001640005850070310800d07a04000c540101105079030f000d0042000d201075003042c10031b0700340126140070750302034012107a008998654904d074400c2c085031760711a00d10b461400f1442c0500076100181c021200d80c140514005c5c00c44184c1920703540810356060983d4482d000c04159801d0140100300c00380210b0a510b20800b00810451a140404160701d500c1c50702180640810 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 452319523 1250 452318273 452318287
    0x10b090d05010626100204030807060c021e1b100c0b090c041103010e0a0905060c0702040e0d03020c1221180d020f0c010302040806040206210a05040311060601080705 73
    0xb90402c10003050414840e8407540041c1120010b101c04d000308078522402482c4c2c1044a00f035442c8217540a50303804c0b9007080e060201d0799880300000d20001100c034080d40f003104140c0c1c054594406c03200c0078405500010786100c09800803070401420000900f24400e00d821210300103100ea00c201d01c0024150002151080d03510f88000e41401e04400d8910240c2040c107100071800d031504200021030403552819001c0640341e603500d00c4001121700303602d0002d0254011301c0104030b1105d244405000b000b400113000066000601112030b281ca40303503030700c4900440c3e00483c0c41848000c0500c040c41e070100d00c8140c450300d030010f055403080f5040303180c0005210446c07036000410702811011850010b410441c50031035203103010550010b550ba0329060110100752051114445d9954071900955041703c504100270255500c445c5e00304a802d400111a05841422426015040c0c0d10b00d10422409480055000546400c00d420010f020b501c00004040007940120140600c590f40441000e034003442500c0e00980740c000b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 452320773 1250 452319523 452319533
    0x1a070615031a040210050c0706030b0a05031516050c121b010504051501050a0f05100c0b04030503060901090c05030f0402060405040c0203090a08060c03041113140f0609010b090d 78
    0x1109410150888548440720b4007004524050103025500803114081c0c1540b03900310440c0c50b0310403441e8400d803940040000308000c6010ba044042040c000804502241e82c4031008649000940701c604038032900d03810280584c0c80d45182d2560741003900b51400b1841c040c00340b00f070565140000390f003035900204006101a4507184184080c454603890000921850405042096130b8001074094100c9140c00707080006807501e401c820352000c0700e04c4000c43c1782c1282e2820040000f0810340e000414203104c100700320240041c3d02c58142c80d10952003600c0c0e03103071030341054418030450040c1600300c41c0c17009281494000a080c0c00c081030365030101610841061341e0791244041200b90149030b1040b40c21a00740403c003402141c001c800340c01280300a40352540015035a003100d50390351005441c4c21885034407c10104020850580680070198005046444a507144a040408440d80c0085050080c9064420300092240300b450389600040c00300c1e4101110750404000d2465072103900389441c85000c52038400000c220f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 452322023 1250 452320773 452320811
    0xf0304060f0908090307060f0905220c0f02210909060a0503010204080d12090b060d030c0b0106050d0b0103090309090b030c10030b030f070b0d020f1605010f061a0706 73
    0x81d124409000d0600035140400c0682c000e001590300c82c2c000c0c400045401d81c07245c0b8440c00701c158a980c69050440ca408140401e018a00101070b4040322107110301c0c84103d00c0390148071910b485542e14000ba00107150002414007901146039140311814481810411001800795983c504086a92000301d444010014001c240381b81d1000360194008030300000e42120104560003403410740d4450380c078140e1559040a080752010340d001442200b00601003451400c0841ca541c202030310034180700000180d0380d12013a404035002d0703001c0000608000f9021000c90314a02031004000004c1c2001c0c0400b0751a694042c040c1c10441c050b09a41d40c0d500e071022003561313808006a21410801510090041102c40002009000315494090207842a01d4803d85540070004080085480140155040200382c00a000296010384003c1c521414144046044600d1401c84604018450000081c074840080080d1043d2002a0700030282c6100304218000d8100f80391007256045035115038000b44070450301018040072 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 452323273 1250 452322023 452322041
    0x715030b0607060c02011a04061a07051203090a1106130b030714040806040b24010f030b090906040516080705060724150f030201050a0f1125080c0102030f030406 71
    0xfa5040c95000100b640d01980040402c9072088648118401e80c201071000766170f120310034401c803143c1400303200c41b28404050140048074803501c00e5135107103075821440f0700c055041134440c89a103400c50035004c41000040c1e040141394001c16070b0400d04103020f4021503007489000348600302c0300c224004000340000e403003000b104e2204115840c18a0b15261540394903a030392001202d0450303a4207500720200d907884a8a641d42d8400440b5040340ba820480c4140c011a4020003101000080c1601c4052036196540e4440c02580b041d6182001002e40d0321341801c0440c5000004100014803081c00f680500c0307040008101401a1603040c0c4d151aa201c54625090030000e00111002c04070134a00c08031034900709100c0c1c015000340001100e405c3c14a07500c0c0c1076515401034040c84000d02103202003008083c01401000c000c3d403003043c0c1e42402c00810a2041c2594244400025075800c0007090700b1650020401c15015280a00203090081c41403000000010f5078905c900501c65907107180c0032000904100060f0007110380303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 452324523 1250 452323273 452323283
    0x30509060f090306060a0b030112060b1309060b01030510050910031a04050d020c01120504020f030f030a092408150a060504051f052d0c0c030f0715030b0607 69
    0x15070000072080240e141c102125462190048601080c4580340c44800141a511030a1280b40346901c2c052006a107410b07030440441d58161108071100c0c0540c1c8100b1818201c41c0080c001003808081072038500100e509200e0240e050615040501443c810406410030503100103403811035060700c400d4450800e9440307980c0000d0254002d0108071503004030341d43c1c0c21401140301c2c0080301c6030000c52030b0042e41c44201c0600c0490006401d41c020001c900c4094000310307001400500102c1c6008102030101e800c0015206409a00e9840090f130021902d9010a11030020301e4202d171916a482401c8041200502403070344450108502040403030390110a01e8500c0c4070000d001080301c0340c5a0754544c00940950498490184101c0202c440003280a100315122009a01607654044c0b81219403207400c0d01c17030360540d128013030802e850701465445040580c0040030918171002c01851841090f4003050310f02404103586180c2504a0705042110144c00300f0002c822034828100484c80444101c0800d000d4001c001e80500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 452325773 1250 452324523 452324527
    0x1d0c100c050d020d0801150509060307030b040906050601111c0c29071103031b0a09031a060a0b28030b0306100e1b190c1401050a0513081603050906 65
    0x86202c1e0001903000350b200c0d0b2a21759070590780c0c1e1500b00c4014900c0c0c910005001c11030422041c201440e20b1002103901c1460350400050305c583e004042030448400400440e2129075450501c1078030740e006170202c140c0007410b200615421038068120401e214941c0d00d03240c288400c0054210801c103070143c20300546010b503100c0050002e1100a80700740c003c8151980d41c00300780d400c41e5030700403064044110385c41200060280d5241d0741c007244002c0706a90100307480c0c204001c5031400c0400000c0f024a020129003a0040700c1c2611410b145003045120030320f0381d1044560380301c204002d4bc0c0724411034a048801c1150500303404405a52600282c0142c405d4840403030f07140c0929410001e15019061060003610025070000c50565981d01031003109100c2c4800b1109003100c00e10141d140f840007030044020001c080d1509060a05041d928080c00e03020700f42a800081c0d449200704441001c05200e44c95010a0f85880034400b400300e500c695829204103200ea18000c140340800c0c000f498016001c6804007030020780b82c1d80e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 452327023 1250 452325773 452325793
    0x30b1201091703042105190509040b010f0c080f04030605010303020a12110a060e010621030e01020607050301050f0102010902090901060801060f06140319020703030204091d0c100c05 80
    0x1a009055088080312481d8603445039140d90b20065003541d00c92944881030b00c80c9844201002c8001480c4c5180980c04c000c8101b04444220300100780e144603000b8241ca4003501ea14051041200341c819030003d46c0c0c10803010703040300301c00c2c03940c801da00400481c1c100400c42e0703940c805034082110070310450700098007250911000004041d800509004001c0c001d40d000d10450030702c02000c039422180e101c0f100100f5405005040d0126455901424002c802d06c0000203480d039507100905611580c2540d40310868180400c035205142e000402125a450240301501040c500b000c000362050006000341030140081083c41d14941e4000d520011701103400415408180c40c1400e05da501a0085004508541d420600002062041d1440000964060361150000ca050841d2900c0081c1c00003800b010485414120342020741c00107100a0404074002d0340e015035610704210200f425140501c1c00c0040341c960b0411061440140480c1d1f01e51011000c44202c080b4400301401224a44610f40c0f003c0c0c020701444120f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 452328273 1250 452327023 452327059
    0xb131118041a010e010b09040204080a0c0f08060603060121330506062d04060507210c0605090102120907030b010e130b060d050f06060a0f03031e030b 66
    0xd8411441004011800c0400b02c4030802c0c080d03020320660840c04901c80040c8041d002c0301c4041c106441001c3c100604080d030b1000c1c187d2400000c0ca0065513540d07603a11040c000e408803003c008000d80042c130001c06050400c9008070b680d82c1030522071000e8100000240780303d2410074402c000c1803030303800440c80c00030304091000c20804032884103807058496a496040740400c01c034501480d803092000800a6017011001c0c00108035280903001805d484d00c1564600c603809102800c003030f10141c0481e03500c0d40d456456610782104c0c9401c0c00ca500d11515042c0344818080c1c180d015020340d0300668015000f04050f1220742881380a401116000090001010304000d5401c500003900c400312070188101030283c0c0da8814181941840a03034500804000140200002ca941110303000e0704508040e01c0c00131034110f607448550070300d803e5144401c1e06407c86010310202c1e141040619002c0c1041040c036040083c51070740d004d8201495400641560140082640b640074080ea220b604603900c0a40703c0c03400c00a07800c0407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 452329523 1250 452328273 452328319
    0xf0e0f0409080c062d0f0a09021c050c04060b1611060c0109051204260c040203040b07110606061c02070501090b0703150302060a050702210f0c04090b1311 68
    0xe5922044102104045c8540660b0351114580110400c1085c1c01d4949501c0120f00da10002c03c690b00203a01c644a2000584805c050428400c0740d83d0002689030341c403803521031b0a00c1c1340e220900d481941480001d100c1c070314801080311054100748021a491005d00d1030a1000140422030369603014001003605042c1507010f40140b070700300741310f2070948801c1800c45410803091700560244010800d440c10310100c113085c2c0503501000240440c000c40b002d0304a0000001c09a91048904854184402052104154020b094401c06040041c0980301e1854100003298090160108041803403000c911050707440900c40e81220b00c12508500240f20118032070070045606c0c4000e8030032500003407038020080c4095101400203000d5a40c01041280b428079411021112a04014001e80e440345165880358007400110050410400d82c0c02c0c050001c20701c1c1c0011190030494500d03200b0780150308202e80742c00018807980c0030380d521450054441c1e081120301e0030460342c0007510511042d0400308a8216010240e0400c01c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 452330773 1250 452329523 452329531
    0x11b0203060c121026010b1e09062b02180a020406020609071206020304021c0b01051002030906030a1812020c0a09090c15030905010212160f0e0f0409080c06 69
    0x40140015210021303002510111407088148820421034a101c0415801c12072240ca441c08000209000492200052880300f503017100301318522803964504d0580c05c0a0b01d4059001404a0340c1141803d1020030440380b00c0e40305010b06e14002c03280845001150348480c02d81c200c0c0041ea400b1030640745882d0b948180258460702604026105640c0001d200a0b4001206000d440081451a2500704a0360700d4a002e5000907108903400026400101082c4404044180d000c0307001d001c030243c507945890180b051114081481000b150810001c079280307a1155030817a500000100b01c005038840e05101150148207103007000400302c0c03a20384a4982d9550b8002b8a5210341441107444000d4555101920710880303100c404028882c601d00041000440041e21425420500c5030a012420384084d03500c41d03089038005014800b007a24204144074510500701c0d0128038014041c104141000f489c2c0101031701d090501c421191203044400065025030300c4540102e003103c6d900075071f800e4580c41d4403514591140c004803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 452332023 1250 452330773 452330797
    0x903020f0f1f0605100e0108060315181f06060f0e09040308070e0d0c030b060103090c0b0c0109020402041d28090c15080f06090103030806011b0203060c 67
    0xca162201050301c800408656000307001c1c5404901c01010794481e03048a07502e00d195600303800600c0b5241e0300f410034850315240e942c101500708407500140003014007822450107a8440000c0c1c5441c1402d1000503508040b4500229000ca030f42c0c502c034a481d103928040c030800c8540900c00c0c080007410450b04408251502501c2d03590b21040c04840442c0e004900e4414280e000380c924012401080c01003907503030740004a030b1519501003001e042c08200541c3c2d0003541107640e0822450100180952129290f0700f01c0400d01c0d0500880012b0307151111840d41602650160b01000502c045043c0001d522807410268007030402d640b15599103140c41d0304500609100c00c070800c04040090b29080c400c403600742d030b00110100c00043d0240e05900c1c0d540101130034201258002d85a010209003c04841a142e520b2140d590714400c90745400120400c8407000508824000e0620b07000500000750442045a07200c82c1c00c2c6410020080760340c1c0600842030704008042d4060092000380b0a51900c200014010607002e8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 452333273 1250 452332023 452332033
    0x5010b060708030a1d030301080706020601090213170106051507060506010c0b1501110a2604060504062a050d0f0203091005090a081b130b010806120a0b0a090302 71
    0x1020301505219400009100c0070003040028031a82060780440900b2001028490140d4110840540380d80d00c2a00b182d50140e0140320f041140c0384c1e04100700c501506445009606001150032405041c20a60040003c2c80780a400c2c001c40e5507400754010402410014554240030300b006c485c0000340c1d40400d009442c1d15080100041c0b40d94043c89c25081c00c0c541c070084d0005a035507241c8811a02d80c0d40f00a109041124030400c0a84403941006809802c2d40103440503038035184492800c044500b500c074402808100d00b80010040342c2e07080019141101c0c0107042c1040002c209142d020702e0042280b40f1141d03203066407603141082c441c0c0050f154480c800540c0b20700d0440b9103450b6003a0703038078082c1402c095407110310240c403080003038495800b0380708201016007102a000c0c0c40f81c401500345005000005103600340c00000541c140b900007848250805000005c00c01e003500d02000810000008040074016280c207181003600306810010114030b203400603180306490400c50300070400781100403400d40c018851 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 452334523 1250 452333273 452333291
    0x3130209090d080a02031816060224010b09040e0102070308010303090f080a062c0c031005090c0114041a040504050a0c1d36010f0612090807020402040609030501 71
    0xb003100b03804000792210303102e561320109010003941c0700526450808001d80d414101d441020050044049108448107503024107100c0000e140440442005914050041c544078003006200e0140c0d0545002810352550344104001080c041c000380d265411007588001440400d056108071041c0c10780e8800c1d40c038522440e54900d10049a44024000e07039140e50808041c1700e001070320035400750340d8491200000120b201c5403251483c186444a04c06098260400048461031b403605000d12400d1182c0303001c040106081c040714650b6100850308609041c41a041d42c1e0400d01c2145005490007802c2200040000a0b0801800e20064006100f41c501031400c150201d514407a05004041d010040c55643c09a82c0000c400041c80d0a0b0f95a00714a4000108200c03c10800008904419241d854040501840c401000041c03140703d0059004481e000b030801c40074498a548040d55902c80801c206011900780c4090400b4210b51003440d000a61207031000400051032608689a4011640110001c00107101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 452335773 1250 452334523 452334541
    0x5160503010606020c1320130501020109030f0305090c100e15040317070f1506030b0a061a070812070c1e0305030c030a020702041103090c010905151b0303130209 71
    0xb1680a100b01580240030b03004942d04101c0780407000781e07042041c00303c3c28444d10f5000d030441c00340d001070300b15281c400094091b000c0654524039900400c030030b00c000c000e0004d41e600e00412500c80e5002e902c0400d601d65021641d094010800b1000700da00042210007140b800d2000038050446c2d0191a0780580359031000072a48914400c03e442c2141c0e0084003040c00c09041f45203da0083d8001c0c40d00701d80a00704140c080002c11454900c070800483c035024006101d42c00d5080590040b1b5004100a090a0401e0000e00040e4415408140490030381030680c0e403109254540b5151b80e00031415681d241c810304a042081d004e6004020751913042c01a07c103101c0035000f008125203250088040600862810000308613070743d10a4004641c4405460401410300c20b50381c1c0000d0035281e0180704c00e40401c60100911030030341c10500001941d0242400c020005a00d0007011605440c00081051341451021541c052802c0650407041c0c0041d4010b816259a4600305d102419220b074980f6060f401900418000790813030b1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 452337023 1250 452335773 452335781
    0x1410050703020307024b011e0506040207320f210a0509011b0204181b0e0a020304020a051002031905040501080a0f110f0912030406050307030213120516050301 70
    0x5041b08038207071910301880200d0140a00000080c034604459402d07003da810280300e15403181303420341c03941d410801d09003012006981c0080c100602c50386c410092030b800240040c549010b80010048519104034500b01d0f100001c54024003925028040c000140b10b44a001142101404140c2140301007442500340210a83d03004415003807000c19000c11990340c8a47c0510180c05a82c194083d8264241400c2c2d40401d054401c40440c0d403262064401035a01042521a20b90010300c000880350001c0d145400c5e1141c0c04504044c01000c2d849a0000100d42551100f0f03880d0806050090080b0141a00040c4000d40e00c2d4014a050040d03172140f0600c1080043c0300381c0031903003104c0050f9500c40450311041804801040702502a00f240750740e459542d035840d42c00401a08981c00310364480c50711030140303400b413210410342000644110307001003105020450b003290950303170400010701d0300607101c00003858210b003c3d83c555000380c459000700c2071054003080400655503004102094a000283c2d64072001d1500761 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 452338129 1106 452337023 452337073
    0x60b01020c100e09041103030c280209070f020a0525080303040f080f090d1101030e071503020705100903030603021c030507141005070302030702 64
    0x65a014403450400c07050607180030055034418407004000c0c0d1440e1a48602c1041e0400105090124500b06000c05142c080c2c03c80e952211034006495403000401010400c40001c410f0003508002c50350402c0c100309501500750400c40c0c69110b000d030343d00441d41229508521408401c00b021880800081d0190400c510098603415901d42e00007400c1905500034401d81c0d4030030001e000000300b00d40c619043e03c44d040243d250301c1781d0004084211394858100d00c585e01142c20907080c000e001d502150300841e44802d803004c0040c88540000551a0251449031a100505820710704580078000d03001064647c1c45802520115a05000b1800032070300103840540000baa1140244114140a400700c0d80e0340300d803c500c40c003442c1e4081e50020f085120784a030007428803e400f0348402c40103074100600300003608210803d229078580300304018000e403c1160f1850061080c6502092020b018000102d84 = true := by decide +kernel

theorem cover : BRFrame.Cov 452158273 452338129 := by
  have h0 := BRFrame.cov_init 452158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 452158273 ≤ n) (h2 : n < 452338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
