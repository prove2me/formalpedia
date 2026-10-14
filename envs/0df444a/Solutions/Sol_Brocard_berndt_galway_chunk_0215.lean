-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0215
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:30:18.425486+00:00
-- url     : https://prove2.me/submissions/084ee324-21b1-402c-9e75-c1fc1bf47f47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 38489213 ≤ n < 38669069 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 38490463 1250 38489213 38489221
    0x1020c031e060714030f07050c0d090f050306010803030106050904020405040504030c0201110102090a180b0a0321080f0705130b030a0f0608071d0705040f0e040501050f040b1302190303080708 84
    0xd5000d6490604139100b040b000e10008020f00a600714541c0c0c0320905181090034900f1003100c00d841e0100480038100410075641d42402110b0340120160014003040f002019503503d00900740391203110600903541040400140c1c3c00403912590120740041401400800c01031905d030400810a000082040b40089e900203409080c1d10014025145070f0103000b40140887e904c0c103402441c501e8030722a0705201d91030b11200b8114090303031400e000c60010f40c01001005d4102c1c1e8551900f88d06080c040c0c014805103c0480103002103012507070807003039001189050044d56a50500c6040c04043c0b065401074007103038000010041c001003141c0269003d82c1098000b8800181c030f40102548504042c01284400302d484023201d0120200300070405e412100038205285001d0b20340390289090411501f1220080e600402444200282440740543c041d0a81803000c401d820282d4614000d01c00c040e141c00c03205c0c07409800ca04159a0b0b40c1c0d020080d41044449000220b660720b1401400c640400c03900d10b008102100e0002e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 38491713 1250 38490463 38490467
    0xd09020a1202031005092e0507020d0f0f05030705030a15030809100809030f070c0e0405010603031e0e21010207110301061203050d051513050a06090e100b01020c031e0607 75
    0x5980511a0240605990f24040d40b980003045441c11f4900604400c4402c4142028490320580d030140c07601c0d50181403035100e5810007070142079203881c3e000c0421030303000b5400010039849030039290006010701e880c0340ea90321441400c002420711001e2520745000d06a900000700245100202042c00041d9003c0c1290007040c01c040d600010120380c511081d400c00c200045124114078000d0030198440d590510170700f5212107148649013400c85045540d43e40d074500c01c0c414107810901c50601460030750009016000c082c0320050200c06c1c4d0040341c130700510310100c05a80d8020707444603c4c5084400c86000f1501d60b0f9142c00c08043c00340501c002e5902a519140003c1050b400d010020482e040d01a11014582242e5414050040a000382700300c41400201e91040311036600c00c81e0110440442407004212410401c00a000f11049c5a02009466180564004200c40702241a141054a00100090742c0700d0400042c3c1c100410441100e50500030500d06c0c0103041c10207116070b400d0654041c05c40e10785607245031382 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 38492963 1250 38491713 38491721
    0x30b0a03020d0b0402061b070303080a06060509120319030615090b0a1107030c1203020d11100e010b060309060403030b030312040210020a060f060819080405060d09020a12020310 78
    0x8042d41040e458002000030400d14901030390401d102030040c43c50802e101c64062411100c860b00c803411608904000c000340740c1e002e01c0d0035800c0b00004608200301490281c000d42144540b0843c4c42c0540601c0130360140c0c00030700b4015180d0681080621303504482003103400030b00400e42800340840d100401c071030004c01a84a940d524007a10700c100505c9181642c2000140c40f4040b13551100c203041d119070100400082c031646410001480005000b00031000c081c0f40281c1021030082c48441080030903240040c20000000b0314140c454600c040001d1515400680140582000004c054105c0f8001041c0042a200014814408c0340643c2d01000144900c100300340c0c40f442101800040b011101002c20f02502e0174400e2030400c4017150049402007240342d60384c14181c81c94090740c090815034444081250181c180b10300c00e1305134040b5203920480c0001e59100001401103000e80340c0101c501082000c00c0368031590010505580050401001030b658000004a1852610b0220b000e40594440c04003008130b2409 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 38494213 1250 38492963 38492969
    0xc140a0c0201050f040f090c03050f061f05040b0c0a0b01090911040b031504050705040c020c0307090513050a1214120a0e030f1303020f090c1e09030319030b0a 70
    0x240ea4240c00d14590011185904a2503080c80a03040c10440001c030b0000c40c0100c07200801040f80d01103440380300b841002c0d044900040c16403d5004080381005020703907400210074034460050b1100c66001c0310084d030880d405e02075508107400504000424000e803840002e13100c58254820f0000b41c6540e80c94950340400c0c1c80300d80000910300c3c40301c6200c1d50380c545030580041c9840b40001c1d04840c034540c124132403800e0300c0e001610280e4498101007014440340c145401440d040103264002417400f8a212004a40d40d024580306090200d0354580104048411030801c031400140c00c01c00b103c60180b07035402c014180c15105170f42940030480d899140c8045010502c182c072181403010306103035030350b071b846103203c1d40900240303508620a40000c020400000f6281806004054440d442186650b4194418441c2c0090b480603114804c41e05e400070814071000c0e22080701c44001000390040c07801b90702e003010408103010303120529615000c04207003000020501920701441140740c0ea01400380d224107109121081d24940 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 38495463 1250 38494213 38494217
    0x708070821030712020904151503021804090c0312020102030f0112050c01081b040e060f010507020901030609020a09020c030307030f0b0109060c0f050d0503150301060e1f08100c140a 80
    0x7000042d03c1c60701586071010b00b030040100c054a404608400101140e050408110902e1000c2d01c0a104124030b00e5542000d05030705080451500100c81020804075010208152103951940001c2080103001d6903481d00a40c4c0c0302031180d50008450002034042e4000300c48181989a20000008140d03800d41440824942c1000140071101030020045443c000004c3c48541941036400700d1000c40d01a42d0020001001c068070751811a003000d1080049994032805542e04020782407164034003590b00e80958a045035802440011110f0300c0388040f425001c2c0d26400b01c8034807032000c61410410170b40840190300c40c100c41c0d5010044403501c90404821a00e601c0b5425000425404060081c14000d1901e04070b001d000e22107100b020001ca540706442d0030000181b020000d5404401e0014240140c1c100c0102c141d4120024800c036801c00044990480005044807a1824004140903130401d46c004250040c002000135070351151032450380704010b040380a2401000500c01c01d500e00704820018142c84a07540c0507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 38496713 1250 38495463 38495467
    0x20d0203030c031c0c02240a0e060a060806010e061c110306070507050f0a150b0a0306060602031c060803070305030c0c010501080c13020403081206060f0d0902040b0f0102070302060f0403050708070821 88
    0x4101f8201140c500284001e0740c05070303560160040c1d4002040b03054400ea0719040046005400c119120b42855010391042c034002981c00148003407552000d00340c1d0718069280382c07841d640380d0a60520307040e200e0074480030325003500401007800161580700d030081144a004400b19101d00000c03004540e644c10010b039020b01003030380500c1250b032401e080e81c02c02c100700080100300e8a209074032610b411040781ca2a500a9026900000e080c00b00c0c003015210480003222080010808946000b1030640c0364818200c0007030801400000080c900001c40c1c0c02e4840303440c1c07814020000e075a101d0710901c1c0e0380c99004582074440d04440c2800700005906000716803d032540310304081c2c244403000d0352214026034060715450744031105104d0b460380900403001500204d07010f030303101151000380d900600c0704641514100301cac050340c0da03c4620101641c0000311642101e03415950207a460100703e0484445020366000103100d8000e0780d0001407516400107200050340c1c5c0300010b84000c5034590311a0072081c0c41b510b05101004000f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 38497963 1250 38496713 38496763
    0x30609070f0e010810050a080703030810060c0f06020f030a1406032404020f1e0a050a03020607030f140408010b03060612070b030406140702010e010b0319020d0203030c031c0c02 78
    0x4209104c9410104000085d400e0b2030b01e0b0380000380307146415041000c1d190300c42035042062581c000a019003017054a10030214140c100b4200508401c0c50500c0078060b6160048610108080ca504460901c00c400445a8680c105540142c001e4205820420200c140c0341010070b086142c04982070a440c83d40c00f0356452143d500c8548803004910050050740d1100d920a140072660729214811004024524032902c041840c0b4000c129005032150042800f80340c1c54003003400140c0721841181c0e012501420320034072180d803079101241e1418105448440c0d0b42800304000030101d0b015007000c0d603001403c40546105a1310301040c40324521900300c110034550301030b0b0403c00078101080300554009000d81030114018a503503c2c00c081c2070300c0503544000141c4d03407883d0441d0007290130700c1413441042c4210003030324070041d141c1c041620224103c48043e00c590088a01031085503400c2085508115a031010780f9103400c0040340c40d40920344205480010141000011041c844c07011074140031000114104074034a02c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 38499213 1250 38497963 38497967
    0x10e040f09050a0b070206010609030210051605030408030705100917030903070515160f0e0609041e05041403030402010c0803040f050f0c031002131502160b030609070f0e01 76
    0x494542140456600c0d412840807400a0090141c2d40d40900c074850024200a05c3c000c0c68160164413100400808020620041e600c000301c5611140040c43c100ea220840426100f680f280007440080c50b0780f00009000481506c04009011007a001d00300380d9000c03640007030041099a80020300200205c2140c210031000c00090409503400c0a65042100c2c1031501d9a81c4031840c140c2c0808600c2400c00b0701e01c041000a140b10300d804040c02c00245080818a410480c02034540c0703c026203030380d00c5044003184041761a04d80d64080c4600e854446220b5030110f4820001c1c2c1c00400081e03509031034504820084540e81400002181c2c0119070603521010441c02544030807001d40c0000d44100c0d9002420b03802c00021540800c01080502d030958040e02c0c0300c40c121000c0614107001c1100c281c040c1030042c84548001c2c0e2080d0150800c03101e4040d804400108a00340490610b40c030b02040c000d05082d0098049011b080d10b0300950301c900d0b410340710019261608031007a41c011880000d40c0380000d5901c901010254 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 38500463 1250 38499213 38499221
    0x8010f050f0a0509100308040e06040605120a020f180114030c0d0c0302010c02130e01060e0901060311060307050f0a020109060c08090a060b12010c02030309060f0603030d05090c0909010207060614010e04 89
    0x3181d0705241004a610b87d40c0b5100e40d5030055100088850b1064280070040c9024401d00e801030000300e540b80c2c006403a00c4080354541d8060800a4460002a81d4410341920b400f40c0102da5040c50082030051503840f500350905500a03800d10600901c80d403110040c26050410198070640d4201d1141c0c0140c40c0366500446941c4200c89049800691090f00c1c181282650301410307400d1580350002043c3c003800e1030381d441c01d540c40c010f11001441c4e041c00d6040000c90100e0f1000000440141c2d4001d90f40d6480280a65a80c070681d402c540c45a400010341c60003030f40c0d040d0b01c00c41d0704600c504818802d50700640d034200c400e443c0c25161480550805680d01e400034041c1d034010764442c0406000c54031840208080b69086960ba0f09a003000750b0800010803440d007a0911030103500c05400c0e1100441c030b0400f000400c3d92070240030501e0b08200d0303440303001c03504500003040880c007003110040c9580c200e0301c0d048049034080e402a140c2103034018148800820b184079100d501c03002c01c00040e950311198207050400c20002d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 38501713 1250 38500463 38500471
    0x1403031905070f050a020108060406050f010e1809150105010801030c060302070c09020309011a040204060507030c080702040504080c0d021507031e02040308070b09060903072a0608010f050f0a0509 86
    0x4880100000c0d00001c0c8003210f9000c9841c050300190502d4610b031300000d001544018030071b82c4120300c3c5c5901408980e885e5100d071501c2003020700c0c18105c440c0c0e6040100381046282c10740d021066801104022102070700040d113072000c940921403005240d03a039070010340c0ca0722400c0c00000e000d003c4a0509100703051203035000e0131545d4011100000c500d950796881000703c1c1c2c0190b92038481651036400c01c00c001104541500c1c0b40e40f40035241180703401d103081c500070710900480c18000d040000d000100d006001086098448060f0018405c0110b41490710300b00e045507000380a0b84186000f1030140c6198075002045042c071301e42186580204030b9840e440210003c01c500300903250807241140c20502000d4692016101840c070071a8440c0e41d0300181c0c100010b545000a10001d540d0b4404810440481808000e65001c180d000314140700040c0300b00e86d1410550200320300b1442d10f003540840011243e901184090482c4c1c1c5242d69007034025150b0042c03040d0081d5207032a050700120301ba44100010300b03080c4402684 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 38502963 1250 38501713 38501717
    0x50402030328030e031206040527010209011205060306010b03090313090906180c030602090f030a050d0813050303130c08030304030e130203130f0204061a0301030c14030319 76
    0xba2000b03540d0520060039456585000084040358058000c1e0341510408841c1d0802c0c0700114144011402d4020107104020004c030301468540300861416080007060041101942c1c41285003c220008541d000350440e40f5094002617944072481032214483c40383d94002d032030140203040180c0c00c00701303000c0c0c140e44040c00c06003552000f0020b45045400130781044001d404070010110796900c07641840b10503200c862031034103801d00322454228005003001906404480c0c0c88040940c4481e1480006442c290b2080030042d01406001401d4080040105a040c40b900c800c2e05ca520041d11180311400142c03540503002410781d07208002188546c0041c5c0c81a03890f142c07203205680060b03601c1c0d00c0000d00350740007501e080300072440381d00700075256103042c007102c00102280400c21411461b000381c10724a40c000c29400503086540f0b451900c001d40d03c0701d40140000d058903405032a00e4040c3c28040c2c89480d40244415036105264050118500036050351450041e14000c00071030034598481009801000d000e084002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 38504213 1250 38502963 38502967
    0xc0201061a2706040602010b0f04140f04080904060b1c020c1002090604090e0d020105161e180617060616021306050307060302071112030a050c0a02120f0d0c050307060504020303 78
    0x840d90b0f642d00e0080001c0c01da154008202149048148450254001e02c00f038072540c1402d501c0340c1a0025021806d80c020f1024403250656100e50800b03007054031801c3c0703035103030002d04140010400040e010024040701c2e6114000c0c400641e81c00c2003c2040b80220300125025401c502103505c1086100c7d00038001e07016000f0100ca10b0140d4602e0210112540c190600245820103420039102c1d94081c8103007903110041c40e0701303160b450242000041c1000540d0552a83c0481c14840d00307500c180c400d406020350205803a000c80c1c0d1281d2190700142c0001080d10740d00c152820350b80c0c0050b09505280050b40d440d0241000802140006030307003040725545118100c0d1803610340d18400000c03580d600b008200c0003400c5c41c1c0c07001651800d560800d442050ba0200700907002e1203190030390704003100c0000304580380e4550600c0c00365114240c500040d07091860240010b50f2054545440b402501000300e0f2441520100c042110b0a05491075000d41e20452a801301402c1c0d23800506c041004500190009540644004c050303038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 38505463 1250 38504213 38504287
    0x305100c110f0a031202070b06060a030f05010f14040e0a14030705030324040c020a030f0e040608070603050f040b0a05070e10030501050103050106050702030307080c07030203100c0201061a 83
    0x600c0c1c1003800010344143d5001e066a4014190400d08148050160340810b51801c1459100c0520000000c0c0070180520000506a0304017803081d07000c44100410043e046c411960740c4e4002c81350301030082c0152582e042505206400303600d40f6100e400188044140a001074450f00c6e120502c58004e2030040c0742680c0401c0001c0c400140c406d000a6110304030204601e0f00c0000e070040d98240b121151209103018a2508101c00030803034000898524107036240c902004a4100a04200c1d85c802c1481803a64000c0d003000c5000c03a0360400464000309a401551b420411a910303521036010214068a0241c4092002c001040f40c0c2002c40c0c1050f40e0002e424201002a8100d000106a210001c2c15030480013a613540014406903a0602456004013280e10340b641c1044041c0d00000d07220310442c01c0c010900340c0b00080400c1c20900a1149030019600201625480e26202010401400c1851003000040d4640140801c3e140c07041c03588003040c0311007820001d0401a5401e86103c1c5000b0384250168548403010144c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 38506713 1250 38505463 38505497
    0x601030207030e0f0f0312180907120b040f0c0503010302040c0f050706020a05070c0303050304140f0d0302090a05061204060f051005100306030206030108010c08010806040807020d1109160f090305100c 88
    0x42034151348001d5016a9040c40b586240341c08e07010700003014460340800b024441a030303a2028004900c1c0140e040e0000f09060301e0300001e4028608400c0700e15a042c01e06444001194004010310b0480703009940500841d4881c80049440003080c28042c1d000c50401d002c00300214000e5805000b1030500c0e0300380503203050400e17186c581c0e0349c02aa034400c0700016000030811040101201000080c3d0608030020800403a102125a4880c0902c22107102019030100b60300e0020355408034a4001800040c1599547d0f400ca8040c901d076511048405440090038041e41c034842e061180300d454440d0400b06584c070301e01810442000071030000c01568604258403241c005c0007583d1000300a5001341607420000605d43c071640b50151a00e0416801410103801c20410403000c100844215500d841e030488400798214034a2605100050000034243c0d0030a10b110100120030040c802444000f060a071684070602000034401c560003451400300401c0fa8001060507080e030002904020f4500b030039400e00031240301c071038612 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 38507963 1250 38506713 38506723
    0x5070902030a0209130507090603021303020d0b070f0e1c030210150602010b0a030807080c07120605040204060b0310030602030603010905030f03040209010f030b0403050306010c06020c0a0201080601030207030e0f0f03 95
    0x841c88802d40e0000d591551407411031200400b040034144248010b1420319400350104002e8032612050503000151001c40700352040c1008042c5600821203245c0c1070031030400110032042101d101c4041008403400083d114000c55a800b10080014200d0010750b200244985a104140e8021800c1d803240449400300709c4a1405415080c10401001d03155035407420704001c1c20f40c3d01401095014052280c02440455030000403185919004465160341d4654056110714182850b441001e10100c1c40c0900010480c3c0b0b6000b041c003d0780212410301c155a1100b801c50001c1c44259041c510000b110802000013601c0c9401450340184010000603031020b03107803117040c1981d004015000002c03400104000071031034404501800b40c4101c8405038005402e55030f4041000c000680090140319010001808981c451100038101e00e90103202552276a002002459880c281284102d001c00d61400000301c0b81c1d4482d200340c1d5101c0b6050b0341c1e941c400707200400601c491590302c00c12982d08056000c451280d030b034804101c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 38509213 1250 38507963 38507971
    0x509010306030b1503060c040f09090c030b0a06030507090c05161b060c060c08070c031d0a030b040c050603090309010c0809040c02060106020c0f090a050601031b0201060501030f0e070e040507090203 87
    0x1041000d0104c15504040c2040c000400d116905042440b0500c4440e11861820043d1030f442000094101440e00f4001c01c20001548018200d200c01c1c0204000f14206400c00300c01c8912410844000035151001ca10958000614000000e24140040c1d80c1c610358150114021500074009020844111360080d003d00d01290060300120308880f103880300304420391080c000010302d5841c0a032094100414001c0609000010140c03c11801358401d1900010400c40d0a807140c000500c8071141c2540c92400104c1c0d11001c0350309996181e0324060020303003070401408892082c00c582000c0c1d45002888030054410360f94071102a540c84100344100e001c2500c680c800d2424003442a0010f00300b661500ea4003c0c03401d00900c401c030f0b008500100e0112010f03164401c801d40c200c55103c0020030320341d54070b0300102d004004040f910103000d020424113240d141d4044d44203c09640b02030303900740520f020700c04d0030b402503402e807902c2c0c213070958056082001480b0340c0c050680c0d00503115106036185107590380b01080503a04151 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 38510463 1250 38509213 38509231
    0xb10050402160309120b040b040809210f0c09060411040b030405150114030607030203072c0102070f0f050d03050c010e1b1210020a0306050405010305010222030c03030509010306030b 80
    0x1500b107010301d030300045507000500c0070344c0d044c01c045100b80c0d6600d10500000b8200038030491011010800f040310840541c1d0300900064615422803440304000c0d05401840760b44200070340036031031480103500c0c804202408015000341c8804403d071501e106002c001d103001883d14176602000d000110b0b82008040003103020324002c1000b050002107582034030f0420007040c0c0c0401100c4c41e41ea032040c0000c0e03c001c5441640036500b03050040c0c40b555800019140401080045045500c50120310900e846804502c06026202a070032a0011503c0c1c8028541c46890341c0200d40383c0c100c5001003003010b80341150989885034072900c0e04604014a2401d128255069250a58019040904804070700c4514401c0400c0c80d00f400c81c0c82681c540c25625209481c2c0c111f0754007038840d4540014540704014007030303003050000344400351042040d5030392070030900e00030340241e407401c100e10084482d40104151050b507460103503504400c001e50803d1656405844c250b1012035418185922110f000001c00c401e031807414401d407060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 38511713 1250 38510463 38510497
    0x108160515090315040b07020a1509020406030b070f030b01020d0212070503130909030f17070c02010908030f04080106050a1805040314030c030411030f0c090603030705070f090b030102160b10050402 87
    0xc6d20b400840610001c060f0400c40d88181403120124040750b1441c0e00540000c24000360101c1d541c00403c0c06091070784c00c00b4000c2c0d842c00050005107a802410307001295080c4d0f60401031554140f00481e21210705034003000041c0d1180b4812017050303540b80b0041c42c48038441d02c112403501180c403c80030000c000c0c0354003120300190b1358841d200c28980c06c8442104480c01629103680d1f5011460711424542c0c0019000d9020030088140160841e4020720794040034003030440c203e0b030b1614481b2440610300c2c3d1083c0107840e255424042c0000701410403450105c140c5803001200c0050400006001005000081c401c0e0b0812000340300c010010f802311402103000d40a01c02c9600e54034a861b0400144145500c00c0540c002d034401030010b003060300c0205c0e00c101042c404031404003141d102c2e8400607183d0b0040710b8000e8020300959400249c1100071400c89022034114500501c20005540100b600301d01801820032121010b1601e807400044039450001e601002d1181050b0100307032282c0c0850103d820070402c4807000030030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 38512963 1250 38511713 38511721
    0x2040f1b050c010e070b04031e0501051302040b0910030825030809010b011806030905030c060f010302030f0d020d03050a180813081207140a1b0e0108160515090315 72
    0x280100380f40c03104d001d002451800c2ca0012242018469444081c0c6031030515451700c50b580d003140100210f00c1d40c020340280040c1c100003002110040c0f00e0a0300301d100310310f48411160345080800030b4a105010790350403d00c88518646400405912020082c040c011800e03440100200741e5000101086000343e07104041442d142d207400d803c41e00d050010358140600c08038420030b80c0d90038080342e0f02940c2c0c2c24a0301140b00c03520b61600510b14002d40302d800328107000b40800c0010444410041c14100c0b0300890490314136421825a140d1603148a4074200d005070420300b1440354842c040d270401d94010f04c06840018400300d100b044000d4410000c00201d42d40e410001d02c40032110f101030f0b1890080d041d000c0c050100500030007050540b034800e081d80100300c10914040c2d41400c8005101e03461103140c1024160b0b4a5a001020300d102080c040d000388150601c9120000c94111400200b0307504c200e0380e04015895080c00c00c01040104200501030300c039844000c000000c02a1002d22400c81283c521401c81c4402e424 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 38514213 1250 38512963 38512987
    0x4090609020310050f0a0b0705030c0c120a030305071e02010b100207060813020d080d020403020108070519080a02040801060b03160206071209060f05040318140105040302040f1b05 79
    0x6596406580d0007801801441040101d5400510481c1c0e003c460070091780c0d020201103200409698440c0c218000d0110f129030034441c01000400d0b050078000c081e01c414a81c00c5042180000000c26044100d52100800d280080d0095104540154990800704401040340700c1c884003082d5400e14000061351250301c040c9203800c0403e030a0114070404d0000c3d04025003030220080c05a0001010b1400c0c000e5626844c10640d1270f41480031300800e400c02c1215640d0344401c40040d0107503002e84403c074001070030b82000412542c440c40030780c0d0b41c0741c0e04d026506c2c0000d041c803141102d0b400c0340030f081600c1c419400c20000456850921900d0300400344403200f56228a03017601100740e0408c8500d004c10654000c14200042d46a0007114800c44403c6c0680005841002d81400c800030f004001d200640d1526000a01050540010000ba00220303880c060f5001036446880c4016040600452180885d406007c10300052500b0341140d220159006800200d40001c010749095141c00e409038100400c00005009400c14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 38515463 1250 38514213 38514221
    0x507060605061c11040306090503071101031505041a030d0306030203151608090f030315091609151206031101090f0f050d1509030e0a12020d060905150103030201020409 74
    0x1000c64005080003040c1d640342410b000b0400310016404d070380d034109240c1d00c0d0400c4d06540155800150410000318207282850f0383c1d0f8040041076441c80720240102c00558824020808808150980c09942c00c1c42c08040c080500b2200400b070680354a40414081103840422528501207851b81e8013040c1c9610f1030042c141414540e40e11071000e00d146000300701c8095404c0f0001801030856280c0035079a6070b1340c070100500b49001080044401d000010074050716410814043d03004010803144181603850b0819020a1611000b620700041007280da01084104460301a820301e0400324100841c00e9500003406c0b00480d250343d0400c030703549201d0328000845035901032891000740c080c11005050103411714614509035403252007054030078141c40045034104003820040c055008000c01051103000b01c649409001450280340d8140900000240004d1141b80c2032012400141c001c3d12a030855102074545002800c002c05064645120392003245a0142080d90400d00039400f0743d00042c2ca0300e0900044038151 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 38516713 1250 38515463 38515469
    0xa06030207020609120a0c0f0e09011a01211b02060f0103030c0b10211407030c05090a0b06030f06030c0109060210050711010213090f0507050301090b040609020a05070606 75
    0x2510601c03a450041c1c07030307000c01c0300c0405800b02c50418510442445c2c1d2868080000b20003009441103520005070071440c00d42800c241c903000100d1a42c1a61900d10b502e080340c44050301260307200aa1114060300354090030a1540c0f00000c1c200c0030302500328980c2c0d814140da0405a100508a50000d14490400e5060088030b4010148020a203031551440d100242a1040d02c00050603c180f00404145803202440f071401c01424003200c810003d03542c1204600e5080c010781d100303680b0b207115076200128820b0701040180c2900e5001065649841c1880e091203410440203003400c0e0300c2c03035681220081c540c0d907202c0138611944001003c810380345850b800345420180401446410701c0003461080c400141c0219101410380201c43c40080c05540303841003101c0e986104088910194400280c4000000c480d8030000155104100148103045080d40340000301c92048a104000032024001401140c505070401d01c0501d60041011581301d4480030102e0480e4011090701010a100040120411203580294001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 38517963 1250 38516713 38516717
    0x30a020705040606110a11040b1201050708101d06030102040504090b011403030a1b150e0d0201150e060d08070803130b07090503060601030e0a0807030203040609090605060406080a090605090c0a06 86
    0x40c10313240018446c0d80308080e40b0014031034014868691015105c9500c02840c1c858000c1464003e0503ca2400c0340c000c00060783e20000003500350001035004100d00e09001c04941c3c40354002c50b511158004100b0030045c02500b0b050341550204030000c0d440d039440c02a14802800b0780407645082d490400d5401c0119000004c0d00e000380c00074042203801a810004000c4207200305801501c60300343c1842c01c00c17a03051040d41c404050304e03d0b207030003000d841e50009640321030003100d80c008000703100c0450300a000440040c40307100b510307100740e5000070031a00b09613040700c0006100d141814104001d41c1c0e00c403000da0300f045601220002c00c050070351042c00700d200314070360300407085042c449540c0e070800007c0b0791942c1008104a05160700c405c034101c044035040111081850300549069144e201ca441c000351264010310480c000076600c503202281803c0340d8850b1a04031100103001d2403815241100c01d690810008020450450340c448074040421194001e01c0c4c441c1d41c1900c040c111f070010800c00c000b0000290742000301 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 38519213 1250 38517963 38517977
    0x10323010c02031801030902100207080c010302040305071401091a07120309111c08040801020d050106090f0603050c040803070303090611070804030b04080412080901090e04121808030a020705040606 87
    0x301d468011044445403a000224590f11154070350040e405016101c5009403c044601c0d980b6070080d501250084c16205102c0c243d81e1074101c1c81d401142640100d00010340b0b55004114100b02d00d603c0440d010000880605107200202ea441404c10700b0038584c00c0a0510940c40004d2110030003075200d194840220440c10100a90400c5403202541c2442c41e40000d8002c00c00d80c3c00080701200c3d55008200079030380c03000201d50b44988900d0ba040c040d401000e060243e043c104400418041d0154084600f954900882c40c96141c0c9455002c601610001d0000d2034462001c000214500350140010400c15029440209110609150500c201c8020304290004198280071150008140c03600720740c12030f500b06800c010961200c0c10640c8840c401ca0b407041001e40c50001c4820304214101e00036015150707090301c4032003819070344010348250201c0c112802000300f80c041e107049481c40e0260b4100c0700200181402020099180c903589455a071085c51240096801140c04201514150241501400452030860 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 38520463 1250 38519213 38519231
    0x6070309020a0e160c03020c030708031c0507020d0e040209040504140706080106051c06120b04060507020c0f06030a110a09090e01110906030915040803010303030b01080402130b0a0306020301032301 87
    0x13034590ba4440c070390900b0080405400f030140740c1f081004155900004040ea41819038446400da5a070303000e50304c8040c11002c01d5410a1400500307104103803050100d60041c049000e9250800c80d111801103074060342c8258244044822034441d88a264855885003c140d14800c1d44940282d02d031046581c005020404904e00501c050742d03000d02515a240040c80c0c1c9001a601d03008111405048140c00c0f01c0c440e42000c0c4444020f002903804614061030041004008580742c854080744c89001100d455904003032546203218150904100840d0321030b482003400100e181c0c1d03944d401800355000c02e10801c0060200802444940c003035100b82e00c9143c1459000700414490a08291030b24001c0c903601900c600c1c00840001c8160300180318040450600d01152600307440c0a06e01340941e9082800154002840c01180068075402405080e00454000b0034244140301900c03440c801404954074030b242c00080400780040055994005540614415400075051100b204030358060301c8180c401255247e8101441c503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 38521713 1250 38520463 38520481
    0x105010f060e0102070810020912032104060e062403060f04060203100b0a090e010506070b0a051302040e010209010f050301060f0305131202010b150c0304090c1106070309020a0e 78
    0x284119107540c00e000780040d10603030060341012080e600001c16070040c249950741c03150151780208511201128510380078a80d070041c243d500c0c050810b8034040b01d1304500110052055040d00958441e00c104030114826a0031840c407414100f007607458001e080e045010a54100c5122052481c1e441800c0d001000702d440d210b541e000c0c00300b2000e000038101d02d500001294600106a5008000d0141401c503243c0d50503001c400100084228450813840a045800102e80351802d07104907000070b900f0800985c0542c480d28030240040401604081d000c0c104500c4050058440b4041d0003040e01d41c01000507200c81c903842c005883c0400b5114502c0811100304014401d03a5005401c91900d08480c0c40c0000c0d1f2540c2c0c00148444101501c44064a000002e43c2042d51855054121808401040d40c440103040c1c14102403884038060034008101ca0b03001440280886441c0b42d11860b60f10140d8900761503c0b607582101c1d2800c04a00355181c400194880e20440309501703114034aa402800140e84950040c0f602d0858 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 38522963 1250 38521713 38521739
    0x120307020405101d06041a0609040b0a09060f090c0201290a1d07020f0105010b0a05090613080a05060c0a0801291902060c070f02010810080106060503040201020609010501 75
    0x4000d1046554078042080d9185440b151005000c12001c013103031412100081e121958400c41d4071034412820541466001c0c682d01040c4042d00d10054002c2e030501d4003003070410024008400032160024446800010312011900030000180349101c07404820a091145460680e032800720001d09582c1010860328030006000031450780920180f48440d400f0340701e81c002501d06003042e40012031009035400a01050b401001846001d030126800300d42c8041c0c000000c103400e0740c90034895a04d01c0c0509200848240d40a08020510590003e103110f107010281c0c5200070038052250040c10303940d4022100d640800200b0040359800c012046541c604001c000300c3c000b01041c43c14000c1170f003642c103140c4070581c0251302403016001e003c8507000c000b912074000144460506070311241540061080d0008601c40d24401000c0345c1040741c12244c0c944243e10550015200103801820320b401d01c83c03003400000ba100700700303101e810302030324183d82c81568078100b5000081c44c00d400a06100c00507450b0500411900d00d02800b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 38524213 1250 38522963 38522977
    0x4050f0d0203030f220905180d05030601050d110c0a02030607090b0f0901020f06070e180906070f0c05030408010f06050111150c160f0c0b0a051213120206040606051203 74
    0x2150380e9599076010722000c4601540210b1710210740f2581800310396100c00341c00151089000b02c14138641030690441340d40e038692224110b100803070000c2012480f130754810401003c00700318542c0045140341c80c1c115135480c1c5034402e1080c2d0303815400c01e40030202145424020aa04240e5605e841003038941804941c800a200d088048400100c00198814190740240280c81c81040b400c01a103250380707490301015101c24060740150b0700c1102107000380305850b2411085a80a80c500130000c11345555807540071340311001014100c3d0b0600443c41035200005400704000c101609054001240b0641c4100c2c3c2101960096003126041c03200009100081c8a00001c44c411500003410b1100d0341516901c0d40142c280c810449500c0d001c10f00f2264580500c41110104100d00740711b0b034078881c2d406654078005086800b5059405001030010895001d811024034405070300f040c66460302c4a0700d041150740300300c40b800030710581d44003680000040100b44078052003039100903e020b8842c606d12052500215460303100c0d080d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 38525463 1250 38524213 38524237
    0x1031b09050f01030905010c0809120a0e040e010b1203040602070b180411090409060605090a0c09030b1b04030318060302041505030408091c05061f0303050702030a12030204050f0d020303 82
    0x202007041c1c40c3c0e1207500712102c42a0000020002c500700107100512030801155121514841d100c200c402c07180c16141203c5201c500395031080c483d541000100400307459281c0c034501d0150740744c4044502c00c0d81c804401500d001b03440002140e0392890060040d0800da026440203e01810078000510448000c0010745010b00007101c00003000800482428464042c1504880d000340c9000740640030080140e00c1102550000c413017075902503944402d10401e507203640003150005000700b1010000510b0b941d04840d0401c00c0f00f9800540504241d583e40d000e078100350b10030f500049100304104046200c1030920000703051180360642c80c090a000d00c01c1040300c0c04000e50300800000000003400d1018403015204550002409a802c0d0705004024000e2208504810380b5035002e00c1001c40c0c4000c190b440e55012081d00714190284082c41d6031002e844c03a40029034142d806004050342140043d56104c44080308140c50b40b00140c40b20705001c284441225590140c0e40102851050300000d0ba400006480d9441006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 38526713 1250 38525463 38525479
    0x5011503290d0c080f030904112802070801020304080d05090f0303150a080d03060f0b070b010302100e030f0f0c01030e07050d020a0e010f0302040f0b220e0f06040201031b0905 77
    0xf803905204841d1107500c00c054034001e400c0c40d003000071804001031007010011541401928110107600701c0505c10100802143d510101c1c1c1d0758803030386491034030300d4403a02c140c01550119907444900e142640d00449007202d101200264410102500b80b117900d8020b00c01c0401042d212042807503580d07983c400a40454130f80c14101c244090580c5d40c0c100d0400c0a040d2000070f40d112030100341d00c00341c050055030280c3c61506005601c0070500541a030141c1e00c3d101d420161040569180d40c0a105810705900d030031004105200c218685a6201040b8641500ca80100200f00c413070710030040c003414401c0b140380f01030406013800f2102000080010b0700fa020364400312070180080321144005001010f0303ea1090507040c90b020000142c9041e420080404c6030300948080c445140c40c120716200320340104007a540d02200c50005450716000380d1140141000d03003100300151900c4180b203400e14188010590180f142d000100700811035033305028000d02036803140e5402c1d000111042c0040d080f501039001c0d003070050f100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 38527963 1250 38526713 38526739
    0xd0806030106030c03060203040c050102030a0509010806041103040f0308090d0804060b0105040e182107030e0a05030106090608010c080106081513021603090f0501090b07060e010501150329 83
    0x820b40c0064000d60b804126540926940c0c41c08401035003080b9410703200e945c40148002020b50010048481e01040c513540e10386849900030043d1050400602040c0e0040e950341c2e440030f0100b20030300003035009500520480c064680039180060428400030242070045c1c0241010030920ae801008160b0407a50091010980040c2d000c0100c2e440c4c05154401c4030114502000e02c40115107200d038160300300c89078100b5548c05114010030084014003281d00301241500c10800c0d40c0210b40300304451014000010840410603070f42d400082e00356a9035402200d1969034070030080004107024410400e80c000142000380b0a580f42c8480038101d10401840070701c00a07a441e411540c25511071409204100702c4000454039081101c2108501e802060f0089001c591180c00110706d00700c0d10803003901264030503502c100c3c0715030421a103991950814501150b0058481c003148d88840000c0c01894003801c4c5100a0300c01c4000b80d04401810386030054541d403d484100d0040e015541507101c4080420072050301c0310b6020302d00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 38529213 1250 38527963 38527969
    0x1050f0711120d0906090e040305040605030907080304140a14030a0b0a1e0b090708040506070c06090f050102030f0c030105090402040518121b011107060902031515100201020304050d0806 82
    0x2c201102500390089050490710381e41c00102c110107503000366840008031170b260641907070383c2c100a54015010990501c003c0261070320560082da40000030805a038845030f56034008520319005900050820843c0c0e00310702c075446c01c020b0b010000800c000c02e00d0340290ac42150201e9240d05804202410004000b400110030107595000803a00c114611400070510002042a40003041c0b56050280300e40e80d41c501103481c0901c1121110301840c0c0000161940f502c4411069910b518030782022200d8507120a001008507030a50700891000e8080c40006da0340380752082400009076001070151441d1030341800140019110242da00d0f61041d0705540010b81c2d900c500c1c1450448620070850307144648030b00424550b944d07111202820302100d40752a0140501d4500280d0b0b803c0e62000f49040039031702024000000441c25507041a021107002905490140182e08c40070201903200b02da0812244131081035021140c10400c054190100700b40c40210b096042a50f129603c403103000d28040c00300110503011030400c0d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 38530463 1250 38529213 38529229
    0x10c0203041a030c120a050124020d1805090c040509010f080607051803030c010c03050702151b070804060f090b0309100b06040909050a05010605040e10090303020d0606120b01050f0711 81
    0x214510079643d0062404110351b0000d050240900346c0d0095641d40074003001c1e00c070380d506040c2c40c0c3e40710b4014002c00c00900d602240c01c3c0b14040c1071040700c075105010019080d1294003d45010740b01c4481d40c00c1d950760404090104144040e0309ca04042c0c900300300c0400000801280d0f464011a00e490040c0d0f9400f10385441240350800b0511565141c00001404410210154010b04840d0445e807814405a50b403048181c2e112085c1a01c01c0f030100208800040c521046d044203103580d0581d080384107041c9141c90300c684440340c009e0b8101e00b0200358845003d41c600ca0b00014044014a4a003291310314502d44140a59180c01c1c11032200483d0b2511080c0000d503590707414082d40d001d400e000c5000c001c42080c0e801c20315074420b01140300b84c5142d441c0041c04182400c19000e006011540c04c4024600d04071164120b0b0000c015415003a410107a0a104030400070080740642c00090000b96150031164540f1416213017183c400f9907907030b81844810094041408414815100b50301c1c1c1100e450522007121a020031220 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 38531713 1250 38530463 38530477
    0x308070513170d0e0d031103120108160812090402090111160f050405130201050313050a030e090a1e0b030102070501020f030910050c16030c0f050d02010c0203041a030c 74
    0x2003141e4041100b1001850154900c0340003021100c0054a061041e100da50942c04042e8000c143c00c4c0701040824000c0040f020b045243d54200c07844e01c802826920105402a0404007a0790001008001c07030300301c108003050207021404050491184a400403150500c00c00c02003078001ca40129030312001d0f030701900c11030000c8003a0380b068803c44926001c80580b2903c003800307940f004c088107000c08206c5003000d108061080c4c0c81c000032000b030b100302a0015101c40d0001000c00e102c00d000e607400e10001076400d108252540d031003900c4076006800d0380c10400450210003012020b5540c502040c4503003040c0f20010b0004425800c03503002424039444808030340a441008000360445d80001628000810060020341c071860303007801950100c032084c84441081d503e0607104802d0070601407201138102030550586032501d51003401c000600360200d0b41c6204064007115801c0c0c5a90b0410b038025800d00d0340a00440304a2039440c400b44d0300e013905040b0540c0040344014142c20200d200071001403d0b8562a408a81074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 38532963 1250 38531713 38531737
    0x6032202040906021b010e030d110c0d0903020906041515030905120405030c010503010b0a0302030a0f0c020109020a050a05090a0906020909100504140f0f0702010617010203010806010515040303080705 88
    0x4402c8090400b0300181d4000e5111a0b05103e203021a0341c0c101806104802c20020504007941c82c007070403c004400508940700041c54900410021109445010016240c0c0d00d00c81d610342c4c0d1040f80c5503004215452038028052401242403840f1540d00d80c08480070301b002d035002e48100c1c1e0100040c40c41d0440044c90703021001461442904c450f6030160240030301030011a0400c070f08076220300c0c44c0e03a401110b05010038450000000c1007442010301c0d1500a401441e0310405078440040c80c86002c040c102c0603502500700150140c1d545491480550074a4141140034280c16511b03484003502c2c00c4045814503030014841641d440d079408400c001c000060b0115480b043e0000c0004469040c1103068000307900b89403140d03078400da00c1d00c803041c808042d80080381c0d80b00d90060940c0c552a640e60000f294029074004080000b15540d881c000308400d0000c0d42949201580000016120340c18040c0d09403a000068008a22a03c2d0441d01512443c0c000d00071103007a20383c980307001415038413800f10540710760180040c6003031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 38534213 1250 38532963 38532971
    0x8040b2806090f141824100911040b0f090a0b0a09050603070504050934020f0c0d0204020a11241305060601050a03140a1e11041205031210030b070e0603220204 70
    0x7440e40d00441c241f030007004440845041c0340d42d92990310703003200c20464009403032007002d1008000102e0b504000d030105085051032075140031801c400241c9010301a03048910070100c00702c0c000c821540e08c84a5070300900070950312603140d03050101c40a4041d000d140310b114800c0c02c00e14002040846010618000e80101d40040c0c8404441d00c1d0442541001c3ca2261800512420000860300c08000402581e205005080c820a0000907000d1002a601101000d800e0081c0d0300111041c9600801c80107002c0840c0c6400e0010410801074241c460040c09130030400042042c01130310780412008034905401403000d08015a5034105050140e01a00c800701c0040d4174442ca40082012103403081c1c003d103900302c2540c4449402802059036440444d900000500c9144c3d005000611455003e0303108400402e0040e0112400c002450076182c1040301d08550341d03401e0b110150380400800c69405005d60f04000c050a02100151610010038503901000300400c1c151480042c1503d50880c072006144007050300600140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 38535463 1250 38534213 38534263
    0x603020406031a070f0e1011060106050406030b0102010b09010b1312050105070801120f03050c0312040c060809070e1306020f0a0306050f1008040b2806090f1418 71
    0x4044540c1003c840c1d500c020081000950061040d1a804282c1d841138580d62410080b441c1400162068490301100340405c06000615419040107118000d058a0f52030a54541c00c020340203096030701c2005a64196814020403c2c0150360306814641901d00841101e0b807129014411490921501d5021400c0c0000240d403c2c024040190400341c0700f014152504031a40e40c1e40e1080c0c503c25001110301400150171039650704e000a100d800100029101c030400c6908000c01c0310070364501c10b101641e0807182c0c0e041c060b8040142a42100210303501c5016040941080ba00d003510400b0314100040c03040d81c1012820b10b0050030807103198140d400c9615110030550700d03003440302e401078014a02c0e401214852204518a4001c9180501144200144035510906940c6440e51418440700c030280114404200c140c90317044400d1041e141c5545003070395402010074020715000c41d9504039443c22603038449060900003420001c40758464095000300702e040904480e808801c080605000c0100c4241c0c1da9094101c0f256 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 38536713 1250 38535463 38535473
    0x91202030301090b0a050d030c141e0f120403060c0201020f0a0305040c0510050d0207021f05030a060618060e010e0a170106170d110f060406141f05040b04060302040603 74
    0x241d4140c6660704401c01107072040c00c0c00c0015003d0b40380b01e107507031020303100c1740c0d40000034484d41e842d942d422310a0380c2d11021468900640c1e4107210301c0d9041100111480c00d01c4440c1040c0030800c0c94140906000900b1004500400c20a071034030076408081e00702c2c1c0e22019501000c9200350b04660301b0043e010400c986642d205500240070b44000d890564286000340c00c0811207141c040307442c1004a40c80e844e85c92403c2e100100c80001313500031580a9a20501e0758409a4903e5503180203030301007084640c0c40b1645c80c500b40c400b040884100707410540c10400d901030340341e02c4c00b0100301002c0156115820420644c0c2c5c3c842004881c90341154007480e42014802e41c0000b29100c5610303581c5503140d0044021720980341c03285265400410303501400c0b4440d51140c00c1565245010307c0784c001640304060240c8018030b61078101c440c82c042090f242220319698540011307981945414560b0b0f000114181c21040000b00104040034855403400750720b2040e96140700780340b1280d55a40c010b0004550150040c048999a4100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 38537963 1250 38536713 38536717
    0xe0f0105180903031f12030225030809040f0f06150f0c1703040c08010e0c010807020307020d031404050d0b0105240d0f0905060a0c020d0f05091309120203 68
    0x1855000d1031090094066044501506512482c860b400035401c0d680d43c3d0710aa1204496440722040302c0c4e40041021401e030142d080070302003c500903001440b0b40a40a040f001c204085015840848503a1030001d0000503203200442c0c0040400721000726680c4580401c2400810480d041c401000346405000100640c0310000d420100180c1e4035202d01c18805800162410000303140014508000d8881402c0d040781aa00590b41281c05010007045083d2106201800c480140f03034562569400011119041c1da0b00200d183d601c08000e10286007401210b03030108046407040d000050521061121402040581006070303802850020a40d2500007450b007002034481000f03000c3d45025045011250b0f114050248d02c24481560b2180958a09107140005400a01003d01c90004031307070f102c0202074045801081254028400031200245070800303054003a00d041084e83c64101400910310550002d15081300c1980e01d401d070161040d11010400c0d450200041075031503030051404456205a5110a60001c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 38539213 1250 38537963 38537969
    0xa0507050a140105070602070507030f0606180e0604060507110703200d0f0f020a0f0803090a0501020c03070509090307060203040c080706020a0f03030902011713020f091501050c03040e0f01 83
    0x1120700c402a100d41e410882c0031850100140440c808215110008075945c0c0140300070760048080e07920340381e203030740c0c030300d4071081c80030200740e8542d900c6410500c40303c02c03480c0c50200781c2c6400380e07010401c0c400746004e100c1d1500301c02040600b0a87c3c3e501d002501450041d006880c9000d034501c00d803410152a860a9420000d01ca05003111401d0100c03031038469410000066a2070541241d050080c4183c2507968102601d400b107822a00041c0300c0d540010304511510422000d01040005962141510000d01c50508e61681c4510304661000c080b0348010b8401040c82c1e015108269450f40c0c40d0703540d1400c9c1a181d48518840208507620020030031041c0440001031000b075a8104042da1103035942c40200701c0c2d95031022240984448018804040040d000340d20003140b143c41810035000c2030b440c280b82d10741403000c21070740c4030082104130812908625000401058030030007203034000240e0800c4003604040c980444004c1c1d040c400e00050040803850b0401c159001491504003207081c0349400408520402e800384 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 38540463 1250 38539213 38539219
    0x80312010806090c09090709021803010b030604170c2b0f0215070e041d1c1404030611220e060d2109050603010803070b061903020607060e0a050705 65
    0x20001103014036000c074005000d03038111001401c21900c084200030b4100005800c0d0320b1188190000000c0303100a0380041d0412001c030300421107841081500741402d4038208647c9500c2078200d081000001020b0052030f20b54a240d140003d1348487c00085550715180c410010303001e80c11b54000b0f15003100d05418515040d000d9440d503400e1000f03150500c05030380c0d400c0c01c1100342c00d40510756000180c14520031030081c1c02c00039006102045104600b419500041001142261a90024892030084920b5544d2900d0390303810034075060001c0203841d141000302d405140402050307991590303851003290072000c0a9134a9201c6440802c0407901e9082181055030081e40f05a02c15100d01c500003c4d428581a03040302c0a060300318a21808428280342c4042600a04240d01c9003484001074000c47d0702e880d10406540a801d102d0021591505642400300700c0440003804944204c03031901000a011401d290a802100d9041d600107403030b00220719141001d4070076111200428031030b0400000520130f0028a5a044031826 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 38541713 1250 38540463 38540497
    0x106090e0d052502010c020603040b0702191a040203070f1220090411012105010503190312090f0b0c0702040506030606031914060c031e01030c0303030906060509010803 74
    0x1032105891501030003240c26000f20720381248003100e80340301c0d446406052051510503c0813001c3d60000b030440e0030649040c3c6110030050304019601d601000a01404143c11030b150411559070356039180d04100030410740b940c1c14242004502151005c01501029009070000711800c16100c0b1048001c4214020050b22441d0100d501121a1141d640100c00b45040c05040300140d9500c2d91140501600320301003d40c10021910450001a20292443c4203485103850780440c1c154504000c05140c20704104580708201c400035440c100090300f02d03001c012b56806040010030302004034140503040b040c0c030b1040684103007180c0003044103052f1204004c183d840d20881e810001625040285079880200701c5100d500b6910181641d40c1d2032400f170302038601c1c10744079905285100826401090030700005403043c203900c0d08080300344114480c0320840025040548100c060103076265885d68003440d4401e21014090503aa400403805002c04c90b04100050640907001d500c0b6541d48005041d604e80c800c11250100f8410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 38542963 1250 38541713 38541733
    0x5010506091e131b03050f010f0e0c0403060f05090114041104020c1f05060909030717070503070c060503010614040f050f13050f070807030c080406020d0e0106090e 72
    0x150544200c00e10141039121440042900c41400660182e01c49511025000014081c02224010350b85036290440e13131050341401c8400c01030140c40025011b4100b891032400180840046100300504071212000c000c102c6455592081d9444e1050360009070203a820304002813004c40c159000b080c010b040060003000400c0550303c1c3e01d650440203503402002011054880c0005140a802403c0324611369001e54030328102080302c070b1401650a0200b42000d41d25901000030354a49185229817102c2c92401852900440b42c1e030b4228030b0441d00b032000350480800f0607848248003042040c5c900195001c038907907039016156013000d4081e4000348a5032000403010700541070300030050416101200d02c100c00000280d4200410414080e80340480943c2202d00c0c1c00e00c00d00010141d000c0c080c0526800480c035141418030b80e1008001c840000c0c42c241c140741c18010300e1300000380e024200c01e0307104e03400c10070040e110601c010030200600381900d00c1015541c03c006011070b404845078064007602c000c48007201c4001e14 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 38544213 1250 38542963 38542969
    0x905040b0109180311031c0f0605030303100302090c071a06040b040216060f02120103150c050c06190e030417010c0c050d0c0507050603070f0f0206100302130608060c070303050105 79
    0x80d034400031225180d01c0c050f01c10002805085601494580c2d03d00352810602001403031001240c03102c043c80c1c5031036180c5041c010b504038188103900c040d00042d0003851840c0380450003c2c0340c0e2901c07840024001e038142d400058000e0074030800d40300c85c5079001441c030341e41c8504120300303421000c8280c51a52041d0b15024810328245014400c85801c9050890307088001c0d0383c0c688404000704089001400926003c115402e81d450900540a02035442200c0c0d50a100300b5080620084850380d80644c02444810011808206000650642d00441e90700c8142215076801d92000f024013090407174030301644000b04001c21280550511980e09203598802000f800c00100c404030341080091001030080c1d089000303a000c565100d6941907810500650071600140d94510100c0e06a86c0100e42180c0052040b5100031100e03032340001082021141440180b0b1380d4185888039415007400c0f84402403064581e0130343c1c0302c0d554000da04000001c0840f54140c814501e0544442001c0b9071110380200c0c0000e00d007000110b5589 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 38545463 1250 38544213 38544221
    0x41101021606030209041d0a1502041404090f0506100806090102120106080a0e030403060b12010b130c0e090106020d0f020d120e25080706020102030f060607020d08040905040b0109 79
    0xa403400c01d1070300000b441d0550a4000354007115405400ca902c03400a40d450400d4003030280c8032107860300020310901e040c1c2d061211620341c1d580300e043e00d60340c0100000c2100d080b019522022808003110005414406032a0501103605c80c2100104a4050b007820402d90fa1288602c0c0c204441074030007601c01c2c84c1d40d1003504070300301d10441d0122401d03500301d6001030115510401c0c11075406080020001030315000c0041c02843c4d504664822a00315488114504d041d0900c800b40c50480c0d61030000038486851000001883e20414403420301c03082d5998801566000c0c4100d40200300c5800207050001c4650311404002e40703d4101090b500f02065003040204281c6100103076803000e9100c1070792600001002d284520002e0154401c00761014800d00d10081903420403540240c10000c102e4405402c064030b8140c0c0c603410300e10654000300969106008000034464044a219884101100d040b95200d01906c001507040c00002300c060440a40442c020a00d0b141c2940142e01442c0030f0320074403503581e0341c07405070206803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 38546713 1250 38545463 38545483
    0xd0c0201090c30021c03090801090602090418020f0105030a0b06030a0509010b030607080c070f14010509070906060e0607050f0601080f1b01050901180512070302040507021204170703080f0304110102 87
    0x1c001c40b42c1d400c1445225041705c42007080c1c480c2c174040c0400c6030350b019103a0035911a1101654000d5000070b82c4031203440d181c4035604140c2000301c0c0d55010140960000350460206013129818010000001024400079138002100c8000045c0019180c2c1009030104006180c201c0303040060707601c2c00506d02e0992500180180c800d12542d036410a05a071130104002494101c2c100442d42c1c680303042100c10010300500c4403000c0c02074400000040324509240d8092400072903901440000d880c0020900c00c45a00416031100c2840a40da840e42c3d40000b031401d03900e0b000001640e0011401400e002083c1204049480d1503854480070884100c019000b1440095007540403000c1d0114030204040402c5502a180120915400c2c040b00c8540703e9132900400e484400b000942c810341d40017598140210310305403084580015081c80100f841c0040e800848046210310b0288001d031518040380403105510400c00400610b40c0520025291041c4580007030302600207550440d24040e40104040d01d40d40b00056440034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 38547963 1250 38546713 38546719
    0x5010603090b0c16020402030406091b0812160212070603140f190b03010e030a0201110301050603040212010b030a080702030c0301050702030d09050a0803070908060109020309030d0c0201090c3002 86
    0x101e0f440c2e16200454652200b40740c07507a0240511016030169803244007462045020300d0f0f0104500500346409280071084100b010001040e840050224100c0003450b4801520042c0700b060703403803010900381e101d0805010002503000c2441480d0720405600130031020112a01038505000707480017150241102d080480702000c03c01d0036600010104080000801070703283c0020323000640c158070302c00440c0c00e59003c4400310210b94000100d07110303110350900c80c4040b24482070f541d00d070642d410817002a810f44006400a845210044040014401d0039444815840c000504881c42c64081d0302d400e032000c0d0004c0318140c0c0f20b80951114402c1a080600800d44515500e5014601d005a265056001015401d07001c1d15180308842c500b000082101c401140111010703200e403c0d001d4075040ca80e501c1c0410507005050402e00500030701078a02d00c00003d270f07406c40f0641c402c08641d503f00050201c0c010114544040c1081051410014821150514041d6000c0b01d10310707001c98060340c01c03100303110f0358010440c0250 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 38549213 1250 38547963 38547983
    0x2041a0a0f1d0c0d060b0c1005090c06030603120315040b0f031e010b030f030d0c020d0c12030b03061306060501090302090408030c12070203130609050918010b06070305030105040501060309 83
    0xc0c1e544464104a035000190f4070700e07982000f9600c0a140b04591003500803400e01d03100002c2171040030000300300d40f00c140a00ea00d000e0200d89080d40d501c60b2140117420342640980008408030301603507000d010b103c14061012600381d0301d078036004111061301a10701c503030540210318000c02160181000c507400341240034042d0050030080d0403001010308200300b03020f0068281d503a1710740784192658240300400c00f4a01800013151240d280341805c03012641d0b80300380c0d1010f65001c494003002c065000b041492190703400c2101d090748090014402d81c05481428252076240c0640420070806403034500b450200c050085c281048400d8651005480380019400301960203920017001500288605c002140c0c0100580d190500380748035502e010050840982c3c13081c0140e000403600e0503201e296040c0000041c0710a03d415203a10340341501045000c0c038007a01d04100345880340b120b56070504007500712661004000d41801d50718605800c00504e41e80080c083c15110314245400042c0041c46030042c49003003034100c40955 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 38550463 1250 38549213 38549249
    0x2010519020304120f12020d05010e09160b03060105130303050307170919080d05010e150d02090604021b070603021c0c022a1903020102061803031f0302041a0a0f 71
    0x40c654003c400100401c101b0103d9110b03034200d40500140c0060441c00c40086090b504155143c0c0660350002c0a201045d4031000b0714841c80d82c1d40c114040c0848440000b45550703601c172407004070b030540701c0e00300041340c0007411800010800d5440360046200c7c017065550f0742505220766019085050068031148642e40c004002400d030702c1d180503503241d5018400d0020354075201110f2a180c041d00c00c00da100004192041e01003110468000703443c0d46001c442250750903503001c038603030000350003c9024040502035a4007107240e45010743c41c03441c1900060715402c1120046c99991800501035481201d01c0c400d8040c44288040c1028a2400742004543d05030700600f454022180c0c2044e23003082c040c11941b28244152803048a951600a010320035403101c0c00c0c10034100c5086000291030180003520030105c2c0c04000303d130704180b01004020780350804081082040200484070280301c010750b907034001950140c40c01100c207030550888064490001c0080da8201c601990703422100f0983c040300d22031041d25101e521195 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 38551713 1250 38550463 38550467
    0x80c01050d0f0e0616050403020102062706041b05030a02030703020103020c030d0e070609050306060d020f0f031603020405010e0903030406050604020c01020a090e18030403080702060f0a0201051902030412 90
    0xd0040d0720420400041d2070008000d00350183c40598400b82101e0700300109100c280b42c120016aa100751640c01d00c245424070710b0f40005d54070340300101200c000d4500c51b403040d086589160005140724202e035048070304d0b034201420a0401c09081c2c0c10300101680c4000c00004403414085445403940c1c0d00140a8008245140c006401a61050004034810700040001016401e03151150945524904008000083c10514081c1802c900e41d08074600c80ea03c160704102c8140d58041840d00105c0c0d0654914484a00e9240410f141d003500d04a0198107002d80d0b0303001001c10703000304194400c0340d008a8007402142d0380c800c1c4156001109503822211600100001030104016402094002602820041c0380c180000c03450341c2244c00c905c0003100021148402000040c1034451030a030011003000e807044524040c81101503070b030320482c4001840450301058000a541c2c0e03000a8800c1e9070101c1107065910111000001d00805040303503440d03500d4182400c5401006524425203201e19030004525000040441003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 38552963 1250 38551713 38551717
    0x8090405060301021204080c240a1d07030614070e09070c1106030106030504060b01030506060403170706230906130b060a03060e010e12130b0703110a08030402100306080c0105 77
    0x2103282c00d59020407821000b081d00c44407981c803650041036415260804600d090382488925520401c40c46004210f80d0032890014402c0354202003e00000030340300e125501c043c2014005143c003542ca6009003500041480300c2c0e07803c40e050101c240600951640e9900e04186d652401d4290a9070b0070500c80000644158041d4060540060198807004081c0780c200340003a040e60b10903040000000d881c0d00c04d1004001036401402c8005109080c28087c07440c00801041d007038051840041d2400e05900351f4100424031040c101c910b0990450024820030920a10610500c1c01310221a0b032207080e01030000c0d007809804140e05000380d0390b09041d8801110307117840d084000000031304070950007203000c100080011031922410720b108590100200e4444100d04415003400703c0e1541101c504035040000d450303450700c03004030481a01c14501c107441c0c50341a241403c5607900c00e043e140c5030003071081c16215824482c00c81c0181d8425842103801c20001503c0c50400c03010b031206845820000d1740a0b04c8240d40325802000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 38554213 1250 38552963 38552971
    0x60f21050a02030604140c040b010509060f09030102030406021b010510050d02040e060f0106020114060a09020a0516060501031e0b150d150b0a061403070c030512090714030a08090405 80
    0xc540750491036400090800c0c2e4161030443c2c80c43c5051540180401062005201c201012241001801c2440001070014424107508910402000a00c0c07030b40c1c1c1507420252001d50102070021501c0e49020f11b01900254031090500f0200f0301c1000c441d618100b01405454401c100e10114030005501c3e10060080d4981d000303a04981c0651551820038002c0810000700740300310740303150b600a440d5241c810003a08484800f0f007141c40540e03030746003040712030b46682203658200da500c40d0300141c0d03408030140700711081e00814207982003e22030400c01c0070a110913500580d0580e80680800c4072100c40308207410385e22909c070b50030003000c00e00c1ca04001a20a20a180311501003000a401c9108410080c0e44042031102d05512440c48076035280081c684508007070784010090710b8641880008200082c580c1c46160000038004420032548004d2001058801c83c151002c01200414542c840d042410030f1589404590240403002d1011360103100b0103140001d2500c8107190070417402440d210f140340510001e080700070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 38555463 1250 38554213 38554223
    0xf07081f030f0206040e0a0504110a0305060c030702071505030403030b0402030601020c10030b0402161e020616050304090e06070f030b011b0c0503030a02100b01180e100b030712060f21 81
    0x800001480445d240360641f18003d41c00001031946424075040721035100441d81e0b03c0c010700c00e450007440040c1c000150603800407045405a6169612034408916200403a08803d0750340f080320104a17002504070740511701840c8281c4050150110450502049000460708030740164400780003240107040103864881c40c10b00d54600880d0010212000c201030b80d0052500c8204010f1b4604000d082c0000d02030850798051141c03c1c0303000c42c074082781c0004069020b10345841d400e811492013400204482041180c0040404041c10702c1903030307841a48035468250807038221021440c0340c2c2e000c2034140e10a1040d20100b031016164100084c40d0412000744900c801c045c2112082c00c80f44003c26075135030400127008000e005500034442103d4514043c0700b40d41d0303040440b6041c03041100b0001c014113000748101c41500c1446c0341c117041542d100d0102c3d04d55098143d206070744000002052204c1d443d80f000443d01a001c04000600034995540b84142e00d510191003102401d4190400360304120b4240611051603902038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 38556713 1250 38555463 38555467
    0xc0305030a1a03120406030b040903090308030a140f0a0b0d05030a0e010c0c0b090315060d03050c01140a0b0a05060f03070f02072313021e0c150f07081f030f0206 71
    0x2070021900d0041d00c01c3c444e20180348082000c121090381402540016002600e090101c40d100740e501800070801d030300004060703074804000640440c0c002e0780152440c107043c03023200081d0304001504115a2009903050402c682c00c0041c03800c01410440fa00c0c9001c55403000056281034048002101c0c80b9042d1040581040004003552010030b03058503004000c0c1c44111074450303454800204145ca030001801207401194000b404201441d503c02c14aa4803070743d010b080041d0384000c0704504600414003030004841d061031100070f00c000080a0b44c04a0940c9000361161130080c0d84030420454070b03009441c20030b6040c200070000103c08500c280191028000580105c3d2065030703d40c54280d110310003a00700d2001d25140d010004080c1e1030046d0301040c010b03198032802c42c035001c051945480d80608003610021401c00000349540200000c1100c2d03145400c2d540c03049403460412010300310b001c26055540c1400a80040042070b1102c410b00302c280815a0503c58031402d4600e0765480c00b80030780c1da030070050303a22500c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 38557963 1250 38556713 38556761
    0xc040c090503060a06080706020d020703030c0602220305060114210c030703060f051326090a0305010209040e031204030f030f14100806060109030f020604050607030512070c0305030a 80
    0x801c10a06010b40c007402c0001c1600d50034401003c0c41e0880a5010404550080074400ad020ba0003144007810f0781d0305803805250310a1542072290192148580d10031542081242d410000310000345d0100a4a1180080d501140d0fa100c1240c03118240c07a01c1c1d000d45c86040c0403c1408440442c10800c01c0e10b42580e019968001c3d00c4000282c20071403150300c01d0329000e4603444202c2090703040d8420903038010229030188440400c0c0740c46241c00500003004410040340400d694203a03501010058610308100200708c00142070b01c070729029000c0d40003005540d000382d00b040950881000041b00b541d520204094045010b03680d075480c100d442d00c84810380f40050503a611800c0c000503186000c0c1c003603600f60425013400d49040171040d81c0100131403540010b09542103d81803001c41d07a8000c4c1400c04483e000040058080e48a000041c10f910550b4842e640c0f000000030b14108050b080fa010340561300104e425000b1a0340c0300c440c1550300020303500300140014010400540b10764150340c000f40407a0b5104010b9103803804 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 38559213 1250 38557963 38557969
    0x7231812070312020307110901061d010c0204180c0e0103020603060105070807230607230705010b0a15090807050310020a050705150a0609020c0303070c031112030a1d0c040c0905 78
    0x52400b050f001a040014000f06100c8443d080300403401d01aa840c502640c50520f0040414682c2002640c44c1d038401840400141c0c1b2030034480c48641c1c3c000307100304104003243d540a0041d400609044031181d41a000001e01003440700e190904a03500500010724680d02d55004440a0307014100841e80d1030028032070280400d410100e06080c1403814407030b180101c000a182d5030f01c0c3c090014100740401030051889005411107034110000c40c00e2604905440b0001403a040d40902001c802c03040d04078031029400981c040c05004071059680c100e44034401210380750a8090740701e50850150a40640c8402b250078007201c480d41c01080d501c05035280560030604603035220b9003081d107100c40702c20b06a860703002030080b2a040c0d841610000c1c209080111301d001120201d05440e800003e01c03507014802540582000c7c14001c924000503901c510098a8140740c10754100b103015002a50b400101038902400340010121a04045c4903e925500080503409000c0041002506044442c1002c00c84034500000b49a2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 38560463 1250 38559213 38559233
    0x4050a0c030803010608010503010203090706031805060c0306040e210d0204090903020a0210020106080601050918030a051903060303020a061104050402160501050a05070f0302030702070e072318120703 88
    0x1600c1102d800303a8075458400000e01038a8181c00051107640304000b8858041000101c01d01194006c1c20042041c100048105020121892000d00795015050800445000400040d4401d102c222420001c18240d000101d0780c03844818010a4000103145101c415981210050445084614030151616444c0c1c3c0f004400e90b4101ca0048001d80d02800780f0038118580090800c09486562008010701807425020135602c4c6d0040c03160500503141c400210f511000c4118100d206001d001c011a955080b14201c001d1513a4051004000c280c082c080d00f00302c140380700b030040000310394065008002c1036600e030310b505009040d19040f851446a0400c000902e071340701c034000762500a1010104120b0507100f401e240d0300b91540100500e040900d010104801c591b004401d00c0314131100351a00586aa031a0700d001d0b8500340c03094001a14903046082000440c0b035101c4214004440b004d200f4819002403010301000c03902611465025541e402c444030105400c101c0d03228204100a00d0489052aa5945070040c0e00c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 38561713 1250 38560463 38560469
    0x905010203090d03050c0702060f070b040f05071a0f0a0327020a080105060901030311070306060b0304120e01050d09050c04020a0504030507060c152301060224010b0a0804050a0c 78
    0x540d401004100003210180050006001e060406016a24019003809a42c0c4103155000380309a00c081040c0142030510b17420340b9282c0703520250010783c600345030408814010f0110b5080398548203840c004a503d20141c00700b0003402c9448800207041000d51071540c1c0750f64220300d907403008042d0b0710a281d40c09080724400c2c001c1c4031000c03040c1c0c02d2030348400788c010320110071034030b8120100d941c1c141401c0c041a91950740c529411030b60149040f50120300300c0b40586061442941c0003a09050425102182d01064800194001c80c442d00101324103d0407001c06030f40142c00302c40c1c1c441c0460020f21016101c544a9000b0043e0b15100340b098a200d0380707166000074200d0700002c0306900080d07404203092042200400017000545032604000c014000c9650716445a0420301e000c07194040d441b400f5084601c0d210500102c40301e80c518004110320368603550020b586140c0464517003040c605000700803551800000801d41a20070b900c10352440c00c1031451007642c58040142007100c541c41030508100101d0b03010031f00034010b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 38562963 1250 38561713 38561723
    0x2b0605070e031e0712051216050d0203091c020a031203060906090c02010b31060506030f070906030b0612090f060406060905010e150d0204110d09050d0509030a110607020409 76
    0x41c3c00482c602860202d0541161003801144000c80740494400034010000c99850483c81384d40d95005031601180c2141408001e100344240f041c03e6400340d0300800500707089101070340d0658201e0f90b1041c14040b41040240c019420584101c014400f081000d135042c06004500d04020032925501d81040080303907400e03030200f050103071307030f0302c0c000302d41350340c2801030300c0c0d070424112208808110003103071000c8009950302d2100401078110792190040c07075558116034000c00004040b15140d01d032010840402c40385c00c5030404000b8114102c085846400780c801c40304210700140c0201e00b403240107040410001c0002e021b11819102d07021058070350410400c64688180d1240310042541440d2000700400d07103078107030031040c60038000c04e08101807004030017951001031500b15507001d1040818000320b00242001c16010301c00200004103a00f210010790000515503204000725044c801d61200121140d002d9650f445516801c800403003400300740d0a6401c1c00d05120000d081510b040156070005040b41c0a581c81190 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 38564213 1250 38562963 38563003
    0x31602030c0d0b07050c0115080a0b0901020c071e0305010510180506010507020103020d15090623061207180e010314060103020a05040f1d03092b0605070e03 69
    0x2141000d01419141103015034601c25804520754031509031107402005a81007080c0400c04846e605025001008038454201c2c00d001c44070746a0005e940c03214815101904c0c400e100038049005503005100711030190a603007000c0e180c40da0401c000304000156010f03651103540302084001c0003065081c41034078081c1221404c4031144500c0c2042e01c0304464890380080040c2d83c03420302001074998120f011503040300e90900e03005a60300c141c41640001442c0e082449410100030800c042016081e5501ca242950b4280344465042e5200344502d41018020141c0150010402d010402212000a03140342d006205824003003c160145c07080e4544a508540c0000716049041c0010814400c1a0a00103035420311a0068202581181c0206040940b41e1103038900650755a01645407101159018449850455515120121001880035034030707000020b400d40320300344602c03088400c914000000882c441101c07520b200008200c0d21440f008240c01070101050041c40744808205503414000c0c804601c2c400110f1070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 38565463 1250 38564213 38564257
    0x60c0706020613030f0e0103021207050d0b150a0305060a090504050a0210031418010e07090b04050c0a09090c0e0306040c03060501051017090f03040303031406060301150c110303 78
    0x30b10300329010700f0b0702504070740c440c050202190b80075090601c0134a80d0708043c904854a20300480081c802c50030900180d03203540080c441c0c51940000201141900406c06011038144101040b001c0341081016407411751080101c80003550094001590089009101c98292640c51200c3c5040d07500407541241c144c0c02110094003146025020106554654901006070091525002d000480c0c09030072481c9a00320b40941300381584007504509040310107170707050b00d1160399034001c24400f50201e0601c0c0d5109031300304000152401e94000c01e44d841d001140d036904110a1600740180b00a16081b074039031040100f000105143d946040081a02640c40b4100b001c400c01e2070350500f40c0446078107821151040540010001d00c1070381c80b03040d107051340c000c00d0090100351701c400c400f45c0c0c5040d001d0004c503841c82c000854000241a0590300081c0000121500c4000c40c4d90780008122240c4024005e01c210f040d0710006c10442c10344102072201a084c8108043e559600344440002d00c4c64102449850007409240554 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 38566713 1250 38565463 38565467
    0x13030302160f030302060a111303140601091b050703090306020403031106060f060d0b0a0302100f090504050106091503060e0903070c0e090c09100f030b0a1a030304140f060c0706 78
    0x84002011100960b54403107081da90001c2d26000b02410604040e80c0b41c0602c4d440e0104983c00b02c0305280c05540480700c4680c4d403071400e0a40d42e8440300d052000d034021800001042e41040c003503429014804242c520b5a00b07030760702007900c49400c00e0340e042d810054460b00201c0001c0c02c510050002e94000e46030031010340c0010000f1498aa4021b21b802d01441060145101c5601c4010644156008c100c501084e80f07004180403c040e09011340c4007031742c043d17150340a04a0031a081000c01c0d40803803d96880c000c6072515841408107a44081c0f0401e400100400d00030441c455400741c062070820068540030030350030f40d54a0080c1407040261402c51240e000060050208000c4021240051048141d503141310b14001d01103544801d401d110300c030301410720342d0005114400e501c2c5410015018080c0e1000c0881e4680c00c0c60001e43c10202da2103080c0b18070700315460106a1400400e0f048401c0700500451031b0500700f518851909094074039450304110382011300c40d015540c21003c2c080c03008841004100251031f100f40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 38567963 1250 38566713 38566753
    0x6030c010903030207060c020d0605010611150408040603240612270209040201021903030203010e071803061e02280504080309040c17070207050307060908030d050a0213030302 77
    0x461414003038078070010000240c020940c1000c642280c1000d14440078603002052a1100e102c40080241e442e16001250b030300e8011401c40c2d4510079a8040300d010504121840712000742c00c0d5006040c2680c2171004100c0c540c0b00390415140e4008000504507a40400c0e6401c1d240c1d1072494000030041800101803040c0a6907901c500241c0450403008a813060324a00c201c1041c2d07640c09400a8054101c070310004065900030800c8603040c04216400c1c15040e0003c0c140103009400038041c0d502c4200d0081c02141d0702c2c0d0711aa941405840710310280d5617800b8503694650004042d041c2000001841c1210340c0e0039154024800f4245540c00392004001c1120544410303034058108460400901000f8032081c401d407540007081d40e4401205441c001400b121030801035030f0304ea9050015005840303e0300c00704074a0725400324020702210400e404035032141d52666821f8600d101c143c050746445038000e01181404d406135070404da40042580e90300525007801d0b0442a6400989500190090303408190805441c0c403503c90 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 38569213 1250 38567963 38567983
    0x1e040f030323010312020c060d06080c0d0302031204170c01060f06030510060e0103020d020d15060e030a17071209080c060f0706020304060e0d030b01020616020a020108041a010902030603 82
    0x814074410b68420b0410307071849041800040e15180880e101c1c0355003c0c0c020440c0d075040d410300400c415103484c44100d0308005080240079805147c0141c0e000400030f42420090785c011070350706030081c40c10044002c240208200d0001c10540e500034041c0f2008801d0420f64000b01299104c403030000c203503181010241c40c100c08696100d5020545402d041181400401d403404041d900c103480c3c80b0b0b244041140040b00607025480040d8a050301c0018120074401c1d065008440c40c0e11720035a0f1144040d0346100580d0010506c031083d40e09500300e5090840003034481e000802da00f030b0702c80b10000d00705000d5031500700c0b1807100c1c150700307801048000e841804031080402200c2d1100108449480c03600500302142c000d10302400e10020304064000c404541003203240d80010404039803035401c8038001240c0100042c007400080d501c8078058094100450310360242d41101e403507203208640041c0400d02c021703030044581c0c0ba070041c02038421f031314000a0322003e0004420b4950092603511000341c0c503428140101414280c900c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 38570463 1250 38569213 38569241
    0x10061508100503070312120606031b0f09140a080105090c09010b0c0a150f0e01020a2006040803130503040303091701020705060105190e040f0303060b070510051e040f0303 75
    0x1c0000c2141d036a0000f624000d0300e0380182c0130410465003420940c1e207072140e030080c640c1c0c2604002e00854001c0c0c0c1079005c0c6a5142c43d051240a024204160035102006101d0401001030120001030040760000c0303901c0c0c00350800250451124070386d40d040d02421903005a40301103658201c009411490b1809055283c05082c04003009440c1820106825030b40301c1d010240103080e02092041000190300381e500000c00c00740c440c40203202840c14050042c1c000d50200c00c501010035845044d00d01801d00340c11080302d080150744003c008685854541351040d420041092200004900301000011401d1020300000c0d803090300d56402190030480c1b0701c20052900382d404032482c0e2042c44880081180010000c2c112903081d510690301202d071601d0b444c0c00c0c122640107000e100500c1020f010400c8400c495070049079000313503010400141c407403034034201d54410180090003581c4599900008401c0582c00150410301101c041c40c0141e40c01c540628031000100e42c00d540305075012028800745501805001121600380e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 38571713 1250 38570463 38570491
    0xe060d090614090d050702101403040308090f0c01120522050303091c0503040f0809100905030c01030204060f0305060f12060403030f0c021b1302040b0a1107050108011710061508 78
    0x30345004006003d2180068491523405054820903401800f8100754041c514007810768910f01424040c2c00c508060341c1d0075245115088008003007120220b0994110501650b40c583c0b034818400012010706000741100c00c480c405a10106154845410308103034040c4200c0c0034544a140514540341880a1602d41d1800080ba00d0407681c451607004c011240c2c4039a0060342000000c0c0306e8186107403a800f642e0f100c0303500030000500b11394130075030800841002c44000710100c9014112850044069001d00e1141c00301181034007142070911802600000e0784414060f05003150740d40810000761101004450f03001c040d800c0702c1d0034030043c540d050164001080d5603035000e1104169445c4000c1d9500104c0c0441010710741001001030050341d030300f1204001a21310100554940d500c6400c0d40b08141d20071864000801d40a0444288140c004210042150710503150741c00030b60700c2e0aa1050046d01d280c1c12028090140d44101c03442180c1c94480d100107000e02d030056003500c000d14100a02084000782003000000d0340 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 38572963 1250 38571713 38571733
    0x3050706090f02090c041403070605040315020904110304060b01080103020f130b060a03051008060f01060302090f0a140a05040501151107170606090f15010e060d09061409 75
    0x4112404503621510010710300e412401c040808038101a030095000741160144405000041c0152081e01c46100c40048082400c0c0f00700b5695480700c1c4900e8021078814402000415951030541c0c290306940c2e9405490180403074002030031a01c4e012003102c01080f004c4188401c1c0006441050806074003800c1a2a031541140c00007000c1c20700740c0c4203c0744202c440300c450310040d000d150482d80009502911403600c038603102101034003406049550080c5200419000100041d00003040c0b80980c10060340f1130340503420000110040e5004002080e0840c080701003011294594440030b00003400d0304180e1102da50001c2040129994084c1c0c0103910171400d00005111078144d00d1140c015900c031f14144260080c4000104c981040034a50101421000400c43c20340107500219006204036400c640714916591200740340c10030300c4001d442e141078140d4488082101035001c0e441480c49004010300031410304404e00480001e0301d14054044400e42e03103e10045d00f0442080c03c1403038000350032201415000e46 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 38574213 1250 38572963 38572967
    0x2a0303080702031303080f0f030a0207020306060319030e01140a030608010f111611060307030c030c08010608060f13060b0c0f0304052202090907020a02030c0406060e010503100b030106020a110d03 86
    0x211502000e0800f01b000280034040c08491401c0f11800c8601c880450b45a01c1c1c0413800500075040040300741e009002d1180011094580441c107841d1024240426448402603a102114850080010329040c096040e440d80c0d03d00c00c0ca04058203031141195408202e01d4204100d180c02e450b01c10001e408081e08102003849000952816240c02c40d0780d13941294080d2505007041c02a500b44c40c800150131000000074803181a515400c8075850b02c54179201401680c085500c2200e2109003480f0301d400003507020b000b0031401e00d00030030011414800108014004e0306180280c80c2112900d81c46544070a0001400c4103c598060ac4551260412107000e14201031900e404120b0040146140c104001c1d21440c2c552aa201140c2c10384600800107400394103985090807000e5a58050244182c2c403a1041041035682403401c0c0c0518820390303020b641c0d480030701d030010001510242c00103400c20361461144080402c0c40c0d451080954001c0207564020b24031010302d030412128040708512a503004820041c10000030a07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 38575463 1250 38574213 38574247
    0x92003010b030f070e0a060323010b0a03080415030b0a08011a03030c0613030c0b07031a091b0c100c09030201080f0c040b07020303090d03050c0d0c0b132a030308070203 74
    0xa40c1c481c140d912a642e1b42c0c0c005130020040350300014075505007100c0c0b0892000038001d1106003140450020400ba16911041180c21113051000a104000c100810f2104600c40d0380d00d0300040744c01d42004504c4240c2c8100140303943e225904042c0113603541ea1100c1001a01445000c82c50001c00d070041c510b464520b01c0c2c1c2980720742c1d005200780c5e90042d038040c91f401050b01c1902464030316504462041d5042c00c115200401810031314850900e540c6600c0c85064039031402e20100b078020729001c0c2c078018070350001c9018a074907500704400c201e0040c000e40c866404400c90602603103680c0483c40d50343d1030409007544005004500064010904842c80d8070800c20240c400c802243c050f502070078080fa468031282d02c002403443c03003074200140d000014512030104050300b085c05059240d64034800c0d9451002c02510403a00d055500310040d008813483d0020400a01500c0c8000400d00d0040a0301da01425544000441d80742d084041c204003480a800c0800038154000e4034540c004c2c0c01840514900b9010901c0300b5821 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 38576713 1250 38575463 38575469
    0x902030405070e0702031318050702010c0c02100c080c03031602061003030509060c01020d050a1d193012110a110f0d020a020405010803041a030901092003010b030f07 73
    0x2100d042004c1554a0300030002e50341c800b40040403442c48103841c1c008520f07400104200180001d420580451516401800340302e21104d801d0781c8810303084140303400304401c6e20341c1c01020b64103101c08030000c0750200c0c0480d00240701c1a60382200840d52030034048142002d202078060b40d1021900001d050241c400b00c148c2c0c44008a82d050f20740540c41c0c104c050b0010b0086c1c46a52a000d800b0740c03000444808040140c0c00c1680b048803078600400c050003002a0964079412904006405500008086041c4035400100326079441d009810300c00313980d201c100d8918420040c01c3d908a18040301c1e40c8041eaa5141c3c00508410308115202082c4203040e040d122146071030164013907035428806820f540007030441d010000300401a0307040013102e4000320b080001940f110a8000300781d0286040c90008556800c0c0001114101e440c154212140c504507a04c02e19400d400240c4601c00c2952140228400320301c80100c840010000e1020401020904004260071619001c1401d070094000c10100022800042000c50807 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 38577963 1250 38576713 38576729
    0x9011203031e0204090509060702030f0a050d0207050102030705031801060e0703050402010c0c38091507152403020603070f030b060f0a230403081804051f090203040507 74
    0x9250700700302c40030010714548094450441d1000c0340000780700000d900000c0c090702c1042c3c241c5056448034001240c8034890800343d1581454204240c140045c4a1802042410301003000182030080a5581c0341c01d9a00c01d40340100000e00c0441888240c3c492444001031800390f102c003c1040742e28280342e40d50b010400a120f07d080c1544c400000e4107690040c1e0a40304902e510104200c802a105c4044540c1440501c5004810124400e460492024440300081c40012400529401c1070b0241c000c000c44016681c40306080071400b44022070014084a8000b00c481c444d03480d000c10414210140014080da240442c0d0747c00044040d410005610344404403504000f032480c042c001551030040c00c0d400b4110b10b1440b00c1e0400301c00607400442a40200c00750000003c2607540b400384043c400c400c1c0c0f110480012162124080c100400c00000e24000e0003400d400e4039204031000002c0030300001a08503001161013080c60b0042c1d5410b85d200701e49071200103014050710700f000c6042d400c190700d84a5a0300c4060150400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 38579213 1250 38577963 38577971
    0x12040810020904091b060e01030e1b2403070e0402070309030602250b06030114040c05060d0e0d170108030a1b02010203040305030d09020f0907020604030f050405030a0506150901120303 81
    0xb1103444540041005503000300c01c2501c040c507a13920901c6805020721a4000080c44000d00280795842802081c0405d0360a0340200010820a8030041203107104012035544540300f20384030200d00324070010101d0f58400604a803500c0c0e1a1004e00680441040440140b06d14030403c01c0f03030f0000741c21a0000086d01c0e000880140c0b12003540f1328030713198084e800781e802c1400002018620104451010590b00c6850250000d00061291501c1e404907001c0030340e401000942c000c0c40038400c41c248400600340300b16032240c01260035441d030b0b103a160400300040381724030000c0c0e99920003010140c0004604c50040550303100541c508101d1300001400045011a07000075511104008815607100b042900c000c1c58010041c3c3e40e40c1d40b040f001f140000c14890310100c1c000d00c0c00c0314889043e881c02106413071103a010364000c0d0201d42d955030340482d40100c00d24804414480c0500002c581ca48003000b45241c075500c00c41c010000c6040152070880c0240b000d140d100c3c0310b103141c80c0050240d0248101c400e40e0a50741410081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 38580463 1250 38579213 38579227
    0x504021c0504110a0807090f090209070f03020910080601030c0207050d0201031104030b1e0604050708060613080303070c0605060901080a120210020706061403010e0303160903170a021204081002 85
    0x10300348801500344580e20040704580810340321703400b040c0f00382100c042400800c01000d08041d07840c181c403d1410041d501098000008450b540507543c2040114490300d001417600300c2140c001800002c4814030800055101d00800415581501c6000f600c0d000354001050164903110010b580c0d0134001000070304154542040000c000d103650140c1c1c0181d41e20031400c0041d80740c5980c1d00c02e134024109901803e241d0a800215030710b41030510440340a1003180c1d032030300d005503928400e00c01607502c070400c03484812008090020790440148050f6000d00d0700c03075a952000c40e9541c1050301c10340350301404092003171124800410240c1e00000c1c22a1001703910540c580c01c0c0c0100b2001c26802c1c000c8019101200c180002042820400c095000d80150b421621038111031112844c1450f00301e4984c14400d8445500410225064106450320b07641035688519181810588964410804244416821344400d60106000440c950180250700700c100320100c050b4206443d240c0f42668940c00c15150042844e40010b0038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 38581713 1250 38580463 38580473
    0x6010815060906040e010603021e0304080405010302090d020a0b03090c15030a05100905010801020a080a140609060d020607080702030706080708010308031302040c0207060305011d0f0a0b0d0308040c0504021c0504 93
    0x5200141503505050401b503035540000b401a6000c4c0f2200c00c0101119940000240d452006036400b4503000215141410b05100043d4000c1d84904210381e4030400e0140502d005a55205010029003095030050380c89041c10044640340040310902648180f080204a041605800041e40e83c450718035400850240c5404040d4215601c0c160802050f03542014004548800150000c094881446e0394000645c0d4034810b050b0110343d131545d94062f60403290008681c0a28012aa0340d40100300144420320100d5650b0015126902688045070340791b5002c9414429481c0500c0004000d150324102440103143c2400001d000f144140401019160040049a0114800c0354040400b60f40648200403030440210041c1d44d0b03c1c0c6901c10480041d05160011a030f0500348a184080314024840089682c0c4402c1c6100858820080c401880d450383e40c00b081c86659513844813060076a02944407044241403034100315204200c2d0342c000d02d0040307004002c040d442d10000290740c0f44248503d60f00040326140c510741 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 38582963 1250 38581713 38581717
    0x1021903230c030709050d080c06070503071209050102040803040e100504053115051503160e15091f0b070312090311010c030b0102190c0b1c0f021206010815060906 72
    0x3d9030081c7c1c90060358420400c1300001070911214100446410350b580300c408440c40c0c8401c4604000089080b51041e000400640015030201d2007440054206621003000ea842e42d0800d40c02560442805414068401c441d241e0341f801408003500c0034080c500c0e02105c4541c0291040588007041d680c529071401c1182d16408603555582d5001c22000d00c0f912160107044081d0000703482d100c120000c88401d08419140004921840e0410f40002d00006450958038124007800100160745400650b00b10500c0ca5640203401441401703802c569102c002c1c4244482041480c098001c890a20300c1000881c02090300811080c0466006200204010b40245021120002d034441940211f609007011070107015090781065048000a80c00c50f0307a00b9038034482985040000d20005081140582010300c1001da01a0003400038080140f90f183c001d1b009000000300b203800700125446860f602098020070b500044a1050700300909103010000f0b414407144c01c03100282c41c0e801040c4501400104000c084c0c541000f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 38584213 1250 38582963 38582969
    0x906080712022806121811040f060509010308071a010f150e030d080a0b0109150305060127060f1805100c02030601081b100e0f060c01021903230c030709 67
    0x10a102c02c2d40c2c4d00400b90002114845003440c807400c0007020b0445011629513684c0154103d800621099002018400186889441c0312032180d12030f800417031180c0b6400c12490085208420141e0341d400a41001c41140d01004c42d201c02c402030203801003200840030300800054a034080344400009802e032100b540c0c0440d18444040e0076000742801800b540360801422442851a8441848650f42c00c000440d030303822041c01810070010480c0401c004085c400d42c0125405030040c1400340188101c14443d000982c5402c60310b1041e00c0d004035050003040d500c18035012018400341400070f854030543c8180340b218580360040d14000c0c01480201701001c0d03c03e108001900303402405981581d619100210703200c1d60f10b004240320254002c582d04421b402e0030301280c490100c042d03445010390703441103040182d6415040103c1e984100e05200341310384a0000e200500c8180384d284030009020f881d129000c3c042d01d80180450203100081203800c0046001010550780c441c13003c1ca0915543e5032465000d5030540300b103030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 38585463 1250 38584213 38584279
    0x90f030109060f0e0f030d020304050a0507030605040302010c03060308091201021308030702121501030311070906090b010207090b130b060c0706080a0506040b0109060c0f0503030709090608071202 86
    0x1400000c1481000c0e400030b00000d05208003442100342d13001c0c50707595072070210b45140d030317958802c004045a28a0b00d5000e1508548030320140c0d1964606900c0d01464007200c1c0d00255040c942c0c800070b0108058091007000001103132070809015441c51034482c1c0303130a070003159200344c06039489807d440803010003941160404e01202d0b07100750209450b044800e90700d81010000720300510040124a140c1100040c840c41070310201084d14101342c1c00d41d5070868003854008003201e110f10442c04081541c1840b0700800000d03003101c03100040e0317002c1803800091600030f0a0380800d05091611a9031800e58071002000b00e8040007081c030114156078028040b44040c810030003001d0940c0103207030001c281c1a030710485c01402074240400901603915000300b000102c0e04130b06d182901240c4007100c1000340314000c000450580d4001d041071000115140c41c0c4d14156401180d181e03000a007030035014489860340e44504000741ca45030009203c03981c20001440100c10b000d08010f03201e81c140b0511600c03589243c61500d07148240311 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 38586713 1250 38585463 38585471
    0xc060609051602070806040b04120201020702060a0e031506031b060702030a0f0201020601141c020315010923010f05060705120a0c060e0606030a1707060509030309070e0106090902090f0301 83
    0x1200ca910762541c00b0704440005000311100040e00311000138a02e401160441d0b000b00c986d8941c0c0c0c0c0c0b00130030744240038007070410b65409004940141c0d41c0d90010781404001500c504042d02007400030142400700c0c203000c1c40039514980082c8a010f450000e4401305000c40c00700007441d00600d540c001445806900d00003503040c45110282800c00c82d08100c0c0d580c0d031a200b82c080784c15030b1740c0f0340028010100c0f64450030340c0c1100b941200d410700f01d00212410708242d80058143c900428005060013142c50090b00286501a12401444041410041d0f881320b401e420400c0b0082950420402c17024900036441400d00c20900440c00308140301050040300d15030701000706020340e00d642c40d160280c01010320803029030740c00d450058580c0020702d000c03800381d12030f540050140ca0208d40550314081140c02d04410320040351014042c20000811034440c20380a092104021a01e070700c0e011003494a42040c86e00a042d000c030301e680040004a401c030481c40c068540090b409078a52a440c000f24418840c0d001400b070707141d030030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 38587963 1250 38586713 38586721
    0x1081e010f1707060525020913050c040902030a02040507090e070305270d1809060b0d05070c03080c070609080f03060a060201020307090303030e0708030a0f030501060c020f010c06060905 82
    0x10440c0c40000700c0303400e50700030501d210038049201d48035810f40c03007024081003040006001da0300b0311821414548982d041600541d4030142c000c20440002240c241b030703c00300c1452a039801d0160402110078810341c00c0782c051080c0c9441d07602103a220f14000c0790081c0515100c1010a609a02070341c101409080c6c800410b882e1460034110003000b504042c0d501c0c9036000c4017000b90a07003c500404801500e102100c0050100ba80d20b5902103918000e6803010038541c40310351300c0108039a20107004a85c010400240b5040d00c0d209150600303412074001038244802c1c40103d400c054000782d00503ca03240d100d228060203603141ea41d141080006010243d400904001e40003c40d8417000510b00041e5005e42c6040e10b0714015a0781324041071b4201e00c002e070b81d25008101c4043c1d042001911039003050303a406d900c0c40e06844500d82d03600c03d407900e5500442101404985043c0c4500003695051042a005245502e46000c4d4403513141c0102d20980d14000a6030b0400486580e0081070003525002100204450101040507140c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 38589213 1250 38587963 38587979
    0x4020d060905030307171b0c01060b040803180a0807050913020a03120f1d0d020f040f0606110a080a080a0207050d020303011503060e15030a050d0302070606050108130201081e01 78
    0x110031188031000c03445401c014182c5804074405103102d4107258054420741f00f10003405c0c0580390002000c02c4495921f80501140071107a0ba00070b031004200d0303c0003c503240d81441c1d44c109034109100300c105001c1c4105080802244000013000d004442042e2914040303a15075001d01c00d0b601481000c0a904141105000800c001504415070740b80d651a5503109079840311b100b012250070408140e40260b065901d21450b4085c03a0840342c440066100070211040c0e0700110001c50150795020200005d86991800100315503038004004140d81c1400d040a018094002ea035603184030b008000100c0c0811207000c002441074a410760403070301a03d4110b400c5840204280380c009503690b00900a105810030814580d04800e03000303010b03c1050340d440320402c030016076440001d00e4083c1040c82205034588100540701000c600b081c4011603010180f81d1b00540c1c1d6804a0600f9070543d161684001e0400c400c050400c09103451640f405004194246459030036610b40007440e80c01c10f00c144040d004a211100c000142c0301c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 38590463 1250 38589213 38589217
    0x408030a0801050103050601090e090c0d080909010f0b03010b0a0509041b140c1b031606030903090501110607080408040803160b090111040e07230a0206100f0b0304020d06090503 78
    0x100c16039441c640d5981e00c0e0001182a508140c520700c1c081780d504482400f001d90804209540078030700608680340c80140b4000240030480911046d04e8181d800140180c117400c0c1840c040c2e015050905000c0c01c3e841c505521581c0d58401440b0310719500c440400c503036907580e04c03031822201c05a0b40100180204e00f41c0304100501c3c01300314041000070a00900e20426085905020380308001181e60182c034001941e9035000d00800800c580341c59140c02030b4034031440d20020980c031542c081d0203d5039001500007507501c3c0180c10411590441030500100c100c0918803942c1c0014003070703400700d85860101402e1300c0b80c0c0350501f5980155007041c4164000030403407a42c14404450800c0b50300c0c0c0544003094098498217095400c0710b80f50700c4060104401044180540c0103060b061980001080c40c002d17040100790f4294000b605c05003548510000300000d501c1c0c00700c59042240703c0d00f0518a01c0208072040c54585015010031080c0b060b007000c132401100080565842122640203a074000000780407125091a000da01c03a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 38591713 1250 38590463 38590477
    0x9031006080c030d03051006080604020714060106021005010b0418110a0302131203050426060705071401050105010503070c0611070b04050d0305190207020d050a051b01020c0303040302150d02040803 87
    0x1303100700030074510460311070b020f203034003c40b1440320000301c040c18400c00301d40c081001000940c1041c3c00300f2240f0300060001d1050080c20204178050415541418030084c01c0214401c02c4841d45801e203001481604151b0003164121095010007201117441003403404013402c0301102110801d000415110001c68041d001420090b150701e5200d43c0c0d0580310301e200c0d501e42c11440c1001c4c00045c01400240446002440c00c03400c4140d0000c2d5400c0c41e441452001454402c1c11200000007490208050040001450206100b42200c10003484a90305000000388980002000c403020850780c100700b002403100c6644000603221005041596401c21400c01c001e05041c1610304854501c512641112290300c01d02c5164040e074019610101244852401c070806900102400e07648950315640110005800300301c129980c174031500142400740c00300c050507a104211800258117640100902c600a0b990110485e8140c0f60b048400c0c0c0010001c0a000f860f01d4042c1d1650040818030019020400c000004050010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 38592963 1250 38591713 38591719
    0xe01050a05030f06040f17030a02070b0c03060f01080c0d0608010203010314060103080307031505090f0403020606010e090a0905070e070e03010f06051806060d090606080c030d0504030809031006080c 87
    0x150349070140356075100014003550a58001c4000310b4000344e40c298144450600401c005000d00040404101c501d41c8241c070303411a13444d40024010f080018a1010175445040d075001d450851030140085103149041c0070000c0c3c10411954005202c071404881030f143c02c210318401c00c20245440700d0105000b98001c2c007054400900341003a40300000d000080c01e905890b8040301850a5441e5002d0940103041200b000d262105c103400707000318103a29024540391184601110f24622424030b820081d0600f0000741100e8108250700702403458644481407582e0304000070403030000d0918954200300d810b0001c103402180c0254110740c203001806038070949004c2405001c500801426070001c00c7e64003221014401c2135000000c00388602809a59800419480302000e0107862910380b406112030200e403400c25044448035035425007804590005c12000c040c3c103806800504843e880300401a046010700d00c40101a0300c8002000d00d4142c506002c0a090b040a0700000d126954a981d216a19181e03025a4580 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 38594213 1250 38592963 38592979
    0x10315090b0f0a03051b0f041113080106081f0605031207050105070201021204030f0324030605090c010804081305031507020d0309020609010309060b1503061201020a1b02010e0a0e0105 81
    0x54624001c882441201e61140040c00c5603803285006c000e0050701071285551140d601c11105200b92074600a42c034602d10b080480c0ca41e00c2011a039603400c010700b603801208041c3e00d030a07414083e4900000e141d900410803d9420b15044081044107005080a80c00c010740502a007003402c0e002d42c60410240612501c950700034041503440070800c07800c030300039206480d03c00c0b1840300214000c0390003083e0441041d0080c1c5001b1031295011003005001050a0341200c050245c841c1e4100700340300b402d10840d5000201100030300004110240005c0503044054801342010800042d400c0090030005810001000d014080c0c2e0300100008503aa8401a8111005400b40c0500307030080c03c1310b83c0302e4482c1c0510a98010201d80c00d1001a50045000b0f00303610300b0881f5106e54078500e40c1850f0391420046c87c05000c400569655900e0031200380b002000c0d020407120020f81c0103114001c11140c10160400c82d10089210441c1c035502c0900040700c009030b41104c00b42d084092040040741111b0030031a2681642d8066032180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 38595463 1250 38594213 38594239
    0x50105011701050708060105070201020a05061009110c060601030209030f0604060209040e0c0109032d0503071e2004060306140114030304050310020a02070803220e09060a0b010315090b 81
    0x390983d40201c03229030005003d000000d0301e540c042c1c000b8005490062046400300d403083e035941480c0081c291036101c04224802001c0000c50180c4c00303807604c4225002039032400c0071466614140d403110042c00c00c9042c5500814103210584013007080480c0e03042e1b41c01c200c507424101401c22200943c4100341460241d0b013421202c040880c0005151200e004060391000b006914580740d019444c0403920344504070081d22520064940d2200b050107810a0050020b195626028600300c20080301ea4008294120004004c10700400d08801c0d212080340040798140407400c48041c00180140b046400040c070980c5494010741d460468a8030300f0741660b0144850003110354481041590b203009600c111a1b0603030219a0445a50000390050400e0340080d004580049031248991415a00245850b88a0390100360f414034880100c149100018036640300303079174442c2c1000200584c56a1000f03080005080d100c41100d1841e92095103d0203515126003000200c89850380d0903a0042d00d4500d540e10700c40c141c20a010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 38596713 1250 38595463 38595509
    0x60e0a020c0309100e03070f050a360213030b060f15071103070b0406080405010b090417130f0b040306050a140711030409060308030610020729040f0305010501 70
    0x1c64040396000c0085007070240c3c40d0100b00c00c03905526141010800b04514001981e102000031102400001141418541c140014001c40c2da040340c4c450600071701600d16810030f1180f50351400b606140001350390046110305841e05000ba02c604660024842a0041c001050000c1c0c420814042d080882d01c8000f08100c003c00c04c1003d02c00d03203d002006041c00c01030480010890001a150440c0160030340303908603038511498119030081c0c0c2c400004507400c1001c000070404280300340403003c2d02c04c554955840c01c1030340b80c1c101c4507450a01c07a81980c01c4006080040e42074610310783d0b40100000c25045011a403140300181940c0c2203444105c2d0005d0601011a10104103402184900b00c0303124100e01c410b55461200b21561103102500f0182400208804140b81150b4090000070f0750007008516603038140002800b1a2030f045c2c645042c21034000c1c12082c400c140803045400c0311008114030b16600901407803d185854451035001e04038881c0c281000001300030b8190030840c101c6682c01040e581045d10b034254 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 38597963 1250 38596713 38596717
    0x60f1503010c020c04020d0e070902090108180604020d06020c010507111207020607060902060f13030b01060c0215030c0412050d03050c030c0403150209120109050c010309030912081309060e0a02 85
    0x9500050381048444207040d04040e4054020203041050124007a800c42c91900d04005203a003090042030b40004cd440d4440d41c00402250300401000c0c510b1107544904c3c81160384440e80600000d20620300d181c815002c1c8140358069944800500c0020001c5040c809805025064060900e01c203030b000e46110751501d4054101503a200503000340006161a800350384420007000c440408a03400f0701c00f408415280b0561360b015145013680c845201d00d40301e0941c2000514050141d010342c08103e0090034450060700c86a444440f4139200b40c5180780c590b01d4005000707400340200c0e0850b160740108481c010f002d01c24001160b150400054604109940703610100131030750701c02190b0b8807201c1c16081008200065580780c4001e04190442001420203c1800008d41d000e640011071040da60345411140090040602c02c501c03846609080811502c0c8859401401200b9544500441c0c07280c09440d9500340100c03541261a01d0b440084804001030b00c45080b4001045c4a0240d503021700643c0e8002130001a680c82 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 38599213 1250 38597963 38597981
    0x6020708070b030415060e181b010e010c02010207150210050106050301050a1203030908070b09010501080d020c2404030305030907050a060801090f0f02030a02091302030402100c050f060f150301 85
    0xb0414507681c0d680e11440703c4c07245200c20040c071070341c1e40c2c00c0c0005090b10098041345c0260034201c40c050307540c0701c0740c00c400e0f2400ca583e00b250904100f189104007100da0300301d1050b20007080d003801c03c01904d800340c4c00144e05002090f401040f00400005102103050f80c0441c244d450b511004904210a90720754808661f540024058150060060078003030020011310407c1e80089032107803030702203804d640f00e036a100b41e00d0b00006000c442c1d0525003020300a49041c280120b03030140100a00500808000c0e040c004d5642c0a68090300d8016a622940c480d000155170fa1007018203071404403d1591580d0740d1900034401c1d441103e54a0244c040c0c42d0000c9001c0ca450003c8204568081d40c8016060b400c0c10205001005c19105403a2199034690407180344441600203103200e1540f400300142c4801404050000820450220718a154410010880144d480040c004002c032058508100020700e81d10f0075034607180f00011044400c0c4071350020003003410803e440162007113000360901d500041d43c4106260a85108403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 38600463 1250 38599213 38599229
    0x60e010c02070b07080915040303020c0409080d0f0b1c0201170106080403031e060303050306010210050c04030b04081b070311040509122a070501080603030301060c06020f041d010602070807 83
    0x100070044010102c01400240d17025010561424000200280a01ca085100505d68041c086010018503805000788504410161410301c00c2c1c41043c0e8841943d13102d41c0110182031070b0303900c0560103108919480b1041c3c44001410031780500102c00101000416400c1040340090a00b000b14403505ea0001001812070b0a5916000c000d600d43d0783e0154043d0000703001c1c20900351100004120040240d0007890019406521030903543d06055000a0400709a000c0346d0040e01d06160a00151842d2a0300f00c3d400c403030b001030140a1644662a10071f01c0ca114601d17583e0309a60010b64018002d400c00f1682e001101d205800d80040320311804240400c1e00d10490300040a90028100711110408000007410249230f0303000b0360401a41a0907005801c610f0020b4542d070f89910a150034400795800501d920303000142280107605540c50040000d00000d606a0001c201c190081808180003075041c05440c0900038a0708075880d401c20346410664019800d00c10440144079110b00003407520300c080703001403e43d4600e0b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 38601713 1250 38600463 38600473
    0x230304030b06030708030c1c260906010b041809020103020702120705240919090c02062a031b0403020d060236060304022404030303141314010b03030c0a060e010c02 72
    0x108c0c11000300c601c480c144203000c1001103a41003c4d51072289070b11203100440d0034403000e080c6a0007203882d0940507008509500001c0000703000c0340421080b0349240694408012511608902c0101d001c1d00030f41c2c000a4001c040d690401e008010040303401401d403a02030303070000b640740c018001017100006032220f42c200c8000b042142640e0750505450b0700380f00581c4880341c036104555035031a5404417641840e074840160004400d00801c40c0b224070242740c4c0c40056418061002585140c00100c0d4400a03004241d51007035802d504548145550071344008680081c0150b14221a5041140107940005521145041d000741520707248681310341d580b4841c2a00902ca440c90080b0300c402e0001542c400b410070303a8018200043c41d035030ba880c40a0211a16a0381c070500c00c1c1c44a24500e800740580d007005643c0010b007640d982c2004642200c040700504d0150300140c1000307682e01c0341c00b410340c010007a0504035034150100003040c64070800c00080307115107075200c1d60007003220b1031190300a1803c850f407580d000c000503084 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 38602963 1250 38601713 38601733
    0xc1406010b0306060d060b03090102040504060b0c070b0a0c050a14150103051207030201090203070f051807120908130e0117070503030403033920010804230304030b06030708030c 78
    0x400005005e5010f001d0100041c0d0f01d0b00d0f040c02005a400448080ca80c0c0d0790001801c0c0a1420680900780040410b04606400d094242c051030781c90708041e0141c560a0100070413a8607400780300c0c07942190b8050704001a110769088906020030920301e41c01d000b0442d03108190380742003100b2000003401c1c1201d0708900074100320000c54240340616440f03220243c08540d01c0385003000160703505004090081c6044424044000e00d000b040c005840e59000344c0c25407034004841008a0305030005c1d9070307945c0c110000da000070782c1d00d0f02498001c0581c0251154482803151001020034045481c901d801d041c0c84200484410505030301c40e020b9900c41c064001e0039007540003400100300003406800c0212210350340c40a003081c608410b12500104202e003081c03070640c81c60210040c00604c44081c03201681101c0680b0b2100302c1401110003e0420007020304010801c8020714141a011104d00710544800c002c1d00c0203403581c0e2552030034400d200e040141c1d442440f0340199000002c40001c0003003140c030261060006040340b108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 38604213 1250 38602963 38602969
    0xf12062f030709030c140103061a0702040b060409020319060f080316060b060a080103020906010504060e090613020a0201050105040e010b010f08060d020d030c0605071b080315040c0c1406010b0306 86
    0x405000d2200f40720140d1008000a0008070941c1c016090200904092180000004090301c0140d4445200400d036071040ca520000c0340c2c1e08489015405541c00b05002c529040854518400c540c4400744191000c814400388402000d628400742c5014030b4140100c41c0c854001014060702440f030040964002c00501e450401d0f404441c2080c2405102d00260b06602140421142d41c00300240c4000031b126000144114074022101039000328007841c10608142c01c20001615810106a8240c4149801d00008080345d440032003620011154200070b6448003900000a070190030203025243c8a03604044c0344007490181403280c2001c40b40142d590ba0000724004c0c009540803440a0000c42c7c0007043c107003080340581c441e40c9068068078802d94818140c40c4c0c03581011000c50300c001e80b00004201150381c02c00000303244000d11100007900540d0169032a11051180e034030800c20304880b0754000f070030920f008030003a421000001c0607502038019100b8104034148880e4481c0c209001c0c1c1e40030000300f8030224032181 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 38605463 1250 38604213 38604217
    0x7020606031b04060504021201290a121d0a0203060c070b06100203040e010308041e08070b0f070b010611060c0301050303030711010b04090803150402090306130c0f12062f 75
    0x42c1c1c0103040041c52a8a603c086400d9a002040400c51640d01e0401002410302d45555030101c01c2ca02d80700c2c075800c0c1d00312088031842881003d80800c10041c29040c91810340f6200d502000d00040e403200d05484510f02c010006849245190060348a070007054001078524000c0070843c0c22059200084084660b115030070888480d291100c54011484180400301d283e00034072101d58046e601a2220a8032585007407003c1c0d035520b07808142505c0350300e00e404080016100006985040d41c00e00c070006511008002c52250a90180e440b024109880220001404c0b1340c0040e02070150509038001e40300181d403444208101d910003881107036007690080002030381140c07050980c100c0c1c2c1092030001040952140c0c00050545003408000c0d84d03520701c0002400504003525504400312002030341d055042211440000c0c1c0c40e4440101a00300d014018007001042014080c40c002c00360440403c4010070540b0750200c0024210000301c101c40321407800c001c9021403001d807140d9400d150b1600003810307c03011500d07242010039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 38606713 1250 38605463 38605513
    0x1709150414060103050c120a030909050c0d0240030308061201050a0605030d09061d0d140f010501090608100c030605120c0423040b04020112020c060702060702060603 73
    0x322076040d80000404061124900840c01400141813100d011000c22080b80e0ba81080c080e9294411500340b800260030400c004111600d0340b10024041da956404a22140301c2c074641410740b284000b4001c10780da40100c03031000f40c140030880f189030900001d900b490441c1590380c82612807049200820800a4420340e501c6901480c040c1c00d0740c10480390b484149080d220240d403c41084d41e11214140300504003003080501c0c1003024508240440c0c541b41e03000d09100381070a01040d90406011f414401516180b003102c0007a0f500080c011010b40442c084e040d16210210b0303031901c0c0e070750800d0000a65418140207200684070081c020b0080148145d100c0c0c40203000a4039594141521510b0004a40e03440601039410f07070103032101802c0d2034103101003040200e40302842041c0100d0a801a140100b40310548503a43c003a0b4003400a908548850005070b030a007034800a118040740c00003682c0300a181003c5003550041c40310b0b80843c1c0342510fa1000c16a1119000c686950b0168410700c1d41b5400030549030319108403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 38607963 1250 38606713 38606723
    0x100320010309020a03060c08161706030703020306070207030b0a0203040809010f030f051801053d0806070c05010e0a030f05090f030709050403090806070f0c02031e060717091504 78
    0x790040d0f400315181d00456801643d00b140e42d800302031400390300540415400044100105542c000d4048064803210006640150b0061074034001509610208090f4000c1d6400404454051404e100020b5a8008500080f584e100c007900200b641c2100d5402964041c1e50701400c903a00340074194004585852844a21000300360301d90560904842003172003003500035005616489803541c809648139080d650003030020024465050405404d200c085080410040140c21031188100308210b60620801c0191704401c3c05400f0b4007091040c11600410b0500600b8032400c02405622000f800c040d0b192104130350040c1c040b4100e8414030080300d00c240000c001c040c03401046e911504811002003803400c48290401c41111b982c50007400b0034160062810b1005100c1d003001804640b40c880801000c0443d0b5900c1c0006002c1444640c004665050000c00e01c0200014140c00c901c44c003071509140d403101c003559044040b440c182001042600200109032241c201c0358028050040108032800014900400503a5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 38609213 1250 38607963 38607971
    0x304020d021e011106061c0c0810020702010e01180513020c0708030d0b03070312080403120504050a0201091203091203030615080a0c05040312140c0f01020c01051003200103 76
    0x40160340301841d2804030152203030401e20310002c8400142901103c40d40c004000e6120f80300300050380d6a02a1111a00c100b40b6070f52100f0f03400306140c80c12900f0070f00e030400070f06c5000d40810400420440e502600216000b40e861003007549880700159a40030440880c1c80640b01004010f1000d820440c9103080b9008481000516000b00c02103130b81d0911045030002c91321134000103402d1000c10001c6c092801d42c41c00841c00342c68240e00e541d544400081d1a6406202840b80040004041c0742c0582400c02e041159480180014a450f00d441c54940960190490204910324000324200340b06054800c0700d00e07450f03140d5180c690704001d25103081e2841580103c1c1099220040402c10034140340f00040c1d400c6aa4a4106081c104070526105440c8140e8422041100500c030400101d0382c054580f1441c1c045608100000b170300300c24102d000621600f00144518404d00c03440e4001c4110550080c0540e840c408004c1105844118007003c000c1801d12001d01815090340b510290f00400c44c04021500005041c002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 38610463 1250 38609213 38609239
    0x308061210021804050906070903030c030c06060b0c01050a0b0a1a040902040b04030b01140d03121506020304210206040302010513031b08011a06030a090503160804170c03030a05030402 81
    0x101c140d03440f00703d030f20301124000d88102c1d402d03081a00030b0540150380c81c0c01500709403503c46d00041086469200c0a010820942c004106250058140740c04454003c4024030074030351540024503855200700e000f402691701c0c00b00044e0500000d0701ca070008589000b0640210720345800b80b980e46040c44259900d040490801c00066440c0d43ca100900c0240078039201d280d200d41c5142090310410f0816400b10705c007815030209a444603540c4080503501c056040c18152248542c03041100010f0040c46100441400a180c0c04a501600040a08200d40c50b103144a910a140d0800000030060041002500300300144000e000541c000d0000e04640000c061500440713581e00d885004000145510603d001c880340d280030f100b111070a0083c03010b48a5021400c803030031240e00c00411220f110080c4800c81c215621896402040380601c00c80e4201c0f003034000b24082608045c10054090360291149140900c01c588215070a03000c04a42210b09403001005907041040d15041990140d100401c101d078001c00307401c0a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 38611713 1250 38610463 38610493
    0x30708041b080d0c08041805090706021b06030901020c010515311d0304030f060b06031005060a051204060501050f0a0b0f030a0e01090f11010c02030613020301180f020108060d03080612 81
    0x3a082c0741f5030100000c01c480c2840013a2a041954541000045403c008107030203843c418505403840301c0100307803042c035035940e1030b040c0a500a000703c400c050541d509000503c550000d0010800c01c1c1c1c02000c503111480340210804070000c0e468903802d880d00d0340200380803403d1043c00e1036000e514091442841a4120b80851800e14115407254104440412001040741d0500a03584035007100c0820503110070703185003405152546040340e6407154910a4030009480c811851141d815190505c2011303c9052181c103003850208003929090103507500030340002c1c0b140070700c500e0a5683d0740111001002e07190314011118410152541c00100625039080d01c0d42000250020700340b1810b000c203802100c080f41e540c00140350600050039200c0220f81042011003003480075a8010403455000004510304502055691010902501c4003001d028114005030000c40d003403040c02c90008903158402d82c0c0324105980c442c1e041140d01c1459160140c00262210000340a80c2050301130000103011b043d046540b140390700c18103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 38612963 1250 38611713 38611739
    0x201020c100527030a11040f0204060c050f010c05071115030a0f0605040608070b181504030501050a090b060f030a020a080705210a020d03090506030708041b080d0c0804 74
    0x141030001400083d0301444120310483c99001280205251000080c1803400aa9a44040000a006250001041026540c641e4005034482d00072103820340d2565510500035040e500e080505849e1401000b100c03000580043c85440100c0c029500c81504050450301d400640b104003000403908040c0c004a185c1c4030203400c401461207001c800c640810305440d05102c00342900d865501c0140a0b60400d8010300001c0c40109442e8161104a080e00b501c41401c070b15084c044109645015420480d11082120042828030061043d20f018030001d100a403a0301e0403a41c00c84540d01000f401400902020540c5840c001c400b0301d424440080403119003030800d800184d4000304c1c6038449542c0342d010510030000c07420300003034585c0585c41d41d103000e10071120f104409684500c0c640b4002403007035144100b1201054024407165016020186c80c2a07140d251030ba001503c403440607503055071544200c2010300d5050910b0240b0905958641018240c041e0307145401340e5644801d41c0080b918030405110200b5030034030300a1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 38614213 1250 38612963 38612989
    0x30301030b012105070e1f03120c030203090406120506090304060c1112100b01140f040308031f030620070f12110105130309050a06080c030a020d0f0b0906040903120203040201020c 79
    0x180101c1241000d104000c0c950484144101c1c01547c00303141000442c001c51040003c40c0b4140c02e01e102050a98941241544240180307a64028036149020405040704090350380800e201314112185034440040e015076074000c510802e800038002015000024981c8075442c03410314400f51000b42080001da15482c1010351014810f0040c0e03550307819421a56900950072400f0300c0722950400d1415080c10b2841001d071040d0b000181c008000003010450000d0107a41c81c1030b07220b000210305064603480c0e15003000a80001008803010500821808482180c40c00441e6201603014003400c1031414640e540f2410001288442020b0103444500e41849100a025044c0300c0c0d5113a80c0b030400d40d5645840c01800752002c0d03030010750142e41d80c10300a1060503040b0101c03542102074040590340700d960b00e984650107840b586201d100c43d0760810380a01c000707881c980c0210b9030004c01240d400000c0d0350f03900d041c403003115100300d4050001020305607880c0c00d1405a600441c0c100b030041c41541d200c5802d28002c00c1e00790300020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 38615463 1250 38614213 38614229
    0xf0306020f070210031e020702010804021e030604060507020d0e06090103050903040909080403120512040303090c120b06030706030b01020c09040c0308030112060c0c020d140715020d11030301030b01210507 90
    0x40c0b00080540c0a9560b0840c4c1990606c00450504105400007403035a1b80c028030080c0140c1c1c0003511040209801e4191072440e002c000c0440d010740c5080d1500b4409000243c98100141c494040d028080500440d0080c84070074000d00100e0030101c0324401100034140123088149036000802003c9240d000c180141500030340282e0b80540d59078958079200d04980c1c221501394003040028401202551a1b0355451b94201e03406103008286006907050080032569507901045034420031104030340411140c10409803060780c00714196101c142e0f4072201501561041100240182c202018009052411402c001d4205006a00d200344054481d910102c4075403080c0c03c0b9035642c02d040108101085210300079071045494610340b0050700b80ca00e1740804c0f121182c01600400c031180c050848001d4000810236038000b068660304c22030051031078490113512030701445480c2c4c0002d14510260014140c00104603412654072014801722130b840d04c3c0746407490050600081444e4940d080c08540891410801400540048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 38616713 1250 38615463 38615471
    0x180203041b0b070b0c09010503060d080d1e0507090602030f0c0c0a140a060302090306010315020d0f0b01021e100504030c06020406050306042703050d02070203010513020a0f0f0306020f07021003 85
    0x19040c5910b1100c0300a001528500b1704001e80d0103107903405003d0300e810050944866401030030301e00c4c147e2030a000704450034601503d0410214104540000500070440f58800104401d1300c507100c08644001b194051500981d10400c5104280d5032028010300110a03020b0a4502e500b0381900010201d03e6190303c10f070f2000890f0103100c0c00c07500d024400c0b01e00030300542c10708615242c0888086922060140b0015082070341041401809a420380c048610341d081c10380d03042000d55a1907001c0c50040c5030040070240144280d0b19107000c05803904086600c0910450010b10411300e400c81080042c1c03400610440c1000715002940c0001111070010f40050320346a207400b52a890b090003400100c80e2349203945105080384100d00100303000ea450b5807054a5400d45022079554820701c03101c101034031074168000e42540c0780800b0040d49880d40f00440354002c0c8201c420b4480b1655900325a00e4050044c0110110114100000c100080069000b0121000c99600d081d0808510703400007010402c8035031140002c213442d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 38617963 1250 38616713 38616727
    0x50607030509030a0f210f0608070519030209040c15020102030106030c09060c0f0305090a08011a0f03060c280203090a091e0509030403050d021501080601180203041b0b 74
    0x41c01000d03408602c00b00110700b44001d508004001e2550b500d510002d11200c2c0c1c145584c003181c041c80f5801c030703048001824001da00307105005d40c1c01092240b2900642c3d00509102081c64a0440c032440500c4000c03807500d5001d0760450b0200214070001500407100e00700750010000e8100d40f558280034a11086800058403503141c120090261200701c007000b01004040c500501141c1c2d0001d800c880c61940040c004025190342c0e1405450303d10031829056403000d40c004e000541c00105412503140c00c6025030004105503203900a000c2101c200c0d138942c030340c0354100d5000508030a4240c0003a01a20302055140954a00158900b180352021200880d0041c0c0000900c20078a0419411840050007070b600200100c1c0b040c01c0e11400c40c0300d20040e01c850050340728030103d01d0003c0c0800c2620091a0042c05503031f6680e0014401035a00c500d1480f5614034445420000207595101140c414100d581e0445103c4445a0082c42d00001b035100400c200d40440e80d1201015044074030100d0480940300031034180b0740d5411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 38619213 1250 38617963 38617967
    0x240106030606080103031202091909020c0705060c0303060d0303091e11120601050d05030d051e0109020405060f070201021e0f01060803090d0201110a0506040b100b0a020a030503100506030103050607 87
    0x5a82d00310b0414807030907030010800203600191440c540c40b003183c80140c0301c4c1c0704c400028041c0003040549000f0711219410203c1d42d9242c0ea0f00500c10506280c086800031543c0d00c003840348c0c50050700300451503900103000246c0e40b03013800d081000c20a4403d250028886246580b42c4032030304039404000c00130424101e8070700100541071100305140c140031030700391180e00c4450741e00c155204814050103006c1c152203a000010001300700151484035240c2d030018405840d040340001c4043c1c0a040040300200010f100000b1421300300c0c800c0320142c4070b019200302c1c13404110312500c1e82540d01041080f0b0442c882ca507110050200071801c50300e0107a2070301c806841250b88001706682902c505130450400d40e0010003e5500b2603aa007966a0f40d49076085c2031401d450304519424070b09080700e910000e00345001340400c2208011040745442c1c032520300d202c440001e1903140c1940030703128094440b1240150b0300c01b112503c0441e0084018580c0400c4040c0e010100d40e840300042800c9410a034012100c07903100105211100c0c0d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 38620463 1250 38619213 38619221
    0x311120408040f0509060307030212031b010f180b0601030c0c060c030b01080a0c0215090106030b090d0909180b04080f0f030405071a0409150902030103030e03060f0c09060c24010603 80
    0x413008490901482c149400041e0300c0708101e200007840703441c965083c2c2e022003901b4010707a1900c40110109010b201d020559650180030070f9408220141e24000300500000c00e0a0803261400c1d41090001c600c1e999890015030080041e0314a81092000c0058001c000a07814000c150154a4943d0041250080d20002504c0b1403000303403003031121504051323940c44229070004401032203d00041080b1255100c044015005100e160000740030210314104001107500e00140c040c460503040d80e00c007540b09540303c1e0312808541c868007420b4490862010780c00003081c4c20742d003100d4000c1c4c003440c3c00c6071038060010b8801285074001c048039040c0010101c02c1000380501400081c0081074450f4901d250401001104601d41c8528000c8403252955a114900b0310348078442400050304032050110741d02d503180d0a014090f04c024003200d40c80380c0302d114001000a48400c01e228061920307000f805040081c14001c00400c0e030840d000c40c0c0c030544504a81c100d00601c0c0424000800002c000c0208119410200020280d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 38621713 1250 38620463 38620469
    0x1505010305060d08031b031f06022103150a0f0f12020a05060c010b0301060e040605091b04020a0215070905120109020108190902150d060618060311120408040f 70
    0x4940341c1010082a6140d03480d5039008694031203105982e070b0ba2200f9449265201d02c1c0c17a04600d203000801040004106041c8200c5440c46400d5082c102070354540341282e640c3c040d41300f4074810b4015080781040754401c0c6805590401140320b51074001ca58650041005e1030303040c7e0b0100b2525483d00d5020460304000980c0f800161240f15641aa07103401e139000f0680450091052070f0146500045500b0341020079880000e420307800500a11160790340b52070f04440309505907400c2c1c03032461030000031881144000641d4504010011070500035402e071441000000d4001403050301c1135000303140c4240d040362409072100b44101c274240c5030307040000c4c1498240b1411213400051290542e140c180c0003400360b03030401142c0f94041d0b80a1040680c00e000182c088010b4504a400290403004424030030640b07400c800050201181a4003040184996440c030884203510b561000711048030003050103000c958460703000f90202242c945011490121f50341100448050100e41c1910420000b040078490411442c00751402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 38622963 1250 38621713 38621717
    0x9060e010e0d02060702120609030306040f0b0a15091d0405070806010e06090c0403050d0e042f030408040f0f050f04050f0f04110d03020f010b06030903040303050d0609020a03150501 80
    0x41c804031900410ba0300506000041c0c491080450b5440c115681c00b0361040c0089076010580d0310a003006804a9682d80040d01c09922540c14441d034000400f0441c81201941800100217006182c84c0501c661b03034540002c8640070070869a0710f000f1030354051100c0c00500604030240d055200c0e29103030410905000c05074000d00701d03030b030050801000707061040c920644d04410708603500d28050700c42000c0710509200361350008040d40550020003410b1074004a04031220b80066a050000112903030a4041400c81120080061750210584c8424500003001441e4030503c1100c180b0b1034282c481c210fa01010f4060f034030500c4020601c11060056042403076000180340001d0740d0600c141e05202655000e0880014510941d040003100060240040503070a07240c3c1110160560001c200e00d820020340f20510050b031514598201078004c0e169003800c8040f02d20403c08100690709090840d9070840c3c2c2584050000307507940c1d07102d03030010500341e010748000e02c08007610752400142c6220341082601400407517800141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 38624213 1250 38622963 38622977
    0x1050111030f0306011701120312050903070b0a090b10080d1e0509030703080f090307080c01020c0108100e0f04110d08040b0a050f0c0604050f0a080405040908091009060e01 76
    0x1401203000800c1c1c0b4022512004681d0b240e42d504c000417900043d1244044000c942c0401c0000340c5401301c0d07600c80340014002d5031540c081d0f1001d0044a41130f82c1c0241c4070401c599008201d0940400d48008006800c211048400b10b40c40040c2d4a500a00c103200369075103000141441000c0040d1a0304001900c40d2007443d05040095801400f01520040c4c044807010050020009140145940030700c00300c809103500c20196601c904a881d01441660080b90096000b0300c18490081466000090b2007001202e050713004020b00c806441c01150307000c0c000303082071841c0d01c8404c00108410b14292680381c894081c03101c09035103a18003030410803006081e03205c00b2800f9004d01c86401c000b154030b138800c40e02903a000300c40d15983c4010035041256180700c2c020b40450128400303c1c2c1021412400300d1003600641c050360843c1c520170100350f00952200014038000b82190300801c42081076003015000001043d01031800b0500700710102e800701e82000c2108400e000000c80c01c01c03080c0419504011800c007500b6003032070600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 38625463 1250 38624213 38624237
    0x10305070e15010c02010f03020d0f0209130b060d020705070f080a0308060d0201140a0e03010501031415070903060b0609100201060608090d02030315061b0c041103090c040f0b180f010501 82
    0x2c4c03d1140c00d02c001034104a00346510040e464041d40441d511000b95400820081e203041d0030050007508001c10061140c005810103126500150003034039079a081c010b100e40c0c64040d8120b10000207610883d8201c5903400341e02d10004203000700c2ca07503030f000070800724001d00000e03081d034a0014040140109641e01c5031901e00c04010250364428850781c000e101603003070190f4800711b45605403050741040d10702c644d06600345030000c000c024002080900340311001049484503a01a03158000143d8102e03111800908545020404551a500718072407820025118a161000e40c0000c1418002d1510184015079102c900422449034403000c11603100c2e0040c80586002d080004000b91039200c060101c515402c804088a00c40b03a84070001c451440d081d01440001030750640785101c1e100e0314250201441203141c81c0c1400034030680c0c402141d110b88103102c0500030384204002040001d00d211495400b9481c1e4410f4041165102d102d03407070194200b8048001600d242c10094000c402405803c201d0404c40410014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 38626713 1250 38625463 38625467
    0x4030614070203030a0504051603080c060c0313110f04230106030b010c11030f150403020c01090b0a111005090a02120a0807031d04060b1b0c0306070c0201110303010305070e1501 78
    0xa41c1d08103a0b105c801050035126802c04e0352401d90905901842d0203440d50000081100d50402070900c01d40303040a0304c0496540b0030145005010840380c071407074041303040400400145642440c400c901402844020030100e0500450304860643c007104640c00c0107400111420b899a8861a0040a151030306200151034103000034025588450010209039105542d160303266002e104420800300240d00700da03113894616243c01d0304810300780d60542c054020014a2481544508000d00c2038400704041a450030756485412620704202d4000704c1018000c04260899002c55802003a0040a5100060400d28058010001400313094040a421507002c0400c030000510380c0400c1c0e52400f5090f06118514240389018428650030102d4100e500030324200c00071070201e0081c8043c1c05032021b845461b948400036100d80f16900c0a0014010781e0541c010000141500c0c450203802c031006106242c01d00e40b202100810520b190400e030000c40f502d412105c0240034042c0d81a8000d0f0f400f5408050bc52071100c030031400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 38627963 1250 38626713 38626717
    0x60a091a0108030f07051203040303021201090905070b0f19020309100c020f09060a0305010c030603060b01050c06010b18060f041a03040b16030902100c051c142104030504030614070203 81
    0x3440c5100c000b1501780709021081c4600401c4908211005035a882e251800038001c3d80300c02010b004074900074001040c0044144a07090003594400700030440141085030b05a02074000e110f502100f80c0f03081005914804018051910812090300299150f25461040104005419013900100304600c0101409030f554170421644101c0140c5241c403090311040c001c5150780906800c0a400c43d07082400c0300c281140d00da84144201d0340a26001c10101c000040111114405d070407034244207510070001031006961001c01048460b40c2200c0e21104d00c040c600110b100354001c000e01c0030382c4000124040100c04807002c80240314041210403107286141c6580e800c10101809000c8031006401c0791903003140c00e4061fa11280603d50020411070040402c00c80003061200071405c05c54090043d886010306000a1902a2a80d5105a00c039019115884112850160000c2c0081801ca03070300301d400040022045050b16014a0007951780c19902c07070450400c042601d04210040021040c54001c006203642c0c0881 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 38629213 1250 38627963 38627977
    0x7060e0c010f0e03250e0f06040609020f030402040b010e18160e0a090207060b060714010606021c08040206070204150e060609061903060b040603020d1103011203080702030c060a091a010803 83
    0x283c03e00b541440440041c0340110306401c02c08203051b0740401e1000c4008083da4840c8111000c0b00c0c1840542d032510040d0050740203e045070601040c060012038010b160a81000108203818900240181d0b9041c0004203582a2010703440801c4c0c040f0010302516103403000d80c04880740240d0600d010840541000314485000d64070440c1211540860100308001aa400c6031061407402012240c6800305401c1c2041c0d0240514010041e80d0f03c0d00c0d100061260010400000c0d440b118540c681c00c04c0b503c2d44007581c00c40402001280e114904004040040e40c82c2c1c8211031000e191410969a164280140c4006c8408054074140c0719480c18011003165a4131141100d0b9540c100814001c0707001d481820a5014101a41080c1c0c01d2400210b80030410350f6141d07024041c0c00240040a1101c000101640001ca103c01e01406030403400e108102004280185040794104006104407032070403000b150340506000342901c0da00714007502c0b094580c0902c00060341d141d18500d035003c580700c0d00d035140000a50380c1c1c4c89001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 38630463 1250 38629213 38629243
    0x30201050f0603030423030703030f030b01080f010911040911090a080604050615030f010e03130509061e061207080403120e0606150f0309010b190b0403030c0807060e0c010f0e03 78
    0x188011b402c401310640ca62104c0e00000c1c0c12150701c0e544a00d8090540400541484006407510304081030719842040d00354080d070b504540101c0f450f400c04030203102512500c0c2129401c64410800020442e03928468180b080d072075000d003140c03500144020010032520a40c440889640100103020110b180880e41e1500f0615400c074800c2e4525100b00400d0034880c1001c2e521409510b4590081882440803000300209951802d0b40500c841e214420070288550580d149500043e0304604460084180c0411031901d0000034960750402c0b2540700c10030609002112400000340480341440101604100c0501d48414080c1c030a00031060031090b9580c0e11000184258032a042441144004a11820480d400c4580d0000c9450b9641b61494600b80a030000c181d0341030041c0b14901c1c0d038110f04c0c4002d1501d1025202800101c41c582031641d1401c54010406020a480c0c1800401500000400034803648800c080201c0c050000c4e00040000034065074210b000010502042501070001c1e0703500403900c04911400c5d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 38631713 1250 38630463 38630489
    0x3021e030406060e04051b01200a1b0b04050f030703080403050a03020105070c020102030702040b1c0602040e01050a05090103032105190c0323090f010c02060a0c0c020a0b031801020301060c030201050f06030304 92
    0x3001201c00404000a88a00610005a1401540c00424912b100324064030500000105d0025291120f02003031280c44c0d0b0f8207105000921007840d00c241420510340000701190744003620f03501ea03007110b03030300c264401c1302c1d103a00c9910100d08142e020301419a0090860030905c0b8440403980010b0346074801c000009100707640d1070300d0103030640d51900005110b8200054030380d1107416844c07902500a612602504102d00a10030000849140c420f0403502500c401500101082e4650354040c0d0354640380518a40c0c1e10b00340708400855a2900d0301c6401d1203076143c11020546c400301c01c002c0a0858030000c501d10f040506000383d118072825804180c1e1140300e42c07030151014994441420300d00300081788003a040c544d4203011541c20800d0340018080c2c0940c1d1039600800904140b02c100703039914400300c0b000035080842c241c410451040c801028651041e20308060b00c07525006180b0765400c82e4000d030441c1c2c01140744c070203034641490360910030940d2201d118103124032503040500009980340101d2050001d080b5071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 38632963 1250 38631713 38631763
    0x40f05040c030603080a090518010f0e0a06180606030b04050c09100c05030a0801031202010507020c0105030a0b03100f110c0c040b0303190203070201080a0c0c02040b0103021e030406060e0405 84
    0x1295200600a5420005d903549800211100805032243c5100c1c940c420745040101070b4443d0040e01d03103203040ba58944604e03c540da00d00040c2c1c03207100f10010860008980e49110000780d001160300d601c822048110300003c2e65038109000070382180c0c03144494a0080d8600030401c003055800c80304880300c09030211b034a521062202d0a04450000007610000c5c6140008a101600039410a030401e068030707c1081c41002a02105a049080b01c6c0101c4080300103a00c600300281d00c650003440151f4010009003030204890260034042481d00712158540740d8019a100d00e5035070055070301c0c4101283c8004000c4518074040199031941d503203d03e802113840c0b00356519060204199800c00c1203940c46c15441a0803030006800000194880e000b0701c074140d01080b070310b000140c090411413051030f80383c03a66a11003002994464003030000401d42c0040150516500308601000a500d80c482601f1002007501e52595924145c03501e40c0540766168011040007070020244000140702040405005400e071481c40301c0581 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 38634213 1250 38632963 38632967
    0x3060307050d0803060306090f030d0b062712012a09050307031a06040e06070e040e101b090e070516021206040b06010e030304171c020d020c030102040f05040c 70
    0x680e51040c1c0d8420b202400c804100310b411400307140b048004806075000341d52801841500c524810750560020781003080220300c610a19481102d055001034442d07403c1035501516125160b81440356207003031451045c07101040d45000c1620079486d404001c000d0124071100c960647c50084c04512480c40801910380c52640c103485070800a00600000342100c0050b6520b051500f218044290581440c0440c1c500040d031508050181132410106140141100d42e07500304121210103040c1c225a500c91784540b0040f8600800700801c082100f0300180010701038980e01e140c640c02121201c0080e0501100700070400042c60200c170070790f03441240e90a00981e1a10740e6451f503c00340c0e8038040b000354401c1d88001c1ca100d0002c00054104d108038401c011014035a22500300540d03001c03c0414035142c0c10b034810081400743c6006d126040c50f01c0340a41040360140307041c076440424042c1054080e0700044c0e1005811f03200056040001401464007a402185000c0c105000e40781c00c00031601600340950346500c1c2c0007103014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 38635463 1250 38634213 38634223
    0x21020904020a08070e0915040218090711160303050406110102070c03030309032c010f02010f110a020d031e020705150f060a090b1813120f0807051905030603 69
    0x250040c0110354603426000302610902c1c0580d00c000004004101a5500d801c0204005000398181800007580c40c0d829010000690f04c180e884169540d0b500610b40c2d0652108607003640640c240744c60b807031003c88114000d540751a01c8189000030161390b0560420100c0e80040403035080d40e0051401b200e0400400c0c03d0f0b5400380c4290080200714984120000040c07603403607805000800d100359650386000801d0355006070f08000c100071b1015078071300160700e0810342e60045038003680d084200c4c0004107584100d200703460120b4100400302c112141000500c0321080361305011070a005072180c203042290a6241866060040640c01e8180d400c0b80d001502d10b0902c0010007a009404401402000891410f4401a00c2508003079441c54056040d184001c11105428020040c600c003001d04188503100080c0884451514042d081c00c0705080d20301200d00100d952204201e02c96103a548407400f9032110701c0002800030b9002800e80c3c040040520500808200d84290031100181501d070042d03c9403644000207080c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 38636713 1250 38635463 38635477
    0x606090423040302030417030c0606040b010309050a0f0209061002060708250c0203120c210702030303010b030f0a060501050a0809010f0905070311010801030b180109120c06060b09012102 82
    0x80a40c0700820042540c008028425110321506440c6021b400c0341d20240c1d240280c02000d205500701400140040c00c00740e11241642c001490f01203072800070380e01d4660800d200e020007070715410003c500210940c1000310354250072400076038011030300d143c030248029222030003d0010400c111074500820680908001c0808180814151003d0f041100010142c10840c0c401c00c2280640245400c0c45054803003c01911030304000400501540c0444500100444001c20807864401c2c130300b40300150160f141003002c0d40c0079180c034040740ca82d24113000c1000c0803606401010503030000e00300607007030000e079a004082d601d041d1280d00f00000301c0d40f00c00180304d01420705000d5a421071488c041c8404180300700066400205e0b40100746114014401da401100d0742802400041d2a513002840402c94006d145171190018006074000000d450f1059620220740441180045c00043c1d000c640050170b000c110720480340240300b040304540c500b40c1d5200028002540741d60350a42d81d4040c0300d1200c2c4084102c3e070111294 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 38637963 1250 38636713 38636771
    0x1031e0602040806071722170a080a0e0303040c03060506010905040e0a0201032a0c0f0609082203050d050702010c050a08130803040b0409021c0e011b03020306060904 73
    0x403540c642c00f0701e55a89804454850009a1000d200c85a80445815150003500c1c0c0c41e20a1403450102c10781c8402c0341400c0c103c210746541c04054032502c1011018048c009440c055a0b483d14241040e1411800362071180280d52960341041080c4000203c5209101d0216039124101007040e0f501c0c24010303201c074405030384402e803c94209219115442d5000c5506c01b100f0303100342c80c100800100136840f044075000c0b11f42c200807864400403c08144a003d0300b842c1005030701c41c50b04601c0e400c01a64811054134400e003030031a0201408280707101c0c40640360307442d50032001c080d910914030030713145031600c9555122100060040c05400100c2005591080780344c0156581c01c201140c07080e840c0b42c50000d00070361200c00301804000e480500410104030200c00ca40031031b03018282450a2608028541000398068080c0003a02501c042541d83c40c0300d03c1c0d014484a00b0340740703000080c041d5058000a08030780900c900c54001c0510410800c10710707039a100151001e0f03944c15540000c00e211152201c0c0c207112021201844 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 38639213 1250 38637963 38637967
    0xe0d06060602010606111903080907080304060e0f04051902090d14060405010b0901030f030503190504140d0504050607080a11030c01020a0e0d02091602030d0212041704030b01031e0602 81
    0x1d041e0ba015000801111100ea4070305008112031902151950514105603100e05c40340c8040d04d02283c4552902604000c0c03501c20381d03030190b5661803024a142d0260788504007241c42030100300e283d46004201c03195500014cd5060001d1725104009a070030a040c906008400c80e408503850550341c4841d42d001022551021001001202c1074100543d254000ca0f011030f200e42c01d1407910041c0e0f04150420b18100c80d40314800b081c288003580c2d01030b511600300420045840848a142140c940ca40b0701510303005602034030481100803441f448407410040100704810a00c60100b00030070058940c041140d4020707401c94405503c880c8411310417201e00903084080912403002040640c280c0c0c0041d40108074105c20361b243d0704540002401801880d001d00c45d070103507101011000007400d1b204045601f40c4501040c0c0705030391074041c45d40034810890700844e10505030b11250004000420100c003901c001340d10b0118502c203050502c0c542d20002e040c481408010019103004142560341c00200144201c529031201c0b0541d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 38640463 1250 38639213 38639219
    0x1020c0d18080d080f07030b090403170703060f0302010c020609030102040b0c06071b1103150a092f060c01020d050411040c0c0206090f0307050402181203090a03030e0d0606 76
    0x20034441000d144154400404032000507900b4001900c2480900580c54441e420f0751000c221403060034000346580249619139041d0159070707403007555283c440c5101c0d440d0392100000c40088546a200000c0140c000e051400409004401c1d40a1101040342d42c24607064407903110781d00c00300788280582c200300c0d40c0644c0007180100b1410102c0d0f011f03003044003204d000c80b034aa0303a80460860710003e85002050816011508082c049035046900c8100c0950203001c680c0d086100c0c00040c5c00e18001100c0d400941942c4100c20020030221014032040b0f15454690304940c0c00c00b004030894000e008003003880c1b255100058000e50000290107031803d045800c0c100300b1240c0b500c2d003083c48140308429041486140b03000c3c04500038902900d0406203940d0007901c0641001c032600180841051071401090340b62050420016103903a8500040001c5825a0b88000c50900f0a2050140e000980c5801003c1500280101c0c0e109031100d000c4101260303098031341155004110000714051b40d0341c6c2c0f031001c4d10040c1445404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 38641713 1250 38640463 38640467
    0x5010e01080d050316050313020d0b090d030504021804050f01050103050d0f051c0f0e10090201091d0a0c03020f1902100b030c151c0b010806060703021c0201020c0d 72
    0x2a4100c420310810740e008104140e01c100d0b02d42c8070840303030117149417901c201e100a450b04c90320103564080949098500728840c150005406055015400c0710061441d400f000f00c030302e07024000c40c405258a8101401a400c0c107500007042142088000e501342034100c7c00003000c2c06820000d40d4466000783d4005c12030740d610380c01c0168071401c0c01c00002003c1009496680540e60cc684212040100004c130000005400d204a0b070001e04800032003840710315100c600141c4020f005210302060301540740400511340304c0c039200142500016034000c1d0104491407182003420304040180710b503c2100c0030360000328040d400744c041d0000e01502040c0c0c1c00c0030700c0c08150325440840303128241c0144081c0781c003103500c0f50301804d0b01e45040e41c0c840c1101e5509174000071600d0109040088007902e9100c00010040d04240c0440c0d54100724403540a905610b030f64552031400541d50304501141c1e080030060724114504a42518080d5480f940444840810160705000640686c400c0d8141d034500d4190b0002c0d41d07850350301d210b40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 38642963 1250 38641713 38641739
    0x1b0601080d111009060b0316030204050a1e0902041d0a0302060108010e0a020f13150e06030109020d0b060a050a0b0c01050109020a0c08030709030605070504031b0602060c13090501 79
    0x84903154030500e0803a0840c01d00900500d502c507440a00140745100110a814010781004102200c202d0303141c04842c011941c041c030090044141c0c0c542c2c0703070344034038074500400040e140d0141c540d07072465181143c190902554110301038800d450110740481c1c1e94007a440800d000744840044902e4166290400380c518010116201c0b500314000c0d801c640460f40c841d042d0508035030082940762240e038807081340c41005040540100c9604d1500a050400c1400b9000d004400d413036400e0200d81110300c44c400300340400400b581d50940c0180703041e0001c00c958050b07a80441c1c9410680e1101404100382e00340024610b0342d440031000040e00f00a003040c805035581d482840b0380f0ba080098203004d2035007064004202407440e0300c20f0303030855141913480c1140d00c000c0b501c2d51580307540041c0201040051004004c40400c401e40505802101c2a40c0c519071380f1451820440b0340d16241084800c66030069007000c00682e50700080c0f0a8224070f400000381d558a50100072004500c4950b4013040e0f10605000000a05c654840744c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 38644213 1250 38642963 38642969
    0x20304030f020c06031b280206010807030b040b09010b040c1107060c120509030703060204030c030204050127020306041515020c0111060c031306020706050a0605060a02030f0a051b0601 81
    0x84640c081e10154030166242c04a0319034281c4c200324248005490700318140041440344020442070781c82c01070041e1821503c3c5604866a800c030170490070b800d15126034100089030041002102038180941190359444503484094806400000c0f007001003644400b007944007840d1980c0040c01003201c4140d6042c00380c25145a010f040409001e05c880000300c0b00e004039040d0b03081d1075000d01c01c41d603028a0384805030f4031500543e503072603018440d9160110000b001c1b4030080011714060106602924514070402058500c140c1240c0c4c140340e811030b1002d035185540d00500b5008040d01030056140d81da20000304006180c1018140f510708419040005d4a4032105182e0035460f18035400e1b40c1396020f1010054a5015150f0081c81d00c6921202c0050402c02c00c10014682242c9a404070405140d066110f20040e0b800035107040d69000c0c0c2d40c07424815283d403644030301030040a09450380c3c0c0c18941503200c040c0d00da028902c05103d20340c100240d0380340aa8880c408440e84001e80a4481d0b40300700e151528a40d841201340 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 38645463 1250 38644213 38644217
    0x100e0106020d050313030309080f19050403031d03190b0901050106030203240315010602030c1006060504050618210c030328031103090a020f090105060a0c0503040503030d02030403 79
    0x440040348251011035800d42d07228190b11040e2464032a8141400348001031142502090303a50540d07031000413002030051060440e4034030700300c1c1c440404031080043c0c0c205030704610040c07110810041000030f4000d05181d501c0c01c1d06954070480b401c08d11000c00e0600d034518142e0b0007011121998582000310100b1420700414008008214a0303803142020b404038882607a0500c00c42070321500c114440516604c500a1890016058501448189403003040d903c0003030b0010000f50300042000340716280208491507404900a000b44580751030300d58003402030300c40d03805400d00071000010040024200e01c4c886110740e000150903684400b80d010400e40700210f0051004c006130040d00cc4800a40c82c000040e14509a400c204d03602c408058541260044400c002d141d1003072584800c228020340c511080074502c244201e10280958a10601c10803a684010721f021600c5004401c00600c6181c40745025656002d5407070400704c030b002140b030502c20703d5400303260b2200d070b410b100000e40d0600300c601540103140030368440d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 38646713 1250 38645463 38645489
    0x7050d06090203060a030b04030203041505070204051e0c0d0905070305010606080a0506220e0a030e0111010e070605090607050607020d080c0a0c03120605190317180103020901140310 80
    0x240341c4000680c070050302c84a42c417411404e02880801d5081400d143c00c070b441390044918065075190150a8842c01c00412408518042020815400d00d402040d9005491010611000080c241c02148120019169011440004c80c41c1c04144a995101084141d00041243c3c802a80d901c1c00b036001e44824010b03400041e0b0503102080950155024042c000c45004100c4601e82c2221009600300c0071011000c1120380e91a0074507590ba0300801c0c082a0701c518020303030b603448502040f030002500d80c91401c0c130342d004140c2c90510040c0c0d41c48404500203080d47e929280183d52140790400041c160701400d08003509500034982401810341c0c001138444a03002c1140c40f08101c42ea50351070046800d0003050054004a4600300380080003038400d40e00040003641c1c4060000305292580081403845049010b10580382501d40c0090041c04407100181d440c0d0b0804401c070b01c1c0b84c00e0804091540031890010114103154000ca43d405c8668007680030740c40100181d4040648070718000312044001d0580f48141c01d48070440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 38647963 1250 38646713 38646719
    0xc020601060e0d0804030f0b0106030c02030c03070f03180801020d051b0d0c050415030b03010f0501030f0b040201030212070c0c0f06050f07080f03130c0503241b0307050d06 76
    0x1084860481e0415110646900c5150040c003035115003001c412640c0503401c01001c0b002841c0c805400098601800418000d50304003640501250a903100701c0381036600501ca0349242d032a00208031410558894801c0000740316a29003902c040e492007043c0402c1c03100e158004161984158081e00c6411080c2d81d01707100c103032079005401005214100320f071280500f00700403090540b551601703d20b28800061400c280380595445903400030000300900100025100c5c45c03c4141c500d030034050550702009030b140070000342d4510355450014070780ea244020907084950000070150fa000381c1c150b61041a80740c00740c02d014540510010400030600104458018003400c02103007030703002c000c4c6020565030b058441c1d030b147c040c3d003401500d00382d080280220b5018000b044011000e200001c0514040c102c607104200030610a840c6c0310000d07100c01e0300814084d42c40580b84030607003281d14900703201505e03040c90004020303100d4075448032041342c0f86030300f00b882c180000003440750781903121000f020b0001c09040100101d6071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 38649213 1250 38647963 38647967
    0xb040b010f0609140a080d050903070e100e0c220305060f010f0603020f0403020406060201020901110105060109030209060d02030111090103060b090d17070c090b0a0b0702150d0902180405010c 84
    0xb405120006966070000380314104844102d03446500d0000c0190b03002c140d40d904003504d400c0e24504281d0000e0004100308031181410043e541c00352140990300d09483c9003181030902840ba1500c52154240310440200380d051110708100d510b0b031a09980d090810848410200300d6100d19880221518403170071000441d181c05e000c0b40e060503a220300826407652480d210040700a90445c0b01244d40c1040704110003c01a5194480d1500411007a0000358a500c0c94000242043d0f03c22072615010364107110810400740c1c0c0c40000841501c1d41290814083e03201c0780082280001c0049000350158a044440d1107402075120241141d10400d98042c0a42610f8140340c100d41e0255501940d04104404c8041c000940c030f100710202c440600c52440360800d8542d0f00c8000007400d065100c40440d0766102d80c40c0c200343c00d1620600015103102174005240400030307400720f4100d41000d00c22110020003c10440d607103200035001054903640041c158520000b004130b01c034142c050141c904664543c60301603101c150b0740c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 38650463 1250 38649213 38649239
    0x40b010509010b030702152e061b0c0b0f0d0515030607020708070b0a1103030106090819020d02010e13022205030109050304270608010b040c02030f0706091109040b040b01 75
    0xd1542c007a001e80110ba0032102200c81c800f030110500c960078010300f540f010b4100b48100c4071000d255580b03d8050303464550b014108409214ad502c0420941006c4503000c0341640c0404c1085445a100055079036084905400c2d440c020908607040441c00d0405201015101c44088044040c003142a26483d45682c60140e90300c1306580709040042e080140e040058056000107801d450a550074a85042c4643c01d00440c10742d88242c00c090041408034000703000c42e007002c002101c4c1c079001807854160240a10b07000200e400c02c0c0c016000b4104072a0071907441d000d455003902800e0a1031451004c0d52110340303818122070340050070b070301880380b04da10328100107010302c2c050168000d090740090156262a04002d00c0d910440500010802c000e44103c0300345103030781d90510030440200030240001405e0111602003200b07440d8142c00580456100b4051030a01c1d076148403c42c0c01080c1c1c48100019420030914180c01c11004d100042580b1088030800c200602040e4840d941c815071141c4841e032500d81c0c84084964003c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 38651713 1250 38650463 38650471
    0x4090b10050c1f020f03010e0103140607050f0a020f01020d0f050604020a09120602040302100c0506070807020613060f09060204030c06050316051605060405010f0c030b13020708040e040b010509010b03 88
    0x1d644928801c2d00040d4606000d241143d54401001d1703c0d000c0f14104004255000f07a2101642803003440040003404003d03d0f005000003c01c2004c0c01a9041a1000910500485101001a2800092088500d402084044140f41e00e0300d00075500d8844104d1031500600c0c01019a5440c1d50a2000103230070b03882c0074802c036500007d0326114000e245091294140b00d8200b0804202c42040e0b080001101694801c0004c80c01b01446076151420800c6501d80282050801b0300000700307211031030b418002c421703801081d4a44e002d1580b03c801e00c030740c051f24142000a40f114103030300c002e29450030072032405101984e002801500e024954440c905a40e424046540788001c692050100c4c2040752804041403180004050580c1c1c0c0b0745040214442549816007010409d80d0211800c3e0f54500700700740c0704502c0340191080b440150904100125081c008034086082410140c5051b135030000d90b101c100000030099801034903011451101d85c0c6084c0c90240c0f00400c081c0191845550351000000d502464042140e00c0703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 38652963 1250 38651713 38651737
    0x120b0612010b0304020a09060e180a0507180f0e0109210503041509060507080a05150102030d021b0615090f01031a04020f03030a120e0c01211104090b1005 68
    0x5030320b440d5205480740c00181089034400c0385841d0000e503411040c05808064580d038550034841d82800b1b0041d02c0700b8110703002c80404507000001c01c2008105d001c40d14804582c641e04c0e00c421150203105011008100c039041056a41e413a188200385e0b20401540204c8816100341c00d804800790341d260304083c558030080d00303e000044040000800040c401d030f1003040c0a20812034041500300030765503140c3c2a200c0840d0b8007000201da14040041e10401801000d4000c2100e121084400c00d600d40000d40f2449065145500b80f500040c940008a201e43c601e41c2d504561981030781c90904000c0820300072203010310510783c403603204000818036041e901c15540303040340d81c010780b0b04c0307204142403407058040c0c2001441a03074031511000b0308155988007070004228201c140c1e0385020a903181e148040701100c034400c448031469032108800b11100d0741c00010700d80148001c02c02428a00c4440c2044c1d40192071640300c24808900041000940004560802c12107507004849280c1c120242800441e018000d0b00401c400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 38654213 1250 38652963 38652997
    0x5041401060f0201020f03041101030f110703030e0f06041b0803090a0311010201060b0a030b0306011211010c170406030609050901090201050405010c030c1a1803071104050705070210120b06 83
    0x74042c40074201c07448540d000150900311803e941d07540a070000c1f80d050320001c41145250240b03690604c01c41c0048003510104121244184401c884240203515008091596444401c40d60304420080d016031907490404940c1c0031b1a15280182e0204600c3d00e0124148041d8400843d114801200346c0750141e0740606902055483d5072500110250716811580c10355680b0b200110310801204020000003009880116022502000341440c0a0050344a2000d415410901078005110340e160541d40f5842483c144282042c1030410003c40c00030624540c200d0030f07000400040e000d8058005030202d44114908103c540da50300c5e41e4500b03035400001c1c0240010004c104c140300c2136025141101e845030283c41d0003d0f5141c100e6440e01c1036814041801c005122007081081404400c1807041c440d2100110701a40c03d02940b944c0315458141e4034000702e84a1519140068241032144099400d60303500100655030f07070407031000c0103014a010140c031808010f040607104030150500104a80001101d00300c0c00c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 38655463 1250 38654213 38654219
    0x60f040f0206030601031b091703040e0f090f011b0306060c0b0402060d020c01020c07050a060f05090609040e150403030b100203041802040b0c030a200a0b071407050f0705041401 78
    0x980b41d407008060505240d0b90f150454011003110413a005100c25507110105880c6c02c10b050002d00740b10b02c11040701c00780d000300000c0c40790000f04224a070f0420140010020103468041100d402c11003507020341c00740d80d0b107030034003020300150442c0c1d0169150403552020048941c44000485642d5111038014201c20003040100d0300504028005201d854211b040c0103003000c031000100350030fa91050071502c0069000308001c2c012450580c0c002002440103041c0380d9a450386410010380f0b103002e26000d03544905804a2180c0e0192034a400c140c2c4a0203650060b0b0350600d89102d04403081000c250b40c01e40009150401046450070150100c004101e1180c0095040c5444c001c0c81603880d80010b40c40e000002c0d0203210004001030720303402501361100c1103070203180c8036048940000c0c0042c104024601a0f07a03040c0710030714a0640c010034440390082d00140b030400c440d035450000b61291448107259001100d03000035a0b505000010500034800c5e203202d010380d07140d030f65102d08000541383c415110818424070f100c010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 38656713 1250 38655463 38655469
    0x503070209040813030503090310020301060206151c03030207200d0803090f03040b0406180b071b1809020306130209061e0a0e072003041202010c020603010b0903060f040f02 76
    0x41d0712501c1180307000d1401d8030b1a2007164044c8005d51048400354004a2048050304c0e050140342d2405d160314004600710b40c0f40800003540d61030064640e031055814007480744442c0d21902219240341042c0012205513211310300e00240290710407101941c203c0660cc9800091840d152441c0c0f01c601d00c02481c441107103600762a20400daa0020342441c01920032911440808007051010b04001c05403030022a46840c0343c14405030000d21000002100e0b0401110b0611009141c4015100d0440e080041d03418420041e179603030001c440c60b5803c02c81840d68528950144004d00e03400246e43c8504c07d40980c0c20a840d50b038561900701c0b18501c402988091120001252030030030641e880e14404000d22041c1d01e03580c441c4c2c045609060690007410f40d2000403401c0049117500986404054829201d42640c4070242a480c55128001c83c0100c26190080c030040e8000d5a22039501e0022941c0c00a00060341d075692601c40000951020b58058000d000701400154901c0300004035510480d003140f8280602181070b030030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 38657963 1250 38656713 38656729
    0x10603020f090a060201020c070f0b03010b0705011503060b101809150308030705031b090d060b060408160602010b0105041503050a0e0f010c09050a060905060c121305010909020705030702 82
    0x280c8070461080c08402e815a6401450342c0c000c2ca903035000145e4a241480c400c5041400c1034001d60310f00c0f01505030800403005503100b2a070440c1d50b0000107540380c81aa00d4450f001d0440040c124092580b0300c50040140301c9940c0c4001c2d81c0c0c403070072264162050311546059071a994407030555012080034038070400c42c41d85190881c9048003424000514015208d41d0703810f9041d041950008000740c4084200111030b80baa5078031100303001f16482030300c2c02e20464000203400d0301c82c40c12000702525150591030f101c5454040c242c1d130107459030001307580c402100192001d150386081d21600c1d0040d030070880960301c0d40d4000c070b0807102520000e01c1100d00704480c440b810340c0502805007070707554219651003251324040c038144419141941c561001080c009400711004001421075002148039901880e010400907400c202d002045031030694000d900c130404400e1721418441103c1d45014400701c001802c1d20704201c5104500f0580f0000d0700c0300d8030b80c642c1382e1001100701e000f81d00340141580c0c000c016540142c644824 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 38659213 1250 38657963 38657977
    0x2060105060a02010b0307030308100b0304020f040b010e0a06080a0609020c030f07050a0b15040524090402030a0609080417010b010e040906090203010e010c12050f13030903051f0e0c0901060302 85
    0x11800d0030305c0c41d010a02d00700199109800240342c080030b04c05a0078040000704001c003000d220355800c40c00c058001a10844a86028030720450b41c40d180c265080e4010402c413404100300800340c100307495444c040600250b000b02c4e4802400761070301001107107003420f9100b941c1e019540f00c0020350600c20a940c0da150507902c45102520f6030300c280c100c1c42000034a510245403281d500b5601d030803125941401480140c80d400b520706800740c165044800d9068201e10b140c01c011210032610f0401c2510f81e4000700c0d0810460701c83c09800142084484401d01003071100902c1246c0d0940c0450116907000304800c3c0c00c80f10440700480c00618030f00d03040304003850039030040c1d0240c500582000030b0f074010541c0000d003140e00b5410a454980d442d04007624407190000d81e8428100c068880511031442c150380840002c400042480c1c2d00d1101c210585400d25100d02c0080014561260445034255000744070201c01c0403480d61014401420116141c0300360502141d10740c407200c4003a1100400d642000000c0d000703904141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 38660463 1250 38659213 38659217
    0xd0608010c08072715030506030615040213030209040609051612060f0f14090c0a030b06010807260f070201090b07080c07060504111507050c09150d0317090d02060105060a 75
    0x72103522404c10350081d04200600c0d101c03100045083c592040501614001807000384260480d038100404200c050f9015103158900302c2c4d006070786a4513040e550050b22540d81000e904244034404102c00c003c05a480740a400c0d0003030046503203199004507000407140d40c1d80200d42c1d48102c41d203c18000128141c01156013004020008100041d40c2c04180c82202c59482200d000340e0707140700c144501d0103400d00c04640c030100262495685981140c40301403080c20050f280d00e04000006000604042c424841c845282c050240d040860b80d29411591502010aa81990075010313941c1c00b280080e40148517084410382e000c1c1d1056001d507603500e01611807040040c43c41110440030400b100001e5102e208052203070340310f1007005603204880f5007808541c010b80300d04800b9a00041008001180000031900c05006049130389482e00d6503150080941c1e8070100c0d40c0281c11800c26030701b01d0304050b04001820b000704901000440c8903030300d400420381e0341d410b8a0602c80142c2c0121005220604001c0010801c09c6100c3c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 38661713 1250 38660463 38660507
    0x40c09050306070306030b0c070c030803040c030f05210a080a090c050303040e01080c15040e060609040c050a030c09140105030604020c0f1e06061008190e030d0608010c0807 76
    0x140d0119003840400c60702c03500069039030103050041111039840c0c213810800f110a040d0808940d9510500790740d03650700015013909008000036042090001009000d540c1c0114621070b0040d05240407562841c151040c13030707800c5642d0b00703013110041c2c040e02c1906c1108045644404d201c0c2c0340e5911803c000c01103020140c80c1003001e841c0124081e20108000d0000b0108644030000a40c5010351403030400201a00780c9114244e081c2280103085d004c4c0c030580e002c1c4c88a07241c0c0158242c80d018001001889008695034120b8202914800500d030050003a104124007528207100c0c8034113405007101d100045000d15060440240b001c454194403c0025650100001d400140340c0351b02c110040d8900076407109441c078a58010026020b606c01029002221942290010701791403c01c01d00003040300c144000f40e6003c028101000901406000d01050a901002c00c1d04019003c2c855419548944c07100140c01c4680b810b1250000300940140320308a812034007030380d030708200c0c0e150003a0464080304c040400d0a208110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 38662963 1250 38661713 38661719
    0x203070c06020a020c031b0102120c0703050d0c0302010c0801030b01090906020c0102030906060a06080106121e060b090109080309130c1106010b030a0e030913020f0c010213090b0a060e040c09 84
    0x210320060683d10002c1d001844110000c2d02054a45034841ca400709100f55240e6802d011039800142c42040c1c21250950207403649000503010f403406a05a0014080340306060714040c10070303000511900000d000364006d11903a8540c60302600c8025080c40f0003046902a8801040b82c0407051b03000701c4030140701e0440507142c45401d140103826038105a4031035070660071480501c0303000d181000110005040900b050078481d8076000020b000d408005a15224154448120301e80c024000350f451000c40e040104200152380e1501e464941d5a00f091040a010074001c0304003084240c8008141c44031045d0040000d42c5014148003518082d04040d01800280300610700c00518a00c014082d103400303041882c400350303201e1a2007503035041514401014000150404c1105030302a40301e03008401700c8a81c0d0250096561b118018000d03ca134030034081041c1542d4800310f0304020303604035000070b04101e900716801407010020350300c02c1020341c410600c100c1e00400c40b031364006039090500d03070800c000198450500c0c00085075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 38664213 1250 38662963 38662973
    0x90e16020d03200403060b01170f070c020a08010e01060501390804050904030305150d03020604170f27120a060f090605070c0210090b0a120608030a2d050702040203070c 74
    0x2181c0c00468161fa120b0000307290a50740102c607508003220100b1960303000c0c00c03d10103142440300060040710410800b400c4030019520756025000042256030002c100400b03000001034000c04180c004e460001744004080c86410910b403507110300002e840000d682c000c2d1022081802002c2c110001210380080500c00090b80d6515100321511550190714049006d1411040320040780030003041c12440758020001000c0800d500143c0a80d1041e80504031640d0210001801c0d0a18022070004415811001032403064848114044a4500b02102100b503810713400d40b010401806a403114821441d400032102802044968001035030110a94000007040d2100340c07a20000d88004560100c045820f040411003141080d070780864222000d458559000c07070a1005c08030300c9201c2c95a0710010002c03061012940494281c0c009001084107100b20ba41e00c807800c1001508409400c0001d1007003140034009010381c0794505019005100755aa21203150440310b90810000703410207044401008040c490002c0010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 38665463 1250 38664213 38664217
    0x6030f1104170105010603110d0b0d02040510140303070803061905090a020a120b06040b0a05130303020610090506060306040e010e010501030311010b030715080402031507090e16020d0320 82
    0x400a090344a4800c000202e00c0b0782516010f80c40300381018a05141e1105072211030094940007800c4040105d1f45681240004140d60000c05002e94441d16160a100c1c002001d111034000b201e01c01585404000000000c143d100c0c00fa0b904041c20107442040020040c0c50b0092840b412800860701c1c2403541c0b902c50012990700e03c4100c4141c031940c3d900165a440a6403c82422007502d815880240152050300012610f58052031041c050300c3c20300821015007280c05001910340314148004c0c83d100b03103641d0f070034001d5440109441114640308542404100361645004040c030401018000f980b844e251002407000403c0c07071401d4245195695000385e2007005003030286a008500a90710320b2000c04401011500311800260a50300c2a84202000c10602c0f02082000d900b05040c0c1c14542ca0540d40c41c00031070304004a03240700d40741248042003003052981c1c2100b44e10058136464250711819580742d941c6088820106108503002d039100c4c4500c00b08a911942210074280102c414104c0c5e0302c084458984169 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 38666713 1250 38665463 38665469
    0x70c02011b0b01050a0b1905031b07111009030b01050d022e02070f030c05090a09020a0306050703230f04050304120507030b0c0304240b130b09010501020309010906030f1104 76
    0x2514005004001514042134540041c2603446183c0e4a0032130f00105140b400141e5a81d03103c1423200c04000181aa400f401d140c0701d5000c0a5a4000d43d80c5026113404c0d4070202202c1c510600c50311009042c1d04040340720f00802c105803a8051103111091f401e01d0b0410440701c2c10701000300c0c0c0c05091148540c6040101c1c00c0201c810746030b40312402d1f4250504002c042e003405440e420440d90b01404110420102d00b01805d40b03c1182c50503075240320a0740355a441e44c0041c0912100103508108016800810803105070b1000384502410383d0b08120350715402058900652442041000140381000401c400c6002ca0407000d401522940440f480c00e680c61107c5005c3c00340e110300c2070320b0a401040c2c04006102c0840e1600e83d00241620030f061647c0303066500c42044103000c80b03180d000c00700610020ac909895680c4408441c1800400c2e002e20000040340c0d40002c0c210341120107000d41c0703040d000000d4950000054039020001611061001424240210010030842c18a114403940320700100524902450081c006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 38667963 1250 38666713 38666723
    0x603050703060f270b0708090d050c01090b090d03060503030301030308010605030a06030c060e040e060702031e04050a0f05120105061516020a120b0c0708120a15270e06070c02011b 79
    0x10100c41800c1c0700c85c0b440c42c01018041844804d50820041036404500302d070070b084040c102940c07503a992922850042c1400b000040c051102013050000714400007884203100003c070396040c003c294030ad1040c143c480c0028440100421007150040c00b10070701840c09998401800c840003e07455035280caa11204a90347c1d0711484c04a61080426903c0e4103050244c058a00d191700000c041604207500029664844e5202046240ca10b01541049c100241003c40b00144002401e9540d1991501c8604444030300b9441001c3c46170284982c01c130984101800b0715885201d00510a8101182604621f83d40b54006c039241c5040010704081003005944611160019044901d81a601000c1c5442c22032898000035100340801d90b024842a000a25128101d0b60704c0150b0558004007074440e04003d00240859400b4025040c4c1d40603804a0070010342d04c05451240c180090050b214051040301030704444911108810a802040004500900414122031071030701c1031519121ba0600103400d032581201000017110 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 38669069 1106 38667963 38668031
    0x71a04030b01081b030616080604020c190506090f03160c080a03020d090614040e06010c080c06010306050f090604030f02030c1504020a06030603050703060f 69
    0x8541c0052407144550b115080e641e1079140740d95941d85951580b03a0040b4103480c00040c601c1c0200c0d018503c1200d00401180e0484400c20300500c1c1c6038100340c08000720050b500c803c0010034014802c010342885011802c0c58443e040c02c0014102c05410381c06015005c1c246200801241c0c514110252200b0048980749400004180540c0c00000300e409500c111900303058011411500e104000d95480081d1a12004c00b42c0d00d0040c00c40811031107900501080c40030300400300c6216000241410080110800303a5180d03445036124141003440c45c4c015800401c1003228501440b0740219042c0088441440c3c01c8408a03900e800c014009000c01003000103019030f840c024022034003410030310019584039030945c0c0c0c030524460000b0b803400c81c024440c0c420005020361007441041e050b60f911030090445145117880300405401c040c9d900303280e195610004141c990b11011070070703d56192859030040c = true := by decide +kernel

theorem cover : BRFrame.Cov 38489213 38669069 := by
  have h0 := BRFrame.cov_init 38489213
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38489213 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 38489213 ≤ n) (h2 : n < 38669069) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
