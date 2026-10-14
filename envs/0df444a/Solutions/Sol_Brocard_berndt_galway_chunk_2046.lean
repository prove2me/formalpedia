-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2046
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:31:41.739975+00:00
-- url     : https://prove2.me/submissions/61362cc9-16ef-4c05-bbf5-44bda16a5c19

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 367805755 ≤ n < 367985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 367807005 1250 367805755 367805771
    0x9050703061404200d18060501030309050a08030f0a0306090f140702010c021b0a08030307091e080604020904061d070914060a0e1b0414040b1e041d03030c0a03 70
    0x9002d00c2090b80301c0d40c0440f03c03016460295039944c54560412603610000959a166580a03010152880210b0622508000806604514014100d554a80c00003401003000c80c905220199002080318020605801c225032074100140d022030207040d01d0780291404500304440d00030710f03203c10b8000e03640c02c1d1613010441c0c003e81d480348412400c071a0281c403c1001a03110b1191091400c1d00404c400902000c042c0c02e504045454a00e998510391050755003400086101c082001540e0403a611580094072034840144442e01d405401544d0b04c40241001c2e00c40d005080100d0b0400805034000003014184a5040d084403602c80d004684614480c4901c5580d82e09041c0c0c1d4030140d42c1d5034030f030b46442050014601c50758182841c5c3e0400386060000c008085a0b064803001d2801d512032180500000c2440300c440d030f48441c101d80180019035a00341c4541b0f010f074114240e0031420405c21186500041d406030b0f00000c03481040ca103417a2003070082168801007070000000b480342c829041ca00a1800350f403240c50900c0808 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 367808255 1250 367807005 367807009
    0x40c0203090612090f0a0f0605070e060d020a030f0c0903020f12151b07061b020f0c010e0f0a1203081006051e1b0309030d02070b030408070c090507030614 68
    0x8807400901d594465010801c0d1082842d41150b050f070480e000408840100c06041841032925440c803400790350b0106140e1000341000000c1c090b1503408501403409111000000020442a02900c0c554114203500030442001191080c1e01410b9400030001c014021002e83c08000340c10141c2a0005034040c0e01000100307650b130308200c5003405000e0074800003030540c030a869005e1150304202600c4540704282c4403100000c241d4003000608910760141c0000510402c0c40f080460380c1200104800003950407040007420203600210705000d10410a0078401480a10080002c45c8240341c800510303072188807207602260303c1f01c0c3d0800745100d040c840d03145e1840d29118041c01c10b40300c0c2c6082c8130b4100081d00c20410045d005100c86024a2030b040e402e4419802e0083d40002d09000d0032128042403915030001c00e0092603407600f0081c4021008050000d45010b6081010b030320340c10300c4014009040c40b5400542c650070001d01200719001040040c0d010000d0703040104004010781660720030b440700800d018140788124 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 367809505 1250 367808255 367808257
    0x10306080703060b06041a041d04050d111006030c060e0102030708030a09020f0d0501050403031505030c150415020102030403171504050402060c0102070501091406060d082b0902040c0203 82
    0x1030360400d002007105a2030740c2c0e6040b0103403100e4070b5a076401000a0000240500e10341c03060105e1240c480c944241c49606007550103050a041880380e68507803000c6014000400d0f1301084032610350000e851300b40f2880d03030020021071811031501014600f092401e45c0000034819120107101c107031401036482032900000304004a9690041d00c901821000d410000300b5111412544241c8800f40301074541a04002c00e4000a0003c40419005449a94440c002c101c00c042d0301d4800c010050000602d5030741c0050900c40441c1c1d884403031013a41401001c4c802e44141712041900203990050900c0c0c03c1d4042c1c44011b00c10700038040e409c1a1400c90100b265a981060b8001c005c100c0306200e07510b2010703181e000105120400000c0d0030b000d0820780e000002008412252002800106100d6019800105500800d40780982c403180184640810030b0b0044000c1c40110764a0200701420140c1013820380791070b04c00561a4442a4450942c10f100d1450a1400d9981da00d68540261514a00860f42003000e0035420f10241c0e12 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 367810755 1250 367809505 367809509
    0x120703050d0f0f050a02071703120703050c041403030f0c071a0708030f061201022116050307050a0201140f0910150909030311070c0e0a020412020906030118080c0c010306 75
    0x7050141000f140c41521841c0904250708003841100c04940d641d00000082008460807103a0941000aa1140308100c84841e1500002c0e24a0104020314191040609034081e07801030b443da07050090f0410015035010426507a0940c0d2012407265601c0c0742d04001c3d940c542441c814291803d20b02c00303e0304113404440041d142d90640007100c4915603034035051018842d00000744207951140c810a40790010308070910140480380c0d86a07031000055840b09841034010350b001400c642c41c911080481c100c03403941c000d082c1c94207d07401d0f06100c4d444e90510751059000d440c40d070f490000c000c400d00e0200044030041100d02c60242c040700c01a20782d40c9001800b103009440f0710107001c41c40001840801c00890702154000382c40745000f8500050b40210403c00c040d065404884e05540d030109025003030080b41c00d1a1941504120402e2085181c10f180104507032141c40030b800080e208040d6100010200d403400e4010154084504140880100152914800301e4111100880140c4160200080994028828041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 367812005 1250 367810755 367810757
    0x50c190201140f18060106020f0717030409090218040f02040b0105070b01060e0d0b010906060e060304050c010305101503090606210602031803040b1804050f040f02040b120703050d0f 80
    0xb80d260350300681c0d03048a54002c0c0018410415a49400c3c4050f02c0512a032400780071150f001e044a0a0320382035552821116406c60305000d200e000c118688500e0001c215070490341101404512107030a400001e421200029902c038928074400104130400c00d502c4080e03030949200300c1e001c21a00001c040111510300034030030010201000340c001481030742c0c0688100160070070010210356000304180e0312100300d16000ea000050300c43c0c64440c01e01c4840e800c80e02c4510351403401c0d10894190325091f110b40e40c3d1038907210051410316590304089001101d0008c41c40000d0084c00764000700074000c03a00700400810441805851040c50144c002c01c040880007ca01c5404030064403114052070b450312680000d500240400d25030252081c000101c0140600c042c000030b09680c80342c140c68101c04000c00d170111000302546441940342104200d80580002e0509400a402410001940803544081002025040700c910340c4900350008590f040070b00021500d0036a8400c00c25503980642e41c5a096403002c10022a002c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 367813255 1250 367812005 367812041
    0xd0504030b070c051f090203120a1e05160803060109050303040b0f0f040f0305030316020606090a0c030902090a230403142116110f030a0c0c09050c190201 68
    0xc0c1d01c1c1c40c4514043c0801501070700503101e0ba291005070a42010000d030071404a241d45500d550341c10f41c0340910400c504004189007d40c40e00101e04002418081054902c1d201103c6409001c103a072845170b800d80c1c14100700c486039140040414103048503e600110b807058002804840081400c3c01c02000740c804840e002d0031202e003400303080400e00501e500b081d102100104028400020100c4d4094980002980608051946c031300b820513445440307000c0c4503c3d40096510201c240300c07850b1509401c2944c40710441c3d00000321400d030b950044019006079400654000d55400c03d2040342c00d26540f08904c034200d0f0882c3e0180e642016aa111032141085a02034003003030100c06a80000300e1544024401006911464000c0380d0440102e284040805e54104045504812004294507008858207440d044094010041659501d000316564030031140d042c000c100c60030f1700b2042040f0312400e83c40d010301401d600600148c13034030002c201440c1d0016803020b0b412815284030303401c980f4010b02c680b1809003112000e00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 367814505 1250 367813255 367813261
    0x90504020a030222060206090319080c0705010606050a030c0c02030d0c05100c0806040b030c0d230f031306080709260d080411060a021b15040303110d0504030b 70
    0x802500002084400d143d000c02130f0400c0e450b900b07a60702c0d03001a001c0c420a982281485c2c40207281c01001840c496166204010502d01c00c0070399004031683e8141d903e010300e20365680d6122501c040c080c0d16030042242d800c00a000c2140e98004020b0910301109580c1005140000b044c120f40c0e54004010203905904005135046c0c11324445e000080c0b041d8000d008441d4051041c0000004540e070610295000a07102c070107021840c0b406000742214400300300e0040c0212648100040c151041c0c82c0401003400d88041c4001c405261510504040786840d00c0680354808103a00707d140d101d9110001c881411b05050074003142042c02404918001c8080d50340c1d00307240b45d080c42581f41c8100f000111303200d074800001d5800384095900f00302c0ca03070030360f0a00d5450354041c1c00c0615140c00f040c000560b005d88140c509000c06020a07a0000d1440d040070035040e641c0101d8400100482c5c4140b010b01c4032603069400014012042c1600b02010364203c0032443d08540e840408103508032000d01131400700400e010740318004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 367815755 1250 367814505 367814509
    0x615032306040204050306070905010311040803120603010e070b072d08160222050703050c0904050604060e0c0c06150f040507021524270415050f0f10060905 69
    0x1200e6031051024000524290301c50000038607002046a40700005080348000340b00781c0d40d240c080c41d991464410840b6041c11f04040c0d0032a1a8051614411103d020210001b8040d581c2500242c0a03042040306545540b9100e1102c2503481c3d002e05011341c1c2c40e0100c401000541002c80c107001d44001e0819040c1404914640c2c1c4008240c0e10038140590b41841e50004d42c405659166001361003031722800d0034a5a091030400003842500e82c010300c20b000741480c01c42001250381004040707854626045030300203281e0341c0ea180000e000b840207821039201a20b50808019107603091000411119032603000b151650303030b241c1d02740c0302c00341040d40c01c0d0b00e4005080d0170314002e8909240c0c2090703030070440c80d0064800d000c1800f84840200d140464085800340e2024a414007403141c281a000c0803200140c85a04c0c040c0b241c03403291002c500c20018940401e4602c00000f9043c0110882c1240351004020000d00a50a042250022074042070307600d4808001188081796050300b00e1540d03007048422039121588d1517860402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 367817005 1250 367815755 367815821
    0x60c0c06020f43080d0515130501080309010507021302040602011d0607050f030403050c0d02030901120908030f04080f031e011d0708180a0b0709061d0607140f01061503 74
    0x1c0302c00c082c0500082a032100b2901646100d007071000c244000d401d4001d01040b441ca10080c42108c80549454014002500301000b10750b2442401c0c00c10781c2c2c1e100000e1011136542c4180030080c000c150301c0882d002c030f00c00364190851142a1550303003c1140019400c404d641c2c842c50207071050b8011820411489590b581c03004091540140242825410302d03659410503410480b8004841006820005041482d90307000f2641c2c921140c451a07041044140c50b982d90a5076200c086c1404d88030b00e46c4c9000160400c070102003105c401e03c4020b61004d03140e00340b14401180840c8403001b200100322030b590010406813190b4440d41c070b00703050404988899031100c01068400c40e40c050165824140343c084003669000c000c11100054502c82c0301c4402041c50100402850143e4070340008080002c004600c2d03406144940040c44149411101c450795007485103071001c41c1d0b0b41c4060709002c480c001c040c140d8001c1c120644c0710070120b41014032021071400b84010214100d95040c004540c80751a40700410341c8000c40300e070b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 367818255 1250 367817005 367817137
    0x81e0103200d0c060908070b0405040207140d09030210031122170a1203092d06060e040201110f070e090f070e18010612060c0c06020f 59
    0x7101412010054001240712408100401d0321403180d02d039010407606521881c25401000204094400c481c10440da818041c4505c1c840c09125a401188400602c4001c6403064040400300085030480045554003801c150001e120036403042d03480703400d4105100e0180c0501c400c4080c02001c0c0380e03e00007020545110b0850b0181c06030b808181c1d00100415200c140c0c031498000403035039800030720301d425851810201d64060b12052400301420f0100004c0040d1040d400c1c031041007400715003881555100410341444090f000c8000e0705040c280000010702862a100c0180030324000e0340c030b0218480381d400106540c0c00c032800036803140e980241b004120590f003c880084d000340021054aa02e40401001c4610300303600c0d41c2004220003105030034070500190311b03069602c90301069802401520310b8807895145400c20100c01801c050303200c0c480d611a41c1d10403410840c010b94000f900715200c5d801d088000d5070760f80040030040700c0c4c040c20109000002e09103c4001e1440000b448580d1000c2c9a40700101400f4003580d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 367819505 1250 367818255 367818293
    0x2010818150a14010f03020102060103120225050108060a0b04150509060d060f1d0406050c07120e03101103060f1302030f1603050405070e06150415081e0103 69
    0x110300741c040428505841d806110b031500d01145040818441c041e461034181d0199541422004040005076008241141101e8003c1e08402c008684901c00380d09183c006886002008020b800c1400c3c40c502940c0360406031a0280d80c0c5c0c445c1c0d540ca000c140484200343d0302510244039414070080000c0b800b68680812541c01c549402e5052040e040c7c041019034000415038510103441e500c050105c54200d40c8044002c226800c22034041240520040d04503020142c0040d042a0302c0b0000146201014803c135620a80c0c00505495510440c10b0010015440d04200511034090800713100311501150280135080365000d0b040b145152070b0101002030150f080c5c0b1038290070080410008207150010b10185100705005804000c41d4640100803003050581c01140d00240b51600003030101080c03002aa100549040c1c0a01c0d4600f6113070381c0c1c0010000030b414100c0000510000601180010701803403013002c95845500d40c010242c540158510b0409000184030301844a0003004101046104484030781081030b13 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 367820755 1250 367819505 367819513
    0x10c0c1b0f030605041a0c09010509010e03061e01080730020d060e061303120518010f0f0c0c081603030902090106020a11100215100b0c0d0e0603010302010818 70
    0x40c03815041081d484551003540c2840e611810031051201c0c802c81140518a00817100c91280340c1103410390030318080da0709010304100001c1004a030756401007003c40000078009040740d400b803030302822140040301e8600c4030401d4206c508000081700800080c021007a10307039208526480c49d100e0b03140d22010280c2ca00303000c001102c1c1194000d015840c3d012141c2c0046000c1c9001103000101520741c145003050240014480c0d402c4400508003003a40000c4000c2130070728142d030200b03d0307440303025042c00250b00c61103046503075528000082c1c02e01c41403075001000e10b2155000601c065104200242c4150324001d10240c12040c0802040141078110544c07400802d2007402e0004104000b03401281001c0002d802400260380906104418800c038101c54800084e02102d4044403050600b6009455814000c0d40c281d00256040100c5d0510b107100000c82c002d815520500c0d134490307a00680043c0e80741601c0c4800c2c00403030804501181a800e00200312416660113845000745900e035001c0c00c00100c0c40342ca64400c002d0203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 367822005 1250 367820755 367820759
    0xd050706020c070e0403020f1204260109020301020a020f070b04050d031b050109030c0b060d08041a0904140708071d060702130501031515050a381308010c0c1b 70
    0x64251103c17400b03540aa4028080b4021103801c080c90024947d00e100a01072050000308180e481c9030040d00d0980e440c641200301c44041c3c0c6002c445c0034000c00315000354194000303d00880400d9000400780c0d5502030420031204010780d01c20f08246c9501c9a4050349030407545000704a00800e00644c80100e0f4200034120703a11782110300d41c69003400c464001d0821400a2020001e0005000c00b1000b030541185084580c140050318039a00c0902d240305e144107411144040c0704109440c18241c1c400d590070700314060010700036030350911603143d038200d000c90346440891404008255124465240c0d51140251007a01c10389a8000780e08220309908001812a844401015180c4c3c2c0c40340103000d018000c3d4450910001d514a91000d050240c80e40118804110107988070100a642e0341c0c0344500e42196560b08c5000c81c0080100000d8414400a060310391904071900c2c00c41c0e855407071001c02031541d900303080e031566803031078a41c0909030907150300724030f840005a8904003010210703001503002c503036808010b080224556 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 367823255 1250 367822005 367822019
    0xc0d0b06030c1603020a0f0803010306050c09130b010203070803160816050901080c071a070806030a05061f05030a2001030b10112505040e0102072015040e0a0606020d050706020c07 79
    0x71f0007000b00b2111007102200400810100b4018035820002c0d80c130100342014141c00110b440c869451100050a03903c443c141c0781c50303034002c2c000c0320f0348a50085803441d540c1c504540000760040c140e5400500142d260300000701e1b900b0191a548509003c40e5449600c0c110f9000011502280080d09520382da0b40c0c100010000128901c0c0c4c0e46100c050054000545403805801c080d010030720042c441741c0260400601d20001542c04650780d94451405500041034105401e07200006104039041260188200d2820340c051180c04401c40b40d01c81840040d50600c40101401141580c8800e52155003100300038000c440c000e805143c2d80f41441104100301c07013540404011003c1001526812000381c0142400f01f80004d041600500c000c02080c0c3d0000d51070294103a989880103071500042400000c8a0f2a8090310341d655080e25108882007040d4042c0c42d07c2d00d40140c0400701d4001e80361414000d00c0d05000080c901e00108410b04122629200d40f0700b0400e2644504029500503101403801e03003c4c17064003180035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 367824505 1250 367823255 367823273
    0x5040306020a050d09050609150615030a02070206160606090902090c07110a1401170c030106050309070e070f0e030a1104230907061805060a03090f02090c0d0b06030c1603020a 77
    0x1709000d0401040541070041c061420301c26201c00d0003d1090a410800c038442e2664240bc82400321850721107030342c4ea60780d134000600034060714400961010300096001c0300c000f0840400314482e4084c080821525a035802400d044958190009400141340000220544d031140e014184250144035548442105900014207406440c2c10480207029a40880456968001842d01009860707954800490400042c44002d07404144140010401d0020024000078001d10029004003210b001842d96814a1040603011031208200c020015240d03c141c070401c2c2c40c000983e66003141d0004e00c0100201c1c04002844050010040f00f18000c8850141c15410b07a00f400d40c0542c8950150340c0941101418240000c00290000115118680721000d00b40420740d00c203412119190b80c2824006280c4c61545460000c0e841d140c68041e42c409920b90801c2254010348004201c0d0904900d0204000c04408041100c1402b05803000c100d001c105100c2c100b030130241001c00c60440c50080c0122103180c0401e41e0b4400c89 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 367825755 1250 367824505 367824521
    0x2121606050c21041e03050f0424180b0f0c0f01140c12060d140d03050601030b04060315090507150215060406030b040303110d180512090105040306020a050d 69
    0x200009801c00b050030650401d1003290f0550042103007508064845c1c50041c1540c045000c0c00d210180703242e80c1014002d5044900465520f410152210355805d40100025144002284140400722116040324441c0818801c0070f40409003480426043c685000ea40e600903882641009504000ca03080e04201081083d400026610010072102502130f010131000c00041c1c0610400300003032142e0a0307154000d02141d54421029240e00d080344015090040a08040000780c0d506405413420146030182d058000c03c0c070640c0f00781c80a07c4501c011800f400111603152001074040c3e00ccd5890041403c1c10190050050f982c00b980880b41441d0703c03064907161406049240700050390000c6d10001124502d08015507011104031010070109186860b08064480c0081c4000c04140d07803803801440342c80c18101038803e10002502e00b0021400760442c0d1810014582c502910b0034800c1114001812801030308940e1030340c1041c0d4845091a140d170744d408019412044030740d802e104041c062000b03d1f880c14410071070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 367827005 1250 367825755 367825771
    0x21f110f07050a0f05060304030e0402070209010905040b0108031e09040b03070608010314010c0c03541419150507060e06010803030712090b010608250212160605 71
    0x341c461428041000111403a40000140c5035090340800aa40e1a801a03135842901400e0906682c400d69001900178400c0120003035000c6070742d000100b60424941e12892083d44105082941640c0f00d000c5c550380d9014020403840c00c0b542003210760603100d0385007010307080c00c80c006840800c203100200006402c0044540042c000205100d00400c14420110310b4500e0862040b0000c1160085400c8010103a003603084000c0c060000007401c85d6503500c1e00310040c9440003468001850301c860b0307002c0c1105008000b006a07001da00145808401c1d56650341c00400e041360700403289500e0b01d0301a0010b1104000c0045e840025100412000244981117080c4a42d044412603070344659403d164035128013207600a840c51102030340124010321210b04008201c0e50482c5503030401c0c2200440f40180c10005e8040000014820070445000042243c1c101c25924000d03100d20071b07072000031014203101c031100c5620800b1840050344910b00a40c820f51600d401403080384000d034408051408241c95400c255101a54006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 367828255 1250 367827005 367827013
    0x206030109020915180402160c090c02100b0d1202030f0a0207050a061d01030203060d06021b010617070501121107030e01030b10210b0910080c01050304021f110f 71
    0x200e5440d1540c010a00c0b00c00c4401d4aa0500401c0014606020917008246000c1c030350000305107990004444503c690540e015428403081a15a0000390142070702e4000c2d0409840354201c1480d031032605005d03101ca40d20014004515aa480f9183c89000750070581e0000b017580020000740032180c028000500c6913503030075002840d001345402c0034014000207a500c4801000b00180034550f845420715514007011609180150322234561200050f5541581c20303005010910002d0001d80041d02e15200031490404a4020800c0c81d80e81d0610340010142d55082100e02c0d08562018001c641c01001c0c0341e0701040c0da030700002a0070311607031042050a9205040c10b17000300c1c0c1c9642c9540c68030342c0d250141c1e2032039802c140c0712040100c1c15030300c01030804105600d15007100c0c0703480d02d6000c502110650101c0204030000b002400c0ca03040801e08c2e001e41d4285801440101e0040d408118001c0d4080c0040703d000b9540500f450603a03141c0a00000e0000d04981122410004880503561000000300030302c20500302010060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 367829505 1250 367828255 367828267
    0xb060f1209070510020c0906011b0b010f050f0102070b25080702030d0509010f031a030105040b041b0605160c1a0a09090c0c0b1e1003060f0b030304140d020603010902 73
    0x29031800b202da40c0414030a0a402400c00482580403034001016802595109401e844010050740d0b1a00080034007002c1e281c074081c40c40c0c00d00041e0f4040034101e68502d00f100030129264001c0c4003600002e0861140585c1c4506410010503061000520b0844102e94401645c43c5155441c291440d100b41c03029a071302e600201c0c0010079071805125440042d089414007503c1d2032410b0380041c2445548040c2072040c50341c1d940400f07650148590308034043c1d01c4014003c012502c1d2500e400c00320500155402d4841c0d24014080c000804010501407003590070648400d418200c903170301d03041036084c40340b402265000400da500007481070131010078601c00914400242e88420104070f00a144a000d03034800405117041800b1003624503000341282c40304541101d803441c076a55405030f50350b490346c510414213031240300381e44200b205007490580d0090940384102424001c4086503600d180980c2c0c544007000764140c004203c104580c4511104959940402405012880495400040ca50b030005da00c4849038907000995 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 367830755 1250 367829505 367829521
    0x5040302010e0a0b0636100e0903070b060f0a030501290603040305070836010f1d150309030c0c0a080d03050a0e0f0106060206180604060b060f12 64
    0x6010b0403000500c00038090228241c071003442220001e410103001d140320740110401c041c1d1001040c400010450010324481c03032040c2c4815600e48007150000c8185900880118240c0d030000c00e0f4600a8400000544c102740d5203403902401072801418083d80810340500e00e9043c0e403648000203000b14090000029911403a4400354580daa01c585d00051540295001e90b026544035812340f5041030300351805076110445403030031031440e11031441003040114260105403060708081c007110501d0100c0c00550102c070284000151a05514145c1d60804036441c0031251981420400048000384001801c15061603220300111744981d0080c2e5001900d600000381340c0250072010080ca02000c1401d0b13440d4840640340c2401e454650410b11102c1040503214000710302e02580c036070802d20b1060086801d83d504000113000382e500a110910a220160041c1000280c44480b0008401c1450080002500340781c1e0395a91400003e18030020000c0d4807000500500c0500078000010b40b40890b48000c3ca0009800d110007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 367832005 1250 367830755 367830761
    0x70209070818010c090905040219080d1416060e030d020406030209120606030d0c0f12080f010506160f062d11070c1511100b0901080106050d08070305070602030a0504030201 76
    0xc0c0d003610f80e052440c800800c983c0b11a000040f035045510020741030b103941c40007884d0b04000e61940d43e40c61410ba0320104200e00c010454081c506050748510342201c1d006521000c03d801000b044a155981035601240443c206821440c152451103098070700d850600c00c010f0080360001e412507400a603020421040300d0406022018000141800070105807400c040065550401806024100490315108400304860389100041840c0e0100684150501c2e215000345501c2c0203d034440b256000c40b80c0002458101032080350840511044500384001860300c410284180207501202d000341d40c0d80d1858a5482244020b032075400c1c0e984252907041c03440d409100141d9440c800004400201005040c00003110200054100d941b00036942582c102e00f600c041d5212101c0350140001406050010b01003640070f40e02040e01b600d4120340307010169880b0401c040c200c40c03542c001d8980281c03005441001140b41c881c044c240e658440d140c554a004010794454060b41c1041d5600714880791100144020503030280 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 367833255 1250 367832005 367832041
    0x4230a18170a020a0c0807090609050609190207050607031b0c0b01090e100603061508070b0403020f03031b0105160c0b040b0642120609090a0f11091006081501050702090708 76
    0x240bd00c22414100001100c1e02000703000140314142d42142c181d4440c1c5560191003015811800741c0314145171001d0040c02034540006085103d208280e503d0900324010101035104c15000142c680d4203a090460a000921441842d02054407a899110111a91600030f84016501c41c4d58041403a11001c818400401c2e0550000c43c41d642080106200c008500d04c10303078041b070b9011210301440408203004241517120703006045607000c1e081080000c01c0c06054004d00d000b1000c80305a141110801e19007210f1360711041070014103403040390001c6008521001101500100010080b0140040c1e420781c80d440000072429048620824010031904050182c0302c909100315000c1581d03180620640e0514510300e001032034103208042050104403c2c4404002c0210429845000381a0b00401c0f41040084200601c264600c078000c2c0308001910f10380c0300141201120701d23075224100c054984075281800b101150705054100b11060004101507580d81e0b00607030140e440c0c1d443c2c0403200d0402c039401da1541e49982e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 367834505 1250 367833255 367833269
    0x60a030204060b280e06180301020724091110020f1603110d0f1b0b1210090b030615150a120b010e030a1104230a18170a020a0c08070906 60
    0xf544d982c5215a04099218a59181141e1160f580c0b9201c007403a8141c0011820050341543c40400c00307604001414111102c40b007110340f40950702c3e60540342841d05550100e6001802480d0010003060b240c00d004400040140c66030040d42c0050b80722200c194074080800700b401403200c00c0c1e81c00c20000e202c544401034125003c00d554400c40603000b900c80065005061400402d08a00c40300513080d94809a41807201074074180c0030150b07858002452030115640f081d100c65551440c03c0340700280d100038510a46403450380260181189560b46403810750100d400c0c1d00d1680e080f54113425823551044c4a0002021400b88640741d9a0748461103000c0c2d03034219061450a03a0601c07900180c000d60a030380000c3c1d001042c41d48801440038120490021030003400c84074055040071412458000400c00c0c0301b1411603c031304110041000151070b40c1c04400d4004106880c0a0100c404011031000c0ca030142e000104070303030269801120081c0959643d1012019520703401481c141e00509414807444080c2e0003003030002c0c401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 367835755 1250 367834505 367834567
    0x90602220e040c0b0304050708071202190e011712030a020307080907061e031805030703080703060b0d110c0601091e0911010c030212030c1c0203040c0608060a030204060b 75
    0x1650740c150140d545400748004d5020080006410081304004800c0a07128074404d9402c041d95440c5c1d4000c3c2c0a58100040b8402c20807410521007056400d0b4003142141c0c0103080d0880d90381d191403010700006005100710b41c102c0c09032a16019440200800450050b07000c0400103a60385084040144514005010000c080d0405001040416400034000c50103590300c1d440200c480c4003940b001d400618042d1844082c2a801350082800e009021000d01107060181d00c604013140e40340c0340f0480c101c4801c1d01444c0340d0440e0500000d5206500d6a01c0142c4070040c00000614040d444040345180c15400d900c52004203880390901032081500058405610015840c280040c0249075622001da80c0e40c0400e460421840340d4603542452310810010b0100c1514070405030381ca042010300c5030b07001d0b0f00c01c2d03c43d010b0740c4071080030f00c0c0303504083ca1003141d1085070001140305496040403000c0301c2c24003000d00180d9201040d00700c00302c05130f03403107101c1d40004060450250f60b0b11100031441da0881082800c1110311404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 367837005 1250 367835755 367835761
    0x80d120606030b09040809010e1c0606050306100b0a050913091515121b060e03160b120705091201020c0f03190507030c060e0a0303060519090906090602220e 69
    0x110300907105e802075030140b100b90316612201d00489500030010b410562094a2040816004900c0d0384001502c5024500c00d10001d40c958040c5640d851040c0c4105a00340c1c040b603000c2002400d18400b034001d502c0c440c43c19900e09940740000600c80c0000b1118104040d94030700001c810016440b000742c0403901b07504421300001211068904132111070340b044d03a010020040c020020000801000d403140c206072620020041d81381c100007006058144d2140b4003034130be40e11840c0d09550300100f600080324000c00609152074507803419234011400142803202880000e00082055580e11503d0680c0301c000b4100041c1c44101da004014035101c0c40400604c3d50713030000c002c0b0042541a86003030712009071460501e9543c0b1026440c0483e81025000009022107103803003c0b00c45546000301c2d01c030310042d0080d40c040c8619915041003102c03c0700d00345038164120820040c10840700c44250030040741940181c20014060359951104402d076801210110003401c060f055031078907500008506000340c286000038401500d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 367838255 1250 367837005 367837009
    0x60f081f0f05010311032a060714010c0203070c06091a1c0f020c0705190501110c0904030908061602031803070e0907050901080f0a02041128021b09070f0504080d120606030b 76
    0x258072039580c7c5010305070000701d00c4c0510119010424080c15500000c221404110a00940300e4001000440f403460a1801c000344044c0304030f40070070a0300e140700f00b129002c3c411402400c0c0a0740c400c0401020f640281d0205103101074141c45610300780028010090303690f0945020850501501f600a94031400282c1e82156510050100010070b990082c04c0402c210440407103ca45030281610304c40d54411107200412080581c4028068210b90780d8800312030303590303c0300741e00d081d007000d0484900401644203100040c051100000280004240582078513506c80c0c84034405410400200c91000c42c641c010b10701040607080100c0e210340144010b501802410859115281d02e0b900e44040c064803854844070480314100c0c60204646080c522040c0342c06102081e5001d090145164500f0344c0094010004221401c49103d64903071100d10006296100b03e5480c007000b41d4480c009a50300c0d0301088418007001c00c845d80c00300403101860000e81c640c2440302c0300202008090740c000fa08081300b01401c00d22201607035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 367839505 1250 367838255 367838323
    0x507181109040b0d0c0f0f05040212060922081905040308030415060512060603010c020a0b0c0307050f030f01030213090f0f02150418060f081f0f0501031103 69
    0x6850102c0d0081002040c0c50300140400c80e08101c0580401c044680005000c01c1030a004811a04064003905a4a640700c003000228010086802400f001d1440060454604020307001d6000518401c02d4068861504030003a040381002d9003160716142c00586c0341410042c220a02c0c2c0d52410510b00a07240078255619110a0300004d400145081c2607030600400e02c506a8000c880034250143c501d0304110310142601d6590a400c3e103125019500c1c09460502d581e01c08140f500c0031507000343c6601c100b621188160440d41d84001e00c02002c124050043d00b19000000008500903442210a040154158010809070306011000d81c1d103e10320704640f900009940c40314480096070410300481c00754210307001092505c412040e1609031824001004290003e20134414521548039580800410391602e034107201c243c07114010b030b04150b4800a0100710300f0400034844501d859109501084414081c624203007074541c00e8108940403136803901d2580d0141001c1000700c0a03000c0c41e2000c1121117207041c44000305 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 367840755 1250 367839505 367839517
    0x409140103020a031b17011a0405060f01200d0207030b0a15090e12030108010c11161502011517101b030b06040e0c1209060103051002031e0405071811 66
    0x5d041c60001114014007503140b0300000502c44801e08500d501e69030340403c2c1c000d089032241c0505102035020061003e0a10380300b660b1007140c0c0684003e2034100301a00660b044403071889200714540a200d481100711074248500001083d0310340090071481e04515146000000091a80301403e1500586c940c10031041c00c40031003140c65980c030000b0400411004ca50500c903900305c0d0040140d00010000074034010541c0300c2440c40e0a540d5078049214142240c05444003112400da085c01d240441e0300340710102c44400c17500c0e68820f80b400009090345a84840400101c0c96034001752070705403e10001181882d0074043c00b640f1019a1008010004074083c1c1c0140d400400c04001e010103950707140303100d4140c580c502120040c20b020000740c045864140952901d5038404090104d071307000c00d0008a03042040c00110941600d5119000d091814030907030301e980080d0002003609100f00b010b0241c80040c0303e20050164061401039020306406410581076460304600501600102480d0104200316000e9003415126 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 367842005 1250 367840755 367840763
    0x1506050a020703061109040c050c010617060c130e040b060f060c0703110d05061008010c05180910031a07020607090303022d030409150905040b1305031c020409140103020a03 76
    0x688020004403600c00360203404562600123180065030210903800201500c090442ca1000f1701c00e1035158807414000c040c0d12054600d640d441034001c41c200b2549034010b0440708205100054016a0b01c1a4280c85103100350340669003540c0c40003d0148034108250060010170080d02e44074500000b00040a0f961801440b0190a424421080f00c825943d000d032141481d580040455100c0c5c01c00580c010380e20300789446802095847e0805d2020302e14001c000303540700580703903035018010701c0b80d141d0610820110041003031100081441011000030f1141d1412141d0f4294214078503014035195030007a180c01c001501101c1400260002000065400601c072440080001d84482c660b1b19000000044140c1c0c0c0c0d0aa82003e010104021811804641c805145444083c82211025550b4114102100c03025500500f04510410000d500a00f1590305014103900c6401240e00e0201217194081c802800c00f1015544a0340000b0108103030751041c0518280f04080e00c0ea0082a5407551740003841100e45840024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 367843255 1250 367842005 367842011
    0xc03060d230312011701110f13090f0c0e03210702030705040e061906060801120507090617070902040503030a08100e010608010618050609010e030703151506050a02070306 75
    0x18215205521600071041504812603440d1a00d000c80c18901d036100740164482c1342005003424000010500402c0d12440b42940b0f000c1c40c10002003460256503000f40120f24090b0f05500c030009d1307000c009102d148800c000f824000500312284400061103010b58042c0588240e129400c816101401000c40258070644824807681c0d07982c0900c042030070110b01da48a241d00502d0500d0501c5ca00b500490700c107110321044a440d0300b012480001c103c00700e80d843e008030000144068018403a044003240210216801001103c00c2555113076044000d9840581004a012040d2003424031001402c00c03100000d0507010301c00354206818600031969a000e00c4203401c081008100c0441d00e9025841513400180400107d441600e41e11050040c000030005c0c8038450000d40c4150b02000c0200d03010f0240b03402e48100030301107403403e2040b80045510209101c440d50781809000c2d0008006800701888000f0540f1008010460308002045d82d0341403040f0342d0020003840350800641925581c0410030100742d0394401000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 367844505 1250 367843255 367843283
    0x8090d080a0b040902031005090609070e06090c1e0c0706050c190f061b080106020105130b091203090c01090608220602040302040c0e0405010b0901051e300c03060d 72
    0x54050700844c1e10181d014050500ca01c2c80ea4091500664031a51166007202c4071a01e0300c5a84641d1008288918981a1101d0010450340d150421409400c0401000d109081120304000c5620b900740300c064003225188005408500c1440602c8414010000390030886e040001c000d4805481e144032110b0f06a0508240a59404018200d0300c04140d15802032020068607280524082d0808103490300140400c4a26000142681c070502170300d482210f1581800190120594405140e02000f5104a10f00d01508070303060008045440034500c05c4401c0d400500034480000005091540c45400100801a450b0108031040d602100c00b175070a040c03a071031903400088107410110000d0103030350402907005080c540c44422082c0d100071703070585141040742c04011a99031021200307054801c40d0050f45c0401e40034001005454410700031200b4501104080c24900002c8070749400d0340d02030401c0456110b0720f00d205201e00a0800c101c902d640250364031886851030a069000070380301c0109400040c041d581034504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 367845755 1250 367844505 367844509
    0x309151d030f0a060203041716110102010615170a050732041712090d0209041403041502010f150b0a0e1e0f0402071e0c05060409050708090d080a0b 65
    0x2c51210454040c054424000c918a0034074080d5106503016a000e25640701144a034004c1101250358005108140c103611200c61b50b180301480e420f80c0381a038155561550000f07100300741440d0307000c21041c0c0c0f66210700d01c0d000d0302c0500400700e101c041c14031800b4a04d4003040001098014410012102c1c0134a40f00d0b10041c02815148070300b01800700c01c0d0300206004107000030280d40407040d01414480f410160303010021550700002c10b41c00b448008030b505c400c1c01d001c44009070a003203090607001401100c100302c1c6d007248203001901d540d2060f4802c044034072400a25030007855080c4100540e450021100b44610003000003404e042409500480120302d0000401035415030042c0181c481c00c00000c1c10032001101824485107038820950030f1103000b90042d5629140c5480c06208494005900642c004003072211b480c4c1503a140c6c5607030384046a1070660813101140da9034035400a480101505000450356251829000b040351602900900655108142e181406500078040c0d43d8400c6074200300140d5100c0d0a00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 367847005 1250 367845755 367845763
    0xa05130b040602190c060b01020d0e040b06090612091606090b0c031b010204360209010507060f0b010f080f0c030c0403020406121209080d050a050706020c06040309151d03 75
    0x1443e03440e4413604002c0d52140c1d40d003107140040040c2c05102c003000300020745001603860f5a500342c000c43c0000d6001c548000e05103400d03030103007440d60009402c41d4105075a0001282480d80a85c83e41442d0f002e460b0100031109000700004001c8080007104000c2c0c0900d401e0010b80000d0301c03801801a4088082480c1190800810030f607130b280c140344501550140caa500e980313030007076126018000910108440b0300700503603d0b92500c0c070001d003100c20041d007101416105500094100d070042c02d0401404001036000310f1010b001e005850500320364000b4241241400140c80280e4244102d410700800004008102e01000d0703407503501c0390901c4001541c903960f400074040035104640001358003c0c035080000c6044c1c1c1400b0642200d40d48111601c03d5500d0303900c08203581e11599441004090343c004c25841714590700c1200a400011104c0c00e2080c20040660380301000c0e40c002640e80302041d400982040140340c0c1c4840500c00800c4185100280d01310b518100814a844100c0d00340c210042544c1003a02c0780d10300300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 367848255 1250 367847005 367847017
    0x302030402010e0d0f0210021501170c090127090b0412091518050402031306020c15130b0c0f1204050309060c07170d050d181b05090a05130b040602 65
    0xd001c84c1240e4024900a4003821900c82d050f8002c0c00c00344004800180005540c8601070030046c100d01d8030303a01c0c000150300c20040f80072645209020311002c1d02c007203444454007035010300808030482156228800042c00310b8102440d400246604003042800400c5645d0107071500160040c1c001c243d441380e585010344d9480f546501c501e009032002c5034204012035202c40110203d242405942c0c071110b0703480e020081680000e81d010010b82440c7e80340301000892035130003000c5c00a003e1003900d440c140c1d0921013078201d071400c4030100310701d0542c024840100980c44041d0703503101e0089094103007050f40380541c01c01c25015512050305041d424201160603c0020000d4400b150340c0200070581d00d17500600010f07180e903840c3c4929000da611282c43e010540740701107176010402409039649030614100e500d5040c068142420107048000d0601c800c4008038116200b0000784403c4402036010462400341030010760760b4001c0251f071102d0718040078082100201310304420501d4110210912544890400d00b000707100d00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 367849505 1250 367848255 367848259
    0x804060f060b031311090417031008030f04050907090f05060a030906050a020c0f030405010c08090f0406090e070e25120c030501170105041218030b390702010302030402010e 76
    0x8010807401034503054111103680c5c8907080940304904442c05201510200396001401031410b0710322084d1110318040a594084190a1100300141c0d5840109003150f210036440f803003d00000405208908001c223400703400210901d01b04148501e800d241c224074450b00e0080a01c504000207a51030024800d4101c0d002c0300750405c2c420022802c1100f80702000354000341c003040d00da00400c9a2004910b10200598040711410303101c10418440320390780da0440341c2c8180039003035011200c80c138200210f4985101b1900a882c22940020fa06200540203501e0301d840f540c17000194145200400c8064512103900000b0440504080389000328000b4054030a010710b0403004226078600b0004882c401c0d0300d90444e81c100e5a00d11914102c0340c1303a0101a60a0310b400300c1d000340442d00070240b801006441010541414000484440280c1c0d460b035541c61300314401560007280c0100800c03299103c800c0501150745002d00010004001ca0515003220702c4140103002010707050641c003000040c25079010300c0c5a90362030140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 367850755 1250 367849505 367849507
    0x60a0203040302180603010506030607020c0d020a1206060306050606070203120f07080c0a0629010f02070902130e0903190507020d0609050a110924130c0c11010f0804060f060b 77
    0x1311035410114003c046440d10f1096080101080080c10080742540c0503082031b9000c1c00300e443c10241031005080d48480102e8202c20030700b41c0000c3d5900e010746107440b0300340f0031031000c100c15203507080c074074199007014001034411700041027802c2c0181d5002441c43d1f20402d096a5807905c8941140400c0741c240140c0368040c101c10300003e41c9503120000407401c000c10910502042100ca0405840304020865140202e21082c0d00d55030800702c0ca60040c41003c44c03c4182d0710458940907200c40c4203000380d070080e5508203c0d00303901070350600c19904403918090340074203240000c1d4180320425006141d81010321440c44180440080e50005540b0750340041c8040b40d42100041c81004118a003d580c1d602811b10145c41c00381000030b00d040c840c90910880c40c01203600b50000325108202da0700500182501c00c50459010030f0303011503541000080d0080407040001e1362a203201c0c08240703090a10301e40322040051410041c003030150904094000c0c200b550070981040000417520f040d0f0351b5020013050980c2042d40f0b1018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 367852005 1250 367850755 367850779
    0x1309050709060803190206010608040605270318060307081f15091e0807150201022101292a0f0709140f15190e071715060a0203040302 59
    0x18000001c080d00d20b20803c40c030340c96000c3c1045c00c1762591000c3c013981c2c000550300c00c04100403c545420058006846803a002d12403030aa4102515809104044001c82d82020814a40d0348911195400f814001620f80914518110130010714284000b02190390382029010f0b6002810a070041c030030098088014461100d10324000050078500961107036075801c40000e40314952003104a015a8220b481903c0140103a508110006810104420805007159403d204051002210034815288044180c0b14043c180d410140004e0704590414040e510b4990064803858040804000720b84410280100e249244681406082c0000c0c00d81540c2000a1040702040340c4001e0012074820200c0f0034248c1e0030803400c040348006c0380d40b800c002c0715040d041c04403d1000481404d85104608411540244131452642e0355224544044400da0002c02e01e80d8103d07402c0140c0c89821000180030550400c01a0314549801c80c40c42c1c0c0760b802140403082c020700022901104160007001510040d6a00074030401101d6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 367853255 1250 367852005 367852019
    0x105250521190c02030d081308040b040302091602061513020c070801051b030604230106050918090a15060b0c0f0d050a0c060504020a03020d0f11040b130905070906 72
    0x2400102006a60b9881d0310100784086000385585910f00e540030303000c6c3c1894003444e0000d840c8807000a010310130041140300d8020014284100810107020050340c00c584883c114010301c04004001880c66000c610408943d088183d00000c03480e9200c8581e400040042e121017001c104c98040204a80081d24000f107080b0040b02c00204015065503160402040b02d03a86a00e8100d00300d2071030007250800d4810820118070319007090303088cc1c06c0b080c54500742c0c00c01d41c00e45040c800003140400d9105000003200443e0030001881c110b08001c01c45540740b0300420550400c4840b8584070750881000415464060ba241c2e4140f410b40c3c0c114000604a0240140c0c40c0d1140c1e03c5440d80311000503402e41034138010480d1a56001b030003442038480400c681d94078a2030b200c49070790361103005003c05402aa40544194000801a61804507030b41280c0c2c41a0048038450a0074074203800c07030f4001c80ad1014461400d02c800031165071900d0f410240c00c11016000410026507504040e410102e40d078110b480a10305000011540b8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 367854505 1250 367853255 367853257
    0x31224060a02060901111617041d07030f06051e03010b060a0f0e0d0b0c0307020a02030a150e0d1407030c0609050f06010e100308092701050f0105250521 67
    0x31302d8004024425030100c1c1018000314850b420940c42290388154041e40841ca03825144100b5500c5120b950b0324164444034004c00798030b494000c4008000c00d140401c400254540203000881c44200801e2008ec1c0c241400500c0d04000381c10440c50040d0070034000c6200380c1d825081803980341d0020300047e6440e80c6e01103004001214501300180070544c81c0030104818102503200e10f003940e404c00c070340c018503445050400d8103951020b44014210712640c112007000da40e007881b15401480c031603138010aa03040d032a456101610071100c080340e4260000300d43c80d0689604a00c41c095800d551280c02c1d503460741c141c5015034441a8184004d0202d030b01d440848020040e000070710342450b00e855011103c0680e41d820341c1e101e8181e0126070042c10410825030401c0041c100c0320180c030410100030b01094000a91154140403649075645640403010760800400132814614010703401041e0130700e00035140c2100d00000c00340d0400030340c0b06a00a032001020364002d01c0424803140008000c90364411a50b681c0d0b0003100c5001d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 367855755 1250 367854505 367854511
    0xb011710260d08040f082208150a0b040f050109020901170403020d050a112505041104030f0804030803130203070905040b13060209120a0b01050102031224060a0206 72
    0x3001e40103074040c140540c5040020812041c800148031a5010050841c0c0c00100a07100700d8042c080ba01c0c3c00c038009006000a040560000140381d1a900e2050481030842040340d0f20181c80f41c4c0050200c01310041c0c1e800a4560302c07001c42d00d80032404c8078410000c100100981ca4150074514980800460b00764215001003040c08030907a036a0002200071940741500c00800d680080142e4807000d0410812030040c0b014158140d15400c040c0030014120304130f02d007030540403900a04200200703030311031606048815121000d00030030b036410000d041c04680d401c0307924808c6000180c02c016002c541c3d14100700c48e400880b006913a01c20f104589a0074824004200049000340c00c912034095040c000c9091509072080764400d50300302483c1c0c105510781c2880030704040c0c0c00ca070042d18060b40810a501540c1c541c0c0420740e030000c0400e0002c00050541d804c0070301e800b8070182c0109046410401030a2400c0c40c148503034a405c40d80f142ca0a0b10186040074503c4400940da8241540289000c602400b0003038010400c40d00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 367857005 1250 367855755 367855769
    0x51c02030105030d08101202060d1404050601090e0c0120011b1b0209070302071a1305121305010f0c02090109050f100302030622050703121205060607060b011710 71
    0xf1300c4000d5250940e1982002c1740c0c0c5070300c0c101c034042003001420481d8600314100c1d400030302002c1c81c0034101650082955200480340f1b14075034040d8180010884104075650040002d83c00400c071900b41c00d101c00d61550b0303586000da0704008110b109940300c00c1c3d9102c400d04105040400030002d6550f151080302600300c2c0e0314100c0c000b040030300d44050003151a003810001000d40c000c1440d804c030360724640140d0080d00442400c1e00d001100b100c0c1c2000d140b10300b01c800e50260659040a20700c0c0e6100f40f40903803030440700314038000303003c0010f0140c3c600c000d625103258030541d5002d0901c0ca16000b4102e504590705001100040e500094140000684640310741c80103014100d00d2441600075a41c840c00c010142c82c05200c001c3d0143e115000045000b50320202d82d071012900c0080f01d1082180700d880d950301e0002e00760010f0355070079007501c0d41c0c081c141e0f08a04c603601c1544a03024103000341e19241c40010118061642c01078401c83c0c0b20040343d0501d80c86001c0500d000302c201042e0000505040c070040ca459190350140079 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 367858255 1250 367857005 367857013
    0x6070810090c14310f180b0d060f0b0d020a03080306190e0105150a0c081e18030717070905041502070f05070902090d020d05030408120309071203020d0807051c0203010503 75
    0x142204080080748081c1d581900c1701001c540e1170860740312012030200300040c2e0340c599034a0540c1115580c03150024510350107088003042000c103800c411000c03a04401e004503c6050030781e0007500180c1b1510507510850f5000003035207840c5c0e5607003004500407500340d9001034080d901c02c00c0041a400315051912341a03e4050701c04860401c100c2141156038852500c00d00c0128464a0000000910610084c0324200e800c104d4a00600342c841c1c0c03000c3c0d040d007144d4140101e0396017012441040341020004c1754020161560b05001c41042c0440184d2a02000d0080d444000c0d06d600c005400c1c0a603054401340e4000250340c04550b00c1c0306906101c0f0003442a00f85c00c030366a004100d80002e92106500941c1c05a103401841119042000e0b4204040c000f50b25100721110f000c01d2000040804050080b0355607400620003c41d640d24003c0c138010708100480e00030040584840c40500d010a9002a82403a80d203114106010319485032003040e12180100c0c0000c104100001c1d103902c00c07003011b503000f460480b10705138100c1d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 367859505 1250 367858255 367858327
    0x30309050c01030203010b0d0b0f0402040303020a02120c130507020705150306010f030e0d18030501060f0e06041a060a03110a050711040e1c050405130b0306070810090c14 75
    0x1107051744001c0c4110300c05440e091060a6a0106039409600d81c4000100701c00c903803e0704400450140d0b00070f903005402503002940004150f0411381300030790526602c4405403070b01e41c1c00000007071030380da245820342021641d84800080d0740318003c00241c0d014040090413240c80c040403440e0113117154811160700340062405000116154000d0080c071b12510801000780140d00c95940003140e40c400c02020000511442100000115000388500c5018158001e80c030602c0506200c06461140e030060f2110b40161b00d0405520300f5503151303503481c00710700004444450303030340416080407070160144441900b0308020001c3c0007501141c001001749003582c42030040503100a04041048221414a4210052500300c0d4207040641540d012804480b8001801d0143c2829140c20215120f0b0400d0031211415566806480324245010801c0d03607070080480c23504502c18505909859112011881070848480c1c80320171030750485000b100740700d2256880034075164803050210742c1812803004d485550303803146071358000c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 367860755 1250 367859505 367859507
    0xf04030c030525150203040906170d0c030206131a0c03061003230711070b12090c0a14060408010515100804080430060623030a140f0a030309050c01 65
    0x443d90b0b684007680d40210140d1416003003400d544101c0c89203800b1404108400300d2100708178810b25000d0140902c00c4000381c08030308221031170050700010550502500110110009500042e040c1e0310284c1207590f00113800701c1d8541080c04c21500491a040f015004080000c0c4041200185d40b040c00c044460082c6440d01c09c1d800c1c5c04480c50481c0b0b0004200d414070480c0280b4800c2c0005603040749191410356044800442e0720341c01c040302c0c1d800111450f44000b80c0b9240d1049048011900071141c20b0241142648000018030707404014400c10482010001200c280355070b41c0382c00c0d00d0007800c50764002d20451402c160604503840440714a6489848050103c1c4409842120b20501c00d0364031900e030f5031609040c80d00504810b0440360320244100c603034074002503409001e2141280f0f02031084a02103000340c18103104100780c42c41d12100e80c892650342a1003441507600012600c00f0260001890030f01040149a1f007030920004c90003119842c410f0034a954100359165000d650083d0003541503072140c21900340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 367862005 1250 367860755 367860793
    0x2190c0606120b0103080304030207050a0b04050120030a180b0d0b040f090510091e031715060706050402040f09050f010b010c0c05041a130b03070b0f120c0f04030c0305 74
    0x2c00500500310b400d00500006a41000640d00580240115045240e0310340c00181000d12580002104040104003044a56007040790301c1c40540003d00100b050b01d640090159890091400036000c0011011081600040c05002d810282800c00146030b80c03890028040300181080102d481d002d0340c40d2500404a41509100e8aa41594844054100fa8580d4105000a400e00c0001a200314608010f4250125641c0442c4030907503200391110119048001c040c8009800b00401c0640780001c005490740c8503030f540c0f00c100d0706000c7d400f0b68001103940340d80c00490010300c4c0e10449000c842e40303000220020300030001850b405955600c0b009124120317004004451644948400508041e62540305220303030f10700340e002105196420055003a030a115a400124201d0b5400c419050761a80c403400c0b4a00d0307040038020308000d1300d1070416080c5480c0d03845a00d00c0040c41001c0c5840e503240141c8000c241101c00710412902c00c4405144816142c0f03441c0c0c240391040318030318032040304d45105001c119000307100302c28 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 367863255 1250 367862005 367862039
    0x50f0c01140a0f05070c080312040510050105060d0f020d060f1502151810050c0a0f020712030e011101060e01050a0501031b030c11010e06070e0a0806010504090602190c0606 76
    0x195600e100322200e0f40f0240c500c1e801c801000c5541d004914404120708a0400141514031596418081c480c2450f00340103040038a01341001ca00241000700600a0303031035150444600e501c5645d800603481c2d50302c42090000b4001e5480c13080881c0d090660005048901e907480300d058880e880f141c802d08040d003207000c1e640c0d03201c0c2c4110710b11486c0c204400140c3c1c0d440c00c007510844854459064035189084141074030308a81c41120100e071411b002280c0310f5019a80a8003054030000a4001840804c0c10b10f40c280a05441d040c0c001800c0080401400d5a142d100320401010301806d80004e005040d1201101119940c0900880c0c0c00b84403940400140c0e50710a004205080021000850511420b00000c40141c40100d141205100040c1f42c030700f6924000344a0310b9080248034001d043d0a00b40404002c0903410492040781c4540800c0d6414015158041011811103008840003e500030751450180c0c0640110319200364800d2031a520480310f640c10548071402548584000c02540740c03076400c2c20100c440a8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 367864505 1250 367863255 367863257
    0x1030608030310090f0603020402161506030506040602031027050604290a0f081b04140f06010c061112070f0e01080c04030c0605070b0a0203060108041509050f0c01140a 74
    0x3d4400c0024080380d500c030302d0350b0070311184010038402e4032038000c0340c160b034040d011030214403004d080d80d1814400001340e000c8041d4841442403018614603115241d072036101602c05810280e0020106400c0900150124002c10040e407260024500c007804d086643c030345c410454031040e42044009041d62905104a0410003003151441c014a85a0380c2e4066000c40a0f030030998000c400301d000451b030b00c0c00383d0040c00010300328240200800c4040c0c01104020303074510850280511300f80000660f040f40d00d507210b83c0d4440d40c01c61100109580c0d0f5001202d01400ba80740c0a00528030f442e00001111f90700000614250f80c4182300a192a22a10000c860081e1507507a40400916607485c0034003550320515080341c106100c90400e90416840f91141401c242c450b9000c9404144002490381c00c0085400c0c0c025030181c91414114114504040003a00e0560700510051980740303001100741205045078024410355401100b161506440180d04654074041d9080131170119100303c0600800590b200200c60b1f8048032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 367865755 1250 367864505 367864531
    0x60f05011b0309050301051006031808041a0f0703120e07060203030a0f091b1802090904020906190303030b120f0709020c031b070306060803070b19020c060c0405010306080303 77
    0x400da000d1045001d00d08000c80402c142c0a6001603903590901078a4050b440506000c40c0c264a000c0025040399443c08801c2c5005404408103408144001c055030704071000d0582076965103c08920000c03492080c1e0110b000715203004103001c01072542c0018642c00c0c0e501c030460200411000449003641c0c0780340501c00c040041c1d00820000716000d45a030010b0031a03180c0e10348085441509030ba1142e0700000d000b6a103940200003542c04002a54840e90903103050700b40f0b102c045140c038610a010848804009001a00405000c0081851500e50225003803038140c480180d80d520a8503890000c1c00360101c0b1103403512803100800c0300106081d02280c201d0011054100412001e8035110200029406c440340c548005e00044c440300c51080d80c0c20400b81c03100c0ba070001c05000258110f107000710448001e9040180e465105111131400683c0f08014140c101c00c10f0f000242081d0112078054000e403103100000c68681c000c00e406d0041e8488160040e1050b103600742c80900140782c481030010380d40e0100b143c005580f226 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 367867005 1250 367865755 367865777
    0x120a03050a0c080f122a030417160203010c1106011203110a141209030c04150503030c06061302073305010b0a0f020708031b03040e0112030201060f0501 67
    0x4054401880c00310140d042c0201c505805454591558006124103071071082c00007000140e1417000c61a503540401004582d4069090350a020b40c0c0c81624001078145201000010401707024000200c0303090400d0f5051000e44d90540c614a000554035106000c9003c0d600740880e5190701e42c007841644c4101c20f9244024101680307010324000c1c0310f003414a001d505000c03040940d0a501351040c018140e04a00071b48a07540d014041c8170f41e0902e042e0440707140f5198500140800d104955010860f0310503540c040f5808141415480d0504030004020342c80a0703414400001c543c4005007000c02c0309445100700f1550f441000b0301d0400070200303903c16060000c05a641100c240810f54519480c00200500d40c0d200c8000c406140d544030804842082c2c0002624920100716804041e0784681480740029a1f48040c0070300720b01c0c240020750340c0c0c01405500101c2c10101c010b43c10b039000c000c0065900404542558840d1941d40e02610280e1000e04002a0010350078144d0101d03558414140c2ca104540c8182d561413200c003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 367868255 1250 367867005 367867007
    0x120204050a0b0d0812010f0f06030209010e1f030b040204150f0e030709050f060a0305060c0706110a210902060a08190e0c010f020c030303012105060112060b120a03 72
    0x10004211203035081d640c0190012a03120024402d0426204d44a165038402d424042200c450405138008166074426800a0042c5444080d00c8000c4810300d060140e103490075100142e449208e00d1003900d401283d0100b022020307052504001c0e5840c100343d141005030fa41050188010b9100300d0150f0583c002810f268800c0551192014841645c031915110302c00c04980e078002424808035901000e00b00c0d0b00ca80502600c65021129540c0041040b2140103809146550f05611258000c02200c602100071828006000d11030f0018041c6081c43c008580da10114524050409112000b000488a80b43c0418801242e407600c01c21002540092505044c40d52004048030350020050401d2600b04560b5010201135103103004150086407a1800b80c6852250403000422214040d1600c8045601101d14601c15480110449041d900410188008601d2403000d44148900703810005040380300b6180000303600d141702052a40c0b800d1140d0000e105088089080103078401c03184246000c80d8020302c0c4044002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 367869505 1250 367868255 367868261
    0x1020310060c020a27020c060406050906060d0b09030c0a08190c0b040f11060711041104120803040222090303060b03061c05010e0a03031505100207090c090b0a0216080304120204 78
    0x1601604081200c0704144400982031f43c120343ca10360341d02d5000005100402215000e8203a00c880450000d040764a040400901001102c49000c0c1c02c0c500d400020510000c03090003119a1103800404440071a4103034503200031a50300c418003004a040000e101083d945200d074800203145a0400c000b900b8548441d124020011540c2c0c41c1107031212414018925207840308009043d03014020700b44240c0500020041c4402c3c2d0782c0c407840b24070001000308018000700c91403650340c0c80407980141c0c000d92250744600c0864911003081080005542940da030003441103c09410141010348241c1e003d2080540d503911f054502d0000b070310420740c42448203c400c50118016120b421009014400200f0700380d030001007090030b1403000302d41540001c0d12061420501043c80049800920381600c0700c500d56030070110000d40f5540715000c1c01c1c008ca0340721a0750100c0c0d5445100c81101401c5580040d80e039440004001035911120042c1c2210507405403000007c940c0008000e0b90b04507054806a00c603044a15406c00c001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 367870755 1250 367869505 367869539
    0xa06020a020a020d03120507050309150c0702030303010e01080d180605090102010b1c03080c090102061f03060c0804031112031801150308090a09020906090d0201030b1201020310060c020a 82
    0x210301c10901d070b58000d6910b4002d400500d50298540c88800c000b40800801540c00040c030860078040704200f0300810b501e0000d4111080b01c01060907132010f0b200ea60001c100c0c2c2c8070351100654144004000070601000c0070b80898101d40e100c004640101c110010250b8400490b40780001d20000000010010f0324007500081c44518014030000030100e442c900001d950403144890300c8603078226076203220201500882c039550807400540c8240e0800c420140000d41e00c40340141420000551142806408042c104981c0051903100e1414400d40304040b0004090850403078060300090303004228021000c001146034400b4101c4111141e2856854441200080071250300030b810340c0d981c42d5034245480c0d011a0003440034500c1052015500c1190104002d0000500d40040c40c420344108087d0045580e48421a02410003d541c04101e5261500040e03000340b000401b611f801c194103040000003207006500951140c1c00039041c80f038080f51500001c90304401c44481c004e411911070b08040c044040c0440c02d00325 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 367872005 1250 367870755 367870757
    0x19030b010512041a0703050709050f090109020a1404030803150402090d08031801110901170705270d150c031404080309070b070501060f0504021c0b0424080606030a03020a06020a 78
    0x42104c0000542c100c0154100d5040000079520360612050561060b8403400030f00b0202d8210354400400c1000500c50305062040a110716400101c0c4503030907000e440e000503070561001c4419151030b50303030914030324560045070f00c842c4005d5204020310b0706141c14401c2c0c07090001e02030309503480d501c0c45550301a040e50001d0001d1000090003c00000c03d214240691214034a20110054941201c3c0c0000340400181c3d4482d524030030070300401c102c0d10b19440000c2d2410447c4012100c90f00340100140c0703549501e1100270141d000001c0c0c001d03038401d024001580080144d072503d002c1081e0040c2c03031400c404440212140010705481c0c40c010901148201f8040d40d040105d18041da425542d84003c4545a5480f8140c21a07207651910020005003104100380d5000700420f4800703501d044590001c5154606800c0c01285540e41e5420700c80346142c441350b2050540d4500c08000360b03100c10303c4000340c41c0303200441d109100503807240ca00007650f507040116003001c0d03003036141c1c0044c50000030f1a51400040c0d041008898 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 367873255 1250 367872005 367872023
    0xc0312120402150c0304092421110612190e15191506080907150c14030301061805041b08070e0d2108040213180c0b19030b01051204 58
    0x13070103c006200401c01001d01c1300e000903c02c07811008815507002e01c1d1541c10304100c00768008002408079524105e4000204901144134000d07549840c0c051000d00416054220b00003003065030081a1004170741c1d0049420840d440000c2c0030381c485050070343d844401c245405420201201030055000c440e0f0540111084c6104445880034609100445110080000901034608010000a50400c800300e401c404000f02809804d8281003c900e988542040700390104542011440140003a00d20402200024002501e50301d5070361300c0004021801c00d26840c0002044100005228500f134400c12a118003048114040d41c100c421082d00c403a2801015038090100c401c0c00708605580d60039000503664030070591080b50103000071100d124411a140c080c0280903070901400056540c0005000041c030b0503800c00300c0c1c503584000445030000c140390300c0140b50313505801012945600d160090000e50704a80c9064540340d40c0d00c401201550341c2030500b140861000c10800311341c80b0010081d00d92040c002e1160b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 367874505 1250 367873255 367873267
    0x3101a06130317041806050a060f051201061115040b0c0306060706050408250201080105060315040e030a270e15060a09081908030f180f0c031212040215 67
    0x1900010342d0300001d0341c0e0f044a0000e0141302d41c0c08041e82c4414038000d83c0380304204641c102030200c0e035246c920b8000c440c184a006840d8420545c401c404460180c2c001c1545c140855942d8000a8850b00c22044d0911503030040004503c0c0b0307410b003424054465074028840c005c194885010718001648040d000d1174200307000b04035450100e0b6050084c640544e1099494903954124184050002103c00c035212600785c605082c15000350b0b90201c05941900d2044a00710b9680d00e131000340da81c4811400b180e04c4d400604140c08d200c40140040040c0690f03003410784810740c5940d00d10111984c020b501c14010070a00c0c84d420303402d10000b501d80482c6503200002030a0141c2d43c600903800554160000350050000034403410b014000c1880901600c0c4511443d03100e540042c19441d0356500d40b500000b8907046000c01c00300d001814200d0812181004440307200309545051844040303154550000c804114041d21070400401d140708003402c1190305e407070740300c900c03100c3d058a81e07500b00b010500c040d4001c011240c00520071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 367875755 1250 367874505 367874513
    0xa08090f18012c040f0b09030405150403020a06050a020607030e011e05040204060e0c0702060c010603140d080f1009231501080906150d15060e0603101a061303 70
    0x4090103842d4141c44003448908058503074150960003d402c98030700850406210010b550220b070380140d9903000000070099900c0d15046c500d103005c3c0d5400761f5840b07054004190511044407008109490080c2c034000703451600c07807505030354030f1203910120320059000b10300041c0b13480c1c801e0340306141d03040c281c03800442c408a2815062850344c030a000e40e403401550303440a2000b18545441a44020015007192140740d10b041e210702c1520b8001c24601174090040020000c1d00e401080d4480c1010b15802b081080c0383c15100d1180c1d40c0d9a84074002d603800884c880c0404504051840305d4400d210b0040b201c40c00c10802c0c104500d4101400455120004d4010380040428600d00c110030154442c0c02c4003161640c58804000004040010140c15a1310580109003804204114a0b81160f28907000b40c810a1160002d450040040d20340d40f9962800715181840204040000405040c05100101d085503044030400100c102150300c0b040c24036460703031004c1c4a0183d450415402401c08078a1002117060711907500c0e11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 367877005 1250 367875755 367875799
    0x30f11070e102115020f070b01090579050118030f0f150507030509060f0103060c0509030f0c04201602040207020d0f0203060601020a08090f 62
    0x6180610100440001e1201d248048500341210045010300b8080c58001d4030340c0c50f40c0b0307981540b286007131980024404040b10440d5086916590b407115510490351380d6032004100404042e070f1002c50f41c0407114400301c0c0e40b1480210040300c098030f40791f0643d01c02c444042800a40b4512000c0549003903004940d915444a5405e2070b00c03081005108007200c401c200c0d4041000b00310392500841d05002000d85900d80c1420485401010749910650a00841000703040500b015030082800401d64488200c2c190002001c54004070300407101d9880c2800341d91141b10410b6150ba0b000c646640303251083c04010800708500b60406c00d4100e13100e00b00300d85441281800b113800c00d42049148040c660003480460128103081c031403118124200c00d080480d89850b030700200381621a84d8440c406245403c08614195951135044404866008082042141c0f0313600c0e081602c6083c070701c0e084c0d04c00c2c00b494001594030b500100d00300d207d60b64401d40e0280b6210320101000444164044015000000e007995064a00307007030381c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 367878255 1250 367877005 367877011
    0x40501082508010e0703020408060a0c02030705030304031706010e060703080403110a0606140108060a030b0403020106050d05010c02150727121505160801030b1b0a030e19030f11070e 80
    0x290380d0035525030400c070121040703844c068602c104161040104000403e400314140b9002000f0b0107001c241c2240c1c04404919500800324003601c5800b002040c4020541c1040501c00b41b03400400040c103540e92050015100c0e0141e80361000d030851400c003c2000001d10540c100303680b0a00c00e007880e0710040401c0400600e0300e0140c100448003541e9842c1c09001c440301c40030354000c0510003480c281c04985000d00c082200e1072014800100ba102064001c01c017018001c2d00030342c0252001810a8404074400e003030080c0a04070301c00608016028a1705c2440381c4050038400c991003202c5035201c10301202403408503a00c1c040013181c0c1070003c00350031301404181044c0602040c0c81e428040c0c500303003c40f4140410490308076500a000031050708020490005042d40002040d41180e420500d0381d4226501c480c004203042d01d044040d43d6900b0b5000130480718064041d801910811b20607001c440504070a2800300b518400310401c0a80406c40c05a0f90780f400c0c51265201d016000e00b8441650521a903912241070580c02c19 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 367879505 1250 367878255 367878257
    0x30106050a08252a0c0510020f010f0902120a1707050c1201020301030b13021503090109120305010602010f0b09130f06060303020d1e080105010e0d02090f1503030f0405010825 77
    0x820800201d0410a868000886030713420404480c600c299540d580344038007a1207080d0181011444060166000b0700c0440701050303400000340841401d0306e00401c018415824224443d03030700b8620310400480c0c00110300310b0b190b500241d0300e00d1011145207210300c113030843c1c3d0b0102c0341c2d841005120700d0191508460010040e040701300141e2030b54150318088409400c002d22080e46812121a28000350f912090000e1440d01e400c5030f025a20303250f040c061805070004d94005401c01c0300700f03540c480034a03034150310490494449600030401040c086030400c054501e00c044407035104c1c00c910085190407580d00d01800145100d0702e08007240d00321540d120020b407042e40c0d100ba000b40c2c010700d0304c40030001d410045450810b15010800301d50314103102c4000d84100018056141000410031655851351100130542c1a804d0300242030480600c1c000150081e5420120f420803c80510a550072509040000944054500b22002035040509240044407507a000424024181018039000010f060b92010000c06c10203103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 367880755 1250 367879505 367879517
    0x9031005010f0e041e140d02070305100c051206010512040503040302090703090209070c080d0f020c012d0b01031d011a03070510050304150c09080d05030106050a0825 73
    0x58000511014510340d8031905440e0807482c1007100003040440104040124100c2151111456090503c1d00c00310f030041ca0001c600c1034003007c00005070001b0300d050840c0d1044003100c041030505003600c41611800074004002c41c900707210001107134031520040d0703a01500c10300d0504c0c00c01d048250006404581940e0030344c2c80c2d8200090070310960074048521580055a03080c244250300a981c08034241210041c1000d041124000c600313410868071301c04031010050008c1003030041900000c0008000c1d800041400e4030f035840c0283c0210403541b2110700c2e900c1480b142449032049142c100c1e0900240a09406031410150780d501c0b005a400700a418094078180c0c604000079807451524a0b820201d008403020030310a52100030100102d0707490317403190007108115203801d079180c1c2c03194600190445800050860b505041030b45110410340d106c13002804840b1840d00b103a0a5580284081e1b42c0341c44280194000100c08100042000f40240700150304030541070380000c01c4e1a90380400401828182c94020700240d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 367882005 1250 367880755 367880759
    0x2031f1203030e0a1e05070312050c070503240702120d090302100510171e1c1103040e090c0406060302030619080d110703060504080712050c1209060903100501 70
    0x42e141c0700d044480500c160040600748404c0d103844d800e521440944451712000007143c14204003043c800440199071262070a4407603c072a04e8060310b540c000310b4083d112840f9079100003980e071800007043e40c032054012400c80c40004071500c05072482a0014014004d51060340c406521800b003510061108191030a0009054612840c0007428900501403c110640c2088103001200000300c01450480c0c05c2031107c4030300400350078001030500e9640c420206d142915081d164000302004a51024410140c81c1608142103c6501c1514a19140d501403003042e032040c8002e02c150300c1c00c02644d64100c0c807030078100d03280c41803454005000e0b101313280c01030320020380c000c01032000504058104c0c11441c07500f180820035990405125030390f201d079040308110800100382c1d480c1d12092018400e0002850700818148480e2800741421061540300c07800c101c6000400b983e9a032040c5101c2c0c0c0640300b01ea2002c60152003080340c1c175040307101035811405289500600422001c495941d04001c950000780d02d6800c0800e180d8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 367883255 1250 367882005 367882007
    0xb0705070c0e07020d05250f03030501050108040803012303061501030506040c120203040305191d0907020604170c15040611070201090e100306020711030606030f1002031f1203 77
    0x388031580710b0141010003006121007550045003410385840ca6184c010b444461356026141c0c4499051034010300c6480c090844020b02c10103402c1c018005010b82c40a00c03032039036650011610f60400300d801500141d0140300610103050412480c0380100216a00c003c3c0108400380024100401511070980180e640d2044a0315960940a15640500100e40c20860300d0502c21000d445071030094003000c0b05c01d5000000500b0140608240e411010700c0d01ca02d01c2c1e1010b205080984042150112001c0d41e0710952410309503403904003001c40c81804698081e1010f900c582e61017012402d100412001c40c0501031004281180e803c0102d078050007a501c200320340700d0030b181c1007a00484260010b01d48440d082004100051b0360050b51103009c841e21080701044c00c1d41c07003180d01110444941c1000385000d0000544038140020301c0c00740d01d450102202500c981d03480b890b04141da61813407100341c1c01481e08040e080d44c9624400390b0103194040522684d00300c0f840d401c0341048042a245800c1b0a8030b5140b08900c0000781 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 367884505 1250 367883255 367883273
    0xf1203030f02030a0518190b100305010617010f050408041701271103011406010807020c04050c030a1a010e0d02010c050d080108060a0c0e152b0b030312060d0f0b070507 74
    0x4401c62001c0c0802541c928000221820300078405000034235903001192424502100c03a00c000e50700b080003000b0594031404402e46141c04004945019030800307407251860103080c0304160055910522081c5010b19121303040301c4141c600880d414140d541c4800080400703a48c0503041109044042c07802e180360301070740342003528150b4100e8824081da241031401140d10f41d0801c0010740080c03007420700540b0390703545c400200e01e4900810102c603040303400c0600b8824901c80341006103001e0400d512090114428401c10000282c490506481c005142540a42c1140c04c10542c1009511b00600d4424031601640d20380c94a4000407a205c00c00081d08900104070064083c041207420410810044c021410b501c0c900611040801500c18030800b40703103501603080014038003191789006034101100010600e01400344441e0120b0710f40d03494803904104240040346000320842e6140c11034440c0c0d42242da10790109010b6480c0c04a54221651815142500007003840181030f01d00c00c00d11135035880c0da1005249000206 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 367885755 1250 367884505 367884541
    0x7030c0219060e0a0f030207150e010c15061d01030b1003030c080904231005030a0203101d06130203150408030a0911060d020d11040f1203030f02030a05 67
    0x4540001c002a125580300c02000007a040d04500302140e200540c140c0c0714107080840d00000c254211600d801d808240e00880e0a030b007102c21503003150240b218110b2040e03c0050008a100c0e001500324403c1c0c9000030b5241b00b0514203640d03080e00004a5940b2003099210b4902e28501079101001e418004000300b180c401003866001c80301801500302c4a103555405000301c4128000241210030203d50499143c4582d031264548601d500100c00c004a4001c0749036101d0142540d420240c003000210100d9a400d0028040a003681e002d0010f140c5100b031240c00364002e012261069000f2100c2c00f141e441da0f400704102444c0103801016090340c0da407c0c0c5104040c900341d4102410b0200c81d62200812010629180036280e00c15503d1b003010403110400e2a00320440b584000380e0942c0070f03601003604104180c00740d01400d907000d210103040050b403078040000c0802d8003540c0b04141c401e0f03100c0e4609001c0107040d1480720052621074140880c00c51202c0445200782d0b041220b2001c0400c0c0d070350701000079480108280c504 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 367887005 1250 367885755 367885757
    0x70209010f0305030f03090313121209062a122006070807080604090c1217090f10090909060b031b01120b0111120c070f0f090906150305030307030c 65
    0x712035491075031400e0301c0c0d0007142c03050008401d011002421030481441100c540440c84441c0c100090349480d500310744803920042c10364840241440b001c0015010396070800070703500e05803100203203000c08210314111038520303101c0121450040501040002c40e54244a00486120f84a0101040000070107a0a00034000e06924040c0c0c0250f05000e00c06410000a90b0005c140e86081c0c101607503900b002c0750180168403c0100700d0311101d003001501c058003c03c6c1d10015403189880c00c0000084c980100710502810200325030020344074406108614010002808108141c10201102943d5505850489101200035524662915052070362407900744401090301e4075148501561104180000740180841040507411039640c5000f9001030380a00c40760b000d840d01007411030302c02091100120f10107800030250505244201e200100d100d00d80b0548010a584120714040130032490803903184041c00c450701055a030503680700c241d045d04c070400d1030b0200c018502650007180d80b800d0606009007150601201d2034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 367888255 1250 367887005 367887029
    0x106061103040b0f07141e100204080c0d020117090616021c030f09060207080a110f06060d150207050d08010b070803010510110d1805060309101d030c010207020901 72
    0x801001201c00540d220505400c43c01d548513205c52800d49550f080d40018850144a00d03d01c10102c0601d0025140888020605070346001c404950124140d004a018940003504502c03010400c5040c09280c0c00340050051518010300c547c0c5504002511206942050050700920100900405181d90302034100030544010f0611901080d0058503071100c42003001c00701501e03108418076a01080e0090208150005e0302155034005518241c0d02c140d012121883c00f00e1303114441000d5054000c01c503014020b92070f0b000b43c519580c134034082050950400313200b240c0e081d2403041e120030304d0300091018280356413041c401800340f100300c50750152401d0340580c0081003400040103428009040d4a003541d04441c0c003030310742c0710681c00c86e280c1c141ca5401d0000000f014a01c40c0f08007103441c0660020380c2c0c800309491130302c10845080c0c4550a0269611003283d0714903050f800031084008809503540304a2203c0c3c1038035450444000c0030000242154001900344c441a9004580d030019458100611401030031038030100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 367889505 1250 367888255 367888259
    0x9100f0f031109090102130806040b010e012301050d06080c0103270602070c09050709090501050a0302011d03070305060117060a051003080f0405041d010c0806130b0a05040905010606110304 83
    0x840190701c0d02c9a82c41c0d0003045164007188460509405813244250310641d00b9020070b4840c03d02c0b65545a0407501622003000034000094020100808141a280040c502d20110f03801801d40c0a03150211030303070041c100281000400c52480c0345104040180221001816410b2005000102a18200c1a141e900004240315050110540900079080c0c1039100c5405070312030015040c023500340002a401010524100740070001859802000042a128810030810903662600144100d2003d01c0c00000e000c81c444d2110741c1d105c3d24141e40302d01e50f80c62006003112107042d225650b243c10300600f82c0c80032800fa24407255003284410148103055210401c2101001945400b00342c40031107950340d100150400d4400646400c3c03e409030b00813140035203400b030400d02c11926507c4040c114010010084151940303070044649000388540d810500600700200071460f8600c0c19428040242050710809900c10452030f80000d4a40b541d025044a4601410002551070714141002e40f04002014030b0300d016810800c42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 367890755 1250 367889505 367889513
    0xa0c03060e070f03021902010203061206090606060f090409080903210f031b04120605060f0f04050c04081603030305060a0f0902090109080a1b050a0807050603060f09100f0f03 77
    0xc2540482d603450000c141c004405004e40c02442008070b0019040c2e51030303100500458054000303500940c01a5001c0e01c1c450300d1103e6050300c488054403080c000340c100b8408104540f60040141507160300c40c0d214985042d1094000030119241c071141180e0280022425250624040c0703c000e01080501c540904205d0f041c003850202071050404500c2800c00110210300042c40d001040b103451040e01c0c4449943d02d842e2260992096000041183c1f103508100008115040111404000342006042800310340d10134010400030b070000406d0200c55034014440028080004c204040600403404180020f55003541401020340b14020301140c0509900101085041c136498282c80c200e0389104001a04c07030b8071400040301e02800070ba000125030300c141d02d240001c3c00103d000429620588022807405250740d10148420512180300e4031500c0d801c069810441824410020741d40000020138007c2d0390b6040b42c000402500d01940c655800c048401d00910180f0140604c20010380100091140f81901c1c40ea0303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 367892005 1250 367890755 367890779
    0xa0f03021503130c0e090d050a081602010f1a1c080f07110d031d100f0c06020708072103020910032003240f150a050d060902030a0c0306 60
    0x1880e550700900000001c3e038090601c40040c01c0242d0141c44540f20a41d9828402c2d14184241c0d04206070f80a03450200c03c0f154000d0045070751070000e0b6264181180c2e2400f80e41880450071255080640d500c03068040e407800080c0c41421444495164100da24029110a02241b50300440403581c46c9500b100d40310000c07035035402c00d0b1041442d040c1302d00c030359400c2a460192000ca01018040c0e80041c0344510031802c25030050014403940b0a00310708014040441c40400400940004014011480044246040c544584000c1410314003444001d0b2402400b030303854020550000005850743e07000d403451880525030020002400351124541541010303101c100085140c00d410051009059980c1c0c0503000c20102c0c41c1c40c01980c00907403241c194407480d1000210002c00e142859043c0010080214a9018540450881810140601084421204420000a680d1080c80e42509000d020720a180e1544094003401014040c020405616420700340a0030003540c403043d4580080c075040400034081514602 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 367893255 1250 367892005 367892029
    0x70f0602011802150315040903050903011b081906050d0602130806010612020a0c12020303181f02091c0302070501091409040605070c05070e010501020f0f0309210307110a0f0302 78
    0x200360b0346d85030b900c420f00c1411a12205540c0003800d0441c54011302d60420090050410150000c0c0248c50307a0010310243c0c0609820302e0008580220046600602485d0540c5949403007610300060f45d54840000901e0005080e404032203442c2c0002c4d40c881c034150f4510401c8020000300c0002c040c40e5040c054060000008501c111081c50b602040342d404080c8200c1900c56480c0e0010505801135030540c3c0c0c000d440b0b9104a0f211044402006201070015000227103100c0e15019402b800300c8507020b48449c5501a520043d2069486100880c00d0790111440c6502c1100c024880c0d001811550300c0c000015118031502d512807070071440b15001c00c1c006600e42c14066640582c0c000d000040b1542c407044192040103078181c01501910854001140c018461455181071b100241c0031259460808400250384042c85c40d40c41845400911000c11b231410070765a000c001c3d0078840303c440744c2101d0810a041c9180c10030030042e110200e511010700040c0c01e050140102910707004101558017411a008926400d01c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 367894505 1250 367893255 367893289
    0x7140a1a0f010b16060f0e160302180709180903030b0109080a020f01120f0905071a07060b0a12061506030c02070b0d060806040803010303030c1e0e0a08070f0602011802 74
    0x2e01a4080081d583e00ea0740e220317500200c1009085080c400c03240003480700701080d201c0c41c0314820051402d90107060050f02140d030b008200742d11384825400c14102030100030302104140301b038015010501e64583d421070f6485c0300b10b1003c0010b0522036820001c0c141c40640c2e02a50610030840707401d1280c44004540501001d80540d659204412901c00494401c145c1041c1c0c41d001c01d10713203003070310141c40c031a0b80041c07a50138045c44c00c4a108980780e1500700c0c170700c00e10110001503002040100c04009403580c0c0103200d011800400f10750002b55501c10400360f5058040f800c499184c0d0301c041403c00201881e60040141200349420049000400c4000c1d42e108081e014040010380d01140f071110054864101c10043c00c01c400588110342081e16003042c4542007800100e0210b42040d90717000125104c1c0e41900812485418420b8280b1402c80b001d69042c512041403a801c0529020085203c001c200000d000404a07504001e80240c9040d81c001d0031651201c07800001c560403040c061015a4808030420308403c41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 367895755 1250 367894505 367894507
    0xc0e04080301121a070507260301120c03020904080a02010e0d050301170a15141e0103150b0306010f061103030405060720060106050306090f06010f0807020307140a1a0f010b 76
    0x240d420305501e41c940e80811500500000d44c1000042035100e40602200d40c410382ca004111204001240925147d80c5a10382c5009014801000b0035550400d109407040e010b210200001b6482c0c0d0045404c41a00f01c40540f0340c3c0400064031804680d091143c070b4000b205007406424102c1003800b00514520040c0325005416021720300c0da0040c40810712820f901a6407104101103006c84103050600a0f04220003208007040080380003460b002c0b1203034040c84103081240800350440e0700359a07602800030b80520000031450759441c07802c40e0301e841c1044518040c3c8103041d15244014940b1b07030018600780701c41c0c80240541d0018428040000c80004515801c005581800c5044001101070300303078042040f101814640c03050350000034105410800440c010041a40d90040b141c0d00d0ba076202c01100c0003603420500048036002d040000703601c1025901d411058600c10341c3d1520310345440380a00c10681003401920368201c82c0a00080051041c00d05114810404c6807140030b142c00e6041144148051051034042c1e20 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 367897005 1250 367895755 367895789
    0x3051804051e0702070e011e0506040f030602070f0f1b09020a08010504091b06090e0703020f07020d030915030605030f0c030a0305072607050d030605130e07120506040c0e04080301 79
    0x1c001c0c880b81c030140c15154500d0700d003588d66001d801101c0102c140c3c080700c1c1c1602001d012600c1d00f08001146d040e00c1004151181061a550302c0400a43c800d01065510120b01d90f40480041c10644141720141c1c050200c1480601d501d94480c80c8000859000c0000180f04120308514180c02082c89411500308450000d07000c3d40500300700641051003841d800050f078101d00d01142442d040300c07032041503404007200d950056440d4501030f0202d02c500005c28107254814494500149403116518814a00c40d01d4111245135841c0c0010003101c5035220f050010a40b14002485035042c20800a03501102c0107004102c80c001c0e20001c2500c84895000c09020004002504014800c100ad0b40c5228046413400010b030b8281180d04400481d00180821915801a080a4100c0e0ba109004a406481000b007600700c25a181e44a190010035440280a000d80660100080c0320420a0f1000c0042400b500c0504004c1c581460f003e4030f0181107401440003052500140310108a0791002d0780d0559003003074410400c510f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 367898255 1250 367897005 367897007
    0x1b270209040608010203040c03030314010605030c0a020703060c0f0e09160807032a020c010801080601050402090a03080a0201060e0a020a021f181b06032a090b040303051804051e07 79
    0x80340c000c3c0403035600000a000c200a450030426003124007a54013003001524a2001a140010038490a00065800d1021a42d613031103590003820319210500458101c90740d40e640341c1003a01c007250311110202c1c08414501101580000344000c4d0500210ba844100703251004071808d102d042140d54004001202000520660295100707c0e001104c4c62a24030107102100001d81211442c0c6d0394140042c05188800031803540070b0403903107042c2c1344143c025281c1e0740c0c24001803100035086070b02c07055440207400390000041a044c40c01854101c825078004100740d4140100071a240c18054002c03c8424410014601c1041d80403c2c51281b00700325150b080c0d0300613020000d00000d002c100c0e10741588540649852030810081c40158040d80d601e10303102500f0309548880640840d4021390100d0703101c1d01c06140701d0000e840780d0035440104070043d00b001d0594607181c0110030860313082a00110f010030000103c0314440003419017012060501120140a04e02e004001411032142c19800b03035040084c080d010850107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 367899505 1250 367898255 367898261
    0x1f0909090503122a04051002010c0206010302010e01120e0303160507080405010f030b1e15070506061309170c010b04050603031219020a02100b0a0b120c1201031b27020904 75
    0xf448060f8a480720100c0707002c4e903d0440340d00c1489442c0c4200140300201044038018000e0040c0d051854018090b03507172031600150707010745c0310307100f803a0400810810080e104a1944640010380b10f00c08020754803072411003c0201c0c401c01100078001800000e01c9083d0002d0414001c44058550a1804401c0014034030300a902400b110b82806500c072001d03030b4180c0215018407003989602c1d1012a1000081c0c030748541046d0340f5100b030050190070740e0418400944181400500c1c8514040c1d900c3c0001410781d40780d111101c0d154543c01c40f44080301000200352540c3c100901411002030070444082080b030500800080d50381c4101300b00e420420b241c000c0040d40103480000502d200c1c001c010030955130355080303900003511903040303460544105107488501120750820002c01d41c151402e030603040e40303000b60043d0f072207d845a0041c071244181208100480084860802843c02188210070700b40848403e0010210402c6270360300a10b0b2000f90300c0009a000507001e028000607010012801a0b80d241500082806 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 367900755 1250 367899505 367899541
    0x1809030409020a02240901060e010503030d0b120a0317090d080604050601170a061d010e01030f05210903061f27050103080c060c0405012c1f090909050312 68
    0x10190340d4100020a105c140b101c0544103880000017040095140ca4810161460a00a1540580c8140041011002c082e80540d801510003031a1000000c20410564a00a011034044001442110000905990013100c1c0c0350405da00d003019000c85400c04000034a032000080210303110355203410206001d03034058010703002002003040c416042072030b054148030042e02081c811100ba00440a220300a84045c04100e20b042c3c0b125440c100455900e107485201da54000d00360107032018043c48020003c105141001e05030503d0303030b2044003615142c10004060400000a01901034a6207001d40500c8614035115424240d81d420f68818820407a201120210303414488081c01220780381c400080203010900002d07200c170481d090115525075407103150717015507405030f48a004e0100c1c00c0c2e4014018070010701030054848040291044120809c10000038040401191500218800d02400607400a601c60468405050706880c140002281581e4042e0b0741e1203444161111301411001180c0015040001200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 367902005 1250 367900755 367900783
    0x3031407210e09010b030907050114070206070201090807030605040201111b1309060e01051005060f160807080a0c03030b03010e030d0207030e0d03030b01020c22050408271809030409020a02 83
    0x90b40d81c460505c4031090740b042d40d09100500c501440061150312604501d603d021149232070341d042c45440d50a1100c550030412013241440f01111012490307440c100b00d0075000303500480003c205400c050002500041c000e0204031a0303074101604481411000440402d440e07041600c08907040300c40030810400401c43c41c1801045107040c0f245481040105400041c0265000308203002290385e00c900b00591031240485038485001b00b804043e5a0b540c580120b54509406428224602034042d50380a04587c08440203a010940c900504001c0c90342c03511030b11039002d000354002c12202419480c480d42c0c80c02090507840100fa00010001d081500c81c3d0202c4001310009071100c150240c4900e80a4040c103001a03009005104103005400380d1325007101c15283ca401030704450032048010103101d0000d4400113005403442e03101040440034a8506504a40104208040e1549002c030540100300381c021408462854070209a024441d05400c040100d60448a8252005030b03108014401a400c01640d121410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 367903255 1250 367902005 367902019
    0x181201021b01090c080102071505091204090c0e04150308133c0b0f070c0509010902040e01090504081c06030c09090b0f010f0b0d1d0703031407210e 65
    0x110581054202d0580503214031207002c112605e03105050300300d006542c4050301d4000c5184149440720300c0380e88100e03040029602528070705030066a541c1041d50059100780c07842c654490103014050351040d4441d1640208071003d025803903ca400c1101c50050301d00001e060301d04e0000d440825100950b241c00010415190105000480f548802c81d0307032119400c0710180d011031400d590211246a4509000b651264081a03040403140c42c06005240c01c07000040706c26644c59180454555a0744c440c060003001822005640d940c18002241c1c600d50060303002c0c03244c0c941044203000000c0e507030130103071007801c441060341c1c0d110001d503000d07908060300203a40003070300c41d03065450003080c080700e29088100c455028002010950b200d42d0706100e4800c80920071000002a00301c01808003400780c0000341200c102c020804030340b07100f1500c6c1a0110400720b004415103071b40208070400402d80c01c8840034203050380100700b0714200140d176140c2c0b0f20104888842c1800e481031604113031032058000c2ca643c0d00004005040700b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 367904505 1250 367903255 367903297
    0x4080f0604020111010902010f05030408071a01080f120d09020a0b1c0e0d090902030c270103110307050d0b0a2c090f1b06070f03020a060f0218120102 66
    0x18a45030031040d2070590014030920300d140120001406580b07410b642c1a510035a00306200b4508851a81000c0d0040b1490720041050402191105103000d04411040074041c1ca0303549880082480c01c2c800810070142900a00010408106620181c03000354452505c04101c40704070b0710009003142c600e41c1184038000004920b03400c81220840c1580844818960100179240d074842c0c01c00d50b43d20003018030701d000403c03460052004d48815005540c0020503240c0c21400c00700c4c1000540c040b291501810944000300e005100100d40e894080d001034001c400302014a5401c0000d4000c20383d20170015100f0710140c6a50014a598407840505002032130001804c0c0340c00361490740b841d80c0304038150b411015030380324050100d5065000403440d405e84183c100000c0000d01d000a45450f0259101e04e5a551300400501c002004110004094003800d40701780c0c01b810409103d441c02e80c00320b806459160000b10301c103100f000302200b40c462520002c4901140c00c0120780c0c0f18040ba040c00f82c40744400c418986500d030186 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 367905755 1250 367904505 367904533
    0x5160824270703022a030901031a0409030203120a0b100f1701031505090607020c0d1103070b03160201061401030513060f0f05010b0c070e070c120906033804020408 72
    0x5070103800c0030311600e00300307031000c442d01752400078003401c4001c42c1ca42080041c04115130007036102e0b005080c0400d41c0c04070038900407800202100c0c01e041080d40035800002d10002901c00c50f6094550120280008208151081000c180d030030038000000004e100c140d40c82d0341c80c254004c00d0101c54405038600d15040c40d603100d02d000358a0030315801d10f10b41900c0c01d0074080b900d50240800d00921070000d070350052001c1c0c40c0301802c0010380703011440207590402d0415207a0466460034000340e400b51040505207031b0f0302c0c20094090b0052a844001d104216407506ca42030040c0000203500305400003007480e010441e074507441c00d04408a00c0320300c8000c00c02860082031010503d1150001c084043d032002c0e0070090741c2c3ea00c1003082e60701e00c902c1802d144035400c440c8050014002d80d0501e613800540c41c0c0780c8848002000d5480140000c100003041010a121490411405915000c1c201e00c1c081e400741030030f4942004101c5903143c0200b04054031030b400c03480c0084203220b48666058400420169007290492400850 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 367907005 1250 367905755 367905757
    0x7090303020c090610030213171507030e03030712021210210f0f0521070b0c130608130c03120f080c070b040609060516082427070302 59
    0x110031809800b854034040311900d0290501032042074050598101c0b28000c45040b0002d44c4400780310742055804040104007282c2408a844840500e00e0090482d41d003070760060b80c1c24000050600040504110360480718800100c1500d8000c00300e41007130b0500c041c0710b0054002a000d610348840b0021074110130059401c00050000048900504509001d4600c44c15414a0004a1400501004142e41c80300000513100382d42d2102540c05502911030303c0244000a500c40c055001c400c0481507404034040091220701c004141d0060540d184180c540400c18603004001030462060400340a100c4001464124907082000380d1284d00008038400a5100d2030903600000e0101009800540e00d8401028141c0c0030b4090117014020340c824443c204942c0d69101c030240000104200d90882e1a41b5069001455030300503a401004403411104503000500700082c06844010b0550840c8514040c4000100d00485a40c0306400020307120403c6050441d0440d801c104000f41006000c5003004040080300345c0d0682c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 367908255 1250 367907005 367907009
    0x10e040c0905101b0f030203070506040b01050a060c0209060f031906052a0d050411130207020108060306160813020901030804060e040b0109051c0804090903030e01020a02190302030c060709 83
    0x118841410540f01a08075902101e0101154084222903050008150309094440c1080e1091044900c0c05100f982d40d03905148080d20100c5881040e1001031020303181c5054030002070116031821043d03c06142d0000f0306881d8010346903501074808110041c0e00c9031400e0200d0482c0c000341e411164640421440d003d80101821038840c00e00b5465002d114080c540c10301403e078114040c0912850604000b10140001058050021280c00d4044120801c1da40c40e03452a0590003512110016110201400003510715040103010700c0c4260000410081024460b03d01c0843e49a51071801201d02d1391404100e44031500d403074a01a510004a030000010046030100a00c281c0d43e0590708c0304403225821061100341c400d40d8040c603000c101c0c00c58050207a03003404840304032441d1902c407011042d031189803185400c40d031194012080240e1076005c0403040c540c06014400b1070280d224001c40c9045600b00c0001d407204c213214040403d0700405603c01041c54400c01c1a240890f184409036000760400c0c04000d02445824 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 367909505 1250 367908255 367908259
    0xb07060f020a021605040e03091003020c07060903060e12040909060b0414160903020306040b0a23100b070b150d05060a090c0b0a0918140a231501050306010e040c0905 73
    0xf2aa000c20142818025134144030540c7c0011401c20070410108042e140400e0307103980c1003550074000104585410003241000306400d4581c03024803800d5090000964184061040696210550401c584c80250007113170101c9031b800400046d10b014500d08000601407028015900038144004041070301403941c2c6860081d44d52006d075061415618405079100386592001a40c1904200001004a24402d4800340e10540100d000079130191510983c52030504032005101c0061506410400310a075201ca04070041c003807090320b50342022890b54424a200c5001481000c41d4030382a0650310041d00c0c5c0c00d1503841029400f02c00d807065440c0c04607600700200301c0c1080a95070f56181920004010b502070044820307909203503840d441491300300a01c0210024200e051010444d07034030402d6044e1410203100b03040c02140007900200d070001b48004103081d445c0c20445000300c06a00d000511480c90072102c40d003105083c017030030500e84a96400d801a90018201682c06d5002410221200035007903004010300e0503a001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 367910755 1250 367909505 367909543
    0xa050d0204092f0f090a0509070215130f1e0b0108011a04020901050703080c1b06010e0a0605010f03051009020a081f15050c07081e07060f090b07060f020a02 69
    0x1201000a011008525042d010788008000d810002c0c94920014031070224060300e00c2c1d801e155110702161680501309c80e5080160040c41c0081003040c1c40118043c0c1081c030503507070715100c01d002d501c8540c00000b41d84e0000308400031019a02c41b40200c0c94005150140d00b00310440542d6944007240c41c0a00000c00d2200480c0c04c403c81403450b6032505200f520a43ca006942d1142030400c0303950103030ba94180c0034040300444031741032200c694040e8003040a01030244080c0050982e952400a6001e00704030b0103402c01c8002070622000380461799003c003401c0042142440c02080c240c40d03041d1440c041c00155007140c0d880a000007000c1d01e54903082aa0355010301c103034118011210007184845056074169015450150302c080c3c440a14062090003c6c024030704401098812155481658501e082034401c241c00742801c1200071003240d004207011280c0100540d0800d106902c00e0742400902015503405089000040461715105028450b032000d86040380903a0115612821410065500d50031000200c410b000c1c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 367912005 1250 367910755 367910801
    0xc0a020709020f0405191701090507082407050f0a0804020108071d1e03070306060611070305031605030d050403021605061201030204092f2b080a050d020409 69
    0x7026100322200040c0c044100d030304060030141004900e00300400c001036402c4e20300d000440d0512404580a801c010b642000007200e0600717207002c03800c1ca100d95000d8655504078040442000d0603020340142c4c01e00744400d8400041c0d40e0305d0f6040d07800380105a402c5410400208a051150740c01825180c0110300076201c10501e5a075010085030304065403281078500e8101209521103a0400c0072040130103012940096015110038000300386040340390f40c82a98016282d03d02084002d4004020110305809040680070090543d1141035681c032881e0280d0729400c203e60700309000c2c03250900a4130603969800c9401e0065003803a042c025950100341c5540702e01d004031140300046620302442122407182041600e280c0316880c5030200002082e0281c070075124451800300f03402c50940118152101550740c0c40c0c80040d204070510600400b0241c0c082d02505007001d500390712001a80c414038061505a000c0066640c0d040c1d0740713004a80b42d000d0502c4580000c0d0003c03c0100f010aa281c0150148000c0052a0140e0031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 367913255 1250 367912005 367912019
    0x309261b030720040603020402120a050105100206010e060f0303132301021513050604050d03050f06030c0f011101060f031205090d060b06040b1204120207060e01030f0608060c0a0207 80
    0x2c031400400a0614100101c000258a80414640c10103c0c000b000081e82ca95250040b40503039000ea000510f0760411002000201040c5103d8a8054582a11294501580700b131001e90b40d040103000320ac08104101c0300113881e954845010301507035000582500d45503480052180c034107030514000d422415a00302244440c09100d040c1101d5850016030052020002c0381841144423071019050703800e82a001520071020030410041300780141e00c41d8000703101c683c400003402421541d024041d03c80c030b0725849092100d10b980c0011b110602220440b40314564002d1307180181c030b01d1508541300c000c81c0e508040e00056030840c40c0d030110b17003180c0c055000420041c8000000b2181c40c420b240406601c15042c2c180603000c641154070100d0801005040103161945424940c242504140c51650103c030348802000100072040c100d080b00e5508900003401040d04000b0f024006000c000740113410190b03035020310702141c1d0894208000400402081e21940e080c240701410241d071120304410050b2040e18030000c1c1c1c075 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 367914505 1250 367913255 367913257
    0x60c0e0a050603070c11040209040e0708060601090f090216060f0e0f070f0e04060204030219061b0c0b0c07030c0e04051e030301060e0d060c050d0605040902030606010309261b03 78
    0x2c40d84c65446420071012a515040703032000310140700f9041a401c4c000b1355441d40310b900c05d00801740f00b00b000500c0c4036032900300701b5454480000d0000f81041000c10701000301000300c0141c1c10950b92000c4000d03072200c2ca07030329901c0548502c0102c003501d070700c0c10007881d0341091602d54009151800081c00750740011051203040d039910b09242c862219510320410b01005044503200140d5005841402c3c05403030543c3c3c80e000200d106802010b0304400d00c054200410078582c1016a10588000740d480390f04100c04e442e01c49000e203030740c18840d1038191070000681c0080c40c1c0f01071281030301031684084128500c941b244850358203450110380480340303071248400c2d13001c40c0fa03064141c2800c000341900c000c42c0b45a007003d404451900304240c400e50080542500180015034600856600d0300c05a42c4098480f00101c05400030742d0313419800035010743c4c90808110003584000c2003150780800d0a003404142e6005038501080c15070070600204201011840d801001c2d02018001016103a40d80b080700102e44220708040390726 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 367915755 1250 367914505 367914511
    0x300e0f0901030b04022101020a0e030a0f0305030a0207020915030105071e12090503190e120a0b0c040e0c0304111c060c091a0903190314090d060c0e0a050603 69
    0x1001114000400c00681c0d81d000c00c0740d004d0320250500321900e80d180c0100c400c01d01c040c2c07a0203500d03940118031740740680e5001c800740c100003204800030401f0032400e803101241d9140c039041c090104100040003410781d40d6250100d4014a501070418005032420041d134858030f4001441c1e040c4694203000100312005d2241c11403c05410203c21003042e00c0c41504425103030f0b5000c545511a1003070300c1e01000f0001c51000c0c006015450f50b84100d07140800c07aa02d20081544060318602c0d80306903140ca080d0a800380002030800c3d0b205a100808603034a80b07a2100808841c002ca51048141501403420000c0b5445035402840c00f4503c544910901e80e10810200411070080208004c0950008a900d101180380c98010186c2403040e0304100b64040d8440c00024081200c3c1e80c1c0d91040c0c484002080c0d4064203040085600d406031644403180034542c15900141150a0045001c100d8140443e01d40b000b82e540007a09035900351b10131010403449020f0913000e0f01083c4490380742403180c05150703000a4941411030440744 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 367917005 1250 367915755 367915759
    0x10905010806131505151f050f1b07060203250201080a0c1101060b09030708160612110403030e04050a050903401e150507300e0f 57
    0x2590740e498074a408202c0d544844191100007203e03600490744410b604c115400303500c107800306c1d0429640c24004d0264024408001c544640d8251404035034041e03000e0300342c4010101d00d1100f640c1d10440d1000003041480505c8001406014480c00060035903000001000c02c0b0302130f0807400c441c0c1c0c5050781500f082040880310180c00704201c08006040042180e10090541c6841d08000e400390600c20b40d1982102c100307401800c2c107442c00003000c0a01b07207030802c02d10000f005000e0040082d20802d4145015916440c4141c0051002000309441403c0d00c1e900155045200b103800e094a907541c900f0010700301d8140e82003407406940f4100c007240e060015401107900c1060084003d5142625444040e01c0031031240740d80b02070102005407080c82441707110302c2160500e0107004800314100d04022198945040c494920f03204805541b50030091140c8444080b1020101420038586480003801c110228203443d4401080b018204614410f40c48424158000100c48540c1c2e000303000d48a0406205020451524403a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 367918255 1250 367917005 367917013
    0x609050d020f0d05010e0c030f0303160f02070b0a0302040603110304170f0c07030503070201031b080a052701060e13020a05100c050a110306070801270b0a080606090109050108 77
    0x401604006541030162000600701c00c007401d0319516a05c0c211445c01c0c121101a42040c0e070380521618040100f10742000c4540d010354a50b090034101058140c0d03070007001d04144034864105400703680c000e000d020010014100c11599036900c1141c000c000354000c0c05200046890100940c1800c0b410b02c3c142c0c3d06c03403580094005142014400318545e990040d02540090000030414200146400d0002500641c81031004584800e01c5100150070340342c112014054180c503410242c41c0d00b95010032900e40080380b4110015464407405414800f100c0e001403200c1042c81046507090304000154040c40031101c81c83c0494000742c540c03402d9008031440c0313903001035031002c80c00806110500d0100c4508240f2491814406025652503440c0d44c1801e103d50030a031075000d04c3e40d680c50100c2c141800401c2e03208403640742035000e0390304160840904d4210240001c2610010003141c0900090f84e42c031480c40d40d0801002000e102c1e40d55031141b550386404507032080c0159245000003500003501d01030760b81a03502150140c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 367919505 1250 367918255 367918279
    0x71205040506070e0406080102041d0c0304030c030f03181b17030403030302130305160f050102070e22081614121204082b050f04030504050d02011115060a060905 71
    0x2c440c07035084c19a41c41c0d400b03a6107520001d4540c5092004000405007220031450440b00340b0709120701500300803d07440c0340e00010410080000d6014032004842507041c104030b60040000038003203009107034080d49031666074000b550030024405115903000729208113045004140f61900162400412003052854903a40b01b8401840040d00135005421921003242c0e5030003805075030780c5031f603403600e0000c40c06554282404501401140d034a001507101400b002e0008001d41460034491141442c0c008140c20017200d00c4010780c0e04035a01d0b207000c039401305420107407107030715840400650b0360007219450080320001c2c045164040c99141c0400c030a13208020007000d0a0400003030b01034818800c00700030b0044074003903c10002008c2c0c0901032403035461080003440044500100c002d406404a910151107800d08a16000400000a61040c21074080e18001c0e549190300c4a218401a41c408804402001d03440c0907031440500d02c14800c8003014480c010407900030082a9a5200c1174500c50054010250011503440700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 367920755 1250 367919505 367919507
    0x30510151208070501020f0c1209030d05090f100806030f06150d031707020a0201080703092f090906041b29090d03020c030105060402040b092704060507120504050607 73
    0xc10000798000d101103440e01034280e454600f244c0c00144143c40e22200030400c60540001040740c003047e41c184181d264601809100000e81e0360034404075840800000141e55061519081c0528141c3e03000038280004600124001030004a800c48803140a8401c214401c0003100000072404d004003681401f02c0c0410751094144000702e140d0004c02e8042c005c883c808030303080301d14483d403051080006501900c0d0907074213817000501c0310310060002c0041500380f05602011503041d5a07503145500b04070800a400c903141400758406146010745190344944104100204174001040f0305100f68802c0b0005a04a0f0348804040b014050900810700107403502c54202d44441003154842580031008038013182031444040016440c080071000480060700507803424034260409000d8030360803100444095042c90b040c1400703030a503405a070420781d11941c40c0c071030381e0300f00450909035406001145114030040341c542414614081c03d400d4441d60002004089140c11100b4513100340d900440d4040c01070300b41a10340d010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 367922005 1250 367920755 367920779
    0x12070204090203150405210405091321080103151b050d0929010b0a1d1c080a0206240d0c09020c0c040605030304120b1f0f03051015 58
    0x400326003512a002c04450484c2c0718841c0c081c03259101c4e038000d060b0701a60300c0300050741149407114124440304c1400180f100d40c0c0ca2102843c5e100c02c02e1405404245c1b0982403e107040c1c02601ca1240d03001484d12002c00d5503e52100d5214140da01440300404250070451601e02140c001c0f10355803608138007040d03142c3d403414428030003482c4080420001046286450712040340740c030000d405805460001c4041500c59101d103100282c01400c20540d4103003000174207400036021800ca0030080400b001000780c001455070f03901c0b20014284c1e43c3e403408102c500c0b405d45410b12a035840034003207074098441c02001400300801c00b0340d0782c60104901e08000900703405000c10310500382d00142d42210000700782c4001040010180c80500361200e0400020310405010034180011140103412890007500100024008409086180c0c0459940841c0c044072540e107600b0301190001c0110b0300ba903010301c0c0741c4200160012034400480c0c141ca0080e8250744414074503040201c2221003080800101d10301000b420401b07031720031071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 367923255 1250 367922005 367922021
    0xd060b1602090c130e040209100f15110f0304030c0b09060d0b040b0909010609061a0f0f040b04061706180403050a030e031b0c060f0405040c03090209040c090e12070204 74
    0x1100a414084103080000034013189401c680c042d010600104030540c948281e605030441c811910114441303051110b100c040030307607602078031882400c45408110f0760f82c0b1510b080d01503040150195041e401c00d291065442e43d100784010b4a00440e40003002c220300da0490200d90013110f0040c4080d152807414000e40300138000d00e8018503401039840c1b0a0700c989855080f0007501c9680e9910000a4550901070804110741854120ba2210b003200303040c2d05084e240040c1121060b2b0340c0c54004545690040d028080309102d0340e0810000610041000944150066102407503209803e1886070b1503542d000601803a058203003d46c0501784014008200800e02501c01840703e0400d525003c21109060100c29145520415a442d5035980c41c170311909004000380716007000141c04071180f0745032072590505588103004038003e0b58400ca03a5101c0d02030290f80690f01c81300d5881e60180c14180d0303e00d400d0416421120482c482e204a02c0e041500964481c5408201e680d00c28100c0d08601e400e056098092000605d08a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 367924505 1250 367923255 367923271
    0xe0d021f11031302030d02011e02031503030706050412080705070f02060f222c06030c0a24090b16020a0509010305030c0c010801030b06330d060b160209 67
    0x14070221601518000001c40c0302e0031054034110308000c0c0354414586000410b16448086900d044600a401501d10020400c0001c40e080c002d0380b25140c40030301546c050200b500265141c44001000001c00c001e030b8104c680700b580125040721541c0b22001040c0c800c4001101d983c000600200708032400038080710300b811096400600f085080c8001508980f059a010028215840800e007080d000c2c0641c4800c0004080c5c0010401742c0c1400b0986441c002c0c100c444824040d440500f1440003c003203480030089098a142c0080c100711861703544108001071501c0480840125003244c88050300d8041c01502d50404a44945c40c0c00c1c1d01c1d000c6400706202c003038144280d040340d02c010036020018030b03a502c0d20b102030b0186004001a50b65104041402454121414030302d40c18050a800100082898071102c0d0354424801e42e8846580d10b808072a401103201d02e0146141a070404620406c800080b1401030818138241306000c02c07805444194001181c002c010000b40e54002e06120700d030050030100400743d004508 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 367925755 1250 367924505 367924511
    0x4020a0603020c101109040b060f070f060b03010c050408160f060e0d050102070311160f0e0c1605070f05010503100618030c0605070201080a18060b0d02090f0a0e0d021f 74
    0x26413000c034040ea4034459040003525004074250b07005d0b04e800d105600741d128085441c02e1901c5c005c031000d000f03a80200040030b4045060020f00105000142e0080e42286100500030004151400c00c0502243c00c42d00554031181b20b00510b400c2040320031031000b026544425040010705141c1f03201150580041c00c4015000101c00500c035000544c2400a014210312a890f442c14003400b2080c62450700c00042c2d00ca100d5054259070800040801c0e010b114256401c1d280c51000c19a10282900d4451141450461580140d604100c0c2440000b1a03d4002d581d20320030b44001c20340d5030f84011a0140825103035002d044209220810609010300e41c0c02e545428030003100781142c2e60343d44880e0720390f1945610440108000003510000c40d030384809819440b002c007900402610040042c2c121f880071007808024411569085d49508030350b514403101c106958010308103505443c007000c2010040c0b900f0f0314034889680c20042494003210001c640d00b2442c900e21390080180c0c0403203484c1c3c50303240d1840b252440483c079a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 367927005 1250 367925755 367925773
    0x31e0203120a170c070b060d17031b030a060e0106030b011e02070b030f19020f09010f09050d0501020c0c0108040f032303070e13050c0f0304050102090a03030f080f04020a0603020c 79
    0x40e40184462040c82e03541200da40714817031030400000c139080c020302c55403154a0801c0c05a001440b090f05461070040c1c1c0444042d05e80ea20800c011b560350301c01c044582d041040201c2000101c2c4502d810070000e450791451080c03200d998810040d801e41e200e419585001c0b805043c4510600f801c2004e1a4800d42000e2040310350b15030360b61549500a0344140c0f00000c03031002000800c1000a07480000314241483c5520442c9824607103030b4070720014010a0f007440c0c1040440030300d00c481180f00300800d001602000700200d55040491401d80e0007513104500c551154095450b548242e0341c050b5200d00e2003580c1015544101c085982e5044031000c2d41810400d5402c07610840e940317800710304a00610700c60b10180d140c0340b42440c1e42c0410404080c000110184209090000300b04004540308142c8e20641101e40c80e154880d151845c0039070180c001c117680c0c0351300b03e58001800001c0c1341d403000d011682400c00d9203588126031204640c4540c201d0007100c019411201451040100030712941c0100021102c520544110030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 367928255 1250 367927005 367927037
    0xd02120c0a26010308033102010801050a050901060c050a060501060c020f0d111908030307021e0604122d200f060103020f190609031e0203120a 63
    0x404180d40e1800d010350042521211150007441807803803070704920600c400351085036802000c040b805000040c607454000c800b103400c140290b02c1c82d120215040c4203030132142411010701d44841032040c0043e170029408000004007410540b1407413040e100041c080741c885078204002501d0b0a0003902c000c0383c5a01c07801c0780c1000403d80c03078070819010f0855a500c01695a020f0b0041050823000420014130404102d603030304000400311300d40c41c5200720051300e219104008046808644007100da10140444c000001085802079000c102c0420001c14218522220341d1414404c6d9a0382004540003442c021010401c2d201850089032035504bc07010060701c1b000e0207586140101122085030380c86d4404603207a11400e0b0020b031558403c0e113187d10b800000400075028190452607880a0600c806409078a4424800200d503c80907140c1e58000700a10244c42000c4c0c0d42c900050084000e4072046d00c548240b20007203842e040d1400d5004841c1b50b0014020402015255162040c43d400b21b02c181c8103100e18040710b14014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 367929505 1250 367928255 367928287
    0x7030b0f0103060c030e0714190f060206010f06170a0b060a0306080f150c0703020f0d2307080307030b2407050106050406030b1b0904090503090103110a0509060d02 72
    0x2458464020100e154514603080081d5001808214141403c0c45400640c03003600158003c01c0701d5105401100c00800d8102240344110100082e1b43c4201070040049034400090460204035441a42102c11030f03a40e0700c0d070354801c00c10079014104c0000c4d1011640400c2e500b85803503d5810101e41c1c0e0000481206003000111540e0040403941c0100b92141401c010b19801444020b1300c081c4a5806406695104149000940300081c403100c8922004186517090600c00c0004041d1080c00000302c072490030108001900d004109520003110b003801502d2400c4028485040d50384941c1c0c040303191802c60f00ea18500b500a0041c2200c4d190f0171940791780040188010103101090650b84d03503080c9a646c0c8525003000b509480a0b0382065004500301282000002c1582c05600d5001c1c2501c03541c0790480c207210f2551a1070707208501c41c0c0d039802030501c2020424440084020702c60104240c904000c40714030401240754500940508801144080c08603200a0034500014450007030b22071306c0185810180100c030762403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 367930755 1250 367929505 367929511
    0x3150f04020424080c0d0f09021206010f150f050c010b031b04050c040308040501050f09041e0e010c050a14160605090f0f030a030c030e0a0501020c0106060e0d030302030907030b 78
    0x9400d0302000943c040c3e842148410700842d101e8a041c41162a24a181200500c01d40500000c072a554403014640d40e1203035448140195402032003c102040306208842e61260b0038000c48800b0100311a0000f6101c030b40b01c03140b9240110a0b129000303282c050700d00544494100c2d40802800d5500c506000c0c00c036076014011084801000c2c1c0c00c00c907410040500f40812510000c120207043d000c200014800305507040c09803001c0342d000340707800d59540110100c0d04049000d0103145541050a09030503504214420104004103424880100000000c0e00300107800e8603404401c40b0013040080249034100c40c4a1038650300002e100e03c1d013962030311940200510180621040030750b042c5036a1024010070300801c0c05101c0da423410020050a80c0903c403010035403288205209042419640c1a200c03254601a8000e0050f03000d415054950300f403503c0c1800d5001c0e40c405507548095510341100420b030319026452800800e40040c00c95004050140d40030384c02940040c241c0880e0b403207007440000005208110f4144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 367932005 1250 367930755 367930769
    0x70528030b090d020c03030d1509060801020d050a14060f06070516080d18050f0d06050411100f09050d06141f061b0209071407030201090b0c0c0303150f040204 70
    0xc01494a0003140f03050245083c00761045400501070000070740e82c00400e940e10401070650010f0304034144138521082c0b20459001820301d84c101580094101c4040d0301030140c201140c03009006960794100c4843c02c98102d2540e101c110400742d40810b15500f00081c04081e24280079003903034039100060702d88501d0480b00c0b00c1000d0a00c03c131080140007180040c05005803140a6080000c000d0080e02001500ea04442c0107080c0540200e840b060307030a541d01e100d40030a654001c9810130071400c09050032401c0020034000603020304014448035007045d12a44000640b4441076586c251002d0500b8100403d029441c04241e865a40380d185c0c404001c80c6030503589000d1420160741366040101c007090b4940046075944084144010312002c16400d10503180c1840f510f42c0d04451284480c0c1c0c80b80c1003070f110b02007440c0c2070742c404070400709503070042580551141c031021b070113000440c01d144c0d9010050070b500d10507080020704d550410320114001120b000400c400380300e002030003441010901d002103800ca030404c0c1d0084c0c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 367933255 1250 367932005 367932023
    0x2010f0216110406060813020303040308121510020a0206090a09060e0108071e27020d0902041512030507060b030303280c0f0e0103110f090a0b0a0207052803 69
    0x1030104050b841c0c2c03036560102c040d42c06011040c034011026011a60040580c800f2008280c00841190340c10300403140510344c000c911684603807401d80406400d82049070020303d04800035100d42064603011031400900100c0d54005c003418403840c0c0c00c0c07002c0c91304603480c5141c02c5a65180c011807042803500035034001e4120000b4602c0703150315000c80c1c03601d440c3c1140d1001d0110140311052190584048450600355070756101c00208043c003d40c040c4c1200100d00b0080c5c000b50b40f02062513014a000c941100c42e800780200c80034031250328000324040e00221180300d40c0c41480c0ca40050740002034010b03400750405c90b009410000f4100480c801103419907004684036001d4003c401000407007060800c0081c501c040d508c070750402c0719a42400c005804140300d020140300380040e4940e0030003207a00c00c0d0006140c4603800c0903210788030500100060155006024094411094540b011030200038500545200c055182d00030114549040e050003003048010032103a18100d81c00b000d2074450003100c2c074003200441c840c001d24 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 367934505 1250 367933255 367933297
    0x903080712020d05130510110115090e120d0e0a05030301061e0c0201020d0815060408150f0f0105060f0f0c0601081b0a031b120302030307080a0603200102010f02 71
    0x303060090440f1036409200003808030800d1791041400560907190309403100c140c0e101001e00203a40111660404801039070030010001c0c40c6d0700446100740211420a0030a20203016000e02c10b035201d41c0401d44114a602082c050460080495042511040c0c23002081c0d8a10008980f211415030744240c02c01800300c1e60b048510f001030400d20401844200a80c030b000c0340400b81e0f030360000b503c43c2d601154150801c0b8464002c1b50043c80500c1540c03605440090070316985641e1210340740c0d1203440c80d28868500001010009a011182580591240d402c07440170b10120b07820001000171a0b04000d0306030451005c140314109100e0000700081103030542540003480c6961510741d00034940744000225a010b5036900809000303903120307010550181c90381700350540340f81112035560049000d0142c2c0f04601c445c4810606005141d004801180240c1c4507075591f0406503500c0d00d8002c180e07082480002e1041c1c140941c01020001800d01840c41444140b00100f00e038010030f8082d005a81001031181000c01150f081 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 367935755 1250 367934505 367934507
    0x60902010801050a0e0f04050c042a18170c0604090b030105060a12060f090b13030806040504020d0b040303060f17010b0d112107060305060102010e070b190903080712 73
    0x380d40c2c0142812075a01c10140d0400b4452001004040d20b5001c1210210010504200c0140001240c1d003201070800c1007002490f040d0fa1008100e420b5641e42d40c00304610498040d03600c201c00341080c0300002800f200c100c510340340ea4060210407a004d036401324000c104418200d691888010300007407150f03400108500c03001304101801c45a0140c02d081c0310319101002003080c03402c0c1001032134040e0740003000021603240740d0060b50050410740318000c00e40e400a0381040031034401074949480c43c5010742c1d00c14207182c3c0c480061104a403030540d806580441d101030a080006e5110118a40c403501c64a000f040351996520390298039020f540100201503092030400742005824894041b9172a412155401d99074035a45520020340c3c604650a0300940c1824250740c1c41e000104070340074400d100172003243c01036690344074010010142503600d02d00550030000e0700b900c0000001014004e64801040003854a02c0b555010814403400c0748001080c001c843d440003000c600f2201c00380c040360713003e030861104070416004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 367937005 1250 367935755 367935767
    0xc100c020d0905300706110d0f080f090f0a140c0906060403020d030219060501030b0c0702030706050a110a0804050405010605040f050603070c05100b2d0d03091206090201 75
    0x507118003040240c660400c03041c1c0d10419010024445074460781441c0100d44409198400d90080c0e80351130b0701c0781e52400144264000e004204204500043d40c10088400744101c42c1d8180c41245a400030f5034136004100e080c40c03041451500700b40950100c49400d08544c0043c0c0c10004101810b403107482d8540d0075a101c40c9030600c003203910f0030021502031034289003410000d4228061400068080e402d0099002c04160003008428040101580040003042030b074034010001e000c090100f01c40207142c020101e0036212008055410165004016140440c280721046800b1f030001c40d001c42c20002646404860f4520030b12580078800e001c2c410443c0c0e618140010720054810690243e000c0090403c801c01861407001c1180094450840722a9941d450300c410490340075506881c00b174414000d03036071182c400139940d6000c0406460b060b55514401410b40b0701c0480c800c4510f05600d0f00384c0e200ca5030380d003c45e450b01d0b0440c103003414407034100b5201654440002c1c5c00c40320300010040701c009581d81320500556030001c5d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 367938255 1250 367937005 367937023
    0x9150806040507090f0b0d0e060f040219081009110d0303050405011109010f03020c0102070206031305011109130506030f0a0c0e0a060506070206071416060806030601051807050c100c02 81
    0x1c280f01021a02d808011510781c1d18a2207070686c00c1c800464101540710701504402e0000b002d00040710400c4c10440c8001e003001d03105030740c128440c02601f03040404060005001c101110700340006046003401107080c6038060000c04804580e84a5140c080c20300c0c95580300030400c0454020340c3c001a01e450316160090844a14000482c00e004040c03200300030390382c1d010502e010309240c4c92401607250301c00966110301901689400940c0301c0404410416484c81a02840f000c9034001c00080c001c07103504070080300c110700c9035803070f010b8121180030110300540380140c22180c0c110340d028040ba001da8940d08515810400c0264040fa4015181e2104118000d001d070201c98000314820410400280342030005043c9100300d0b000203000b110003081c0e4105000082859940050b10b5900751480340c916074210b90400340030343c010100411b000e880030500f036040000da03560603034802420300907038082c7c3c400d01a010140700034944c00401c0000c1183d030705811028007850304281d042e400041050101075001a003400320314 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 367939505 1250 367938255 367938257
    0xc010b0910120311031c0902040b041e0911040c08071409090118021902010f060b04080703080c12040602010b010f030507021b0604030b0c0304021c120f09150806040507 74
    0x22418000000785582e51082203a160421010f00604004814158016030641e41e0a4907546440c100504246400181c081803007203808000e0f400300c2104220444080d00c501850b80000e02081d00d601e01d06503803100d00d056014100c690b40005c200c000042c00d85208404900c005010709060044190b08400c841c130900c044001042d0401103544080b5684980c144140d8212141e80c68400d8001c0c00a03030b04680c044c2d4140c00c2e02e450690100800030340070304010003012420070b18007080003850700380c60016502a5046900682140b6156841d255102e40203a0408401c60041003d071503040b0f040320000304000e04160b000402d00d03080860002d0010759016080b0b5040c58203010800200303d9000c1000044100c0194209644040c898045151409244c000500b4000c006080c021207840101c051840b8610849546100b41600c501c0015070010b0280000e0400920030800d083c118000c0c0d07041d403803203070180c6480040786980f40e2040304034140d00700420700460422401c1c4070143c1440d00550368000702d6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 367940755 1250 367939505 367939531
    0x305070e0103081206010c050604030f0e030106081c051614070b21180a0501060e15010807051804050109050714090a051314070807031401060c061a04020c010b09 71
    0x245031110340301032150fa801412203c1c4c0300300c0041c403941c1c000c02926140940000849840380f0342840e0180107800c1009000010541345010907110386014001e80050340d079100060404004800480700199040403968800c0c0712083c40346a60080400700b80d0240240144400c1d118411048192420b106403034100c04200402048205585040310b17510111401d011121903c0d5030391441e0300155040c04900500803940030b016000e5040c444150000e41c15030301e11040d02480e035215204880d136078007805000b0f1408500440001890640558040c040b920244142c400b03404080e840010200c5000341c000d2202c0c0c0b40e0783c0707040c019007a500010059102100c8203503a49030110742d0300010541c420502c00c03242300300550485c0c0100410144c0010248000071103c002090800c001c0c06011510300f100e114000901e46800d881c04030b1b0b513501d10315040b501503488803076124426460305000b03481c8003e0154002107070702d1158581521a4070050000c004000b000003059a84881003000d10341d0081e07ca4044001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 367942005 1250 367940755 367940759
    0x507030203060a0302060c0705040f062c070818010c1d180c0714030c0105091507090603092f011103040317090109030c0e1b131505090411040305070e01 67
    0x2200c1c4040f80c02d582d0112515a2204501d001b418900710a54100e11703009828032103800c005403800e8000001795141a09000c42c0300401d08005051144079298603944c0c90504008640128002d01c8060313045004008a0101810710702d1a2600b900c101d444e4400000350200400c4c0d02c6078907a000c2000309902c007141ca10043e909800c4052800c0e80003c0d0052500000c001500030401440080140c4044c1000054035150002503800500030f0030101c405203481e0003204002440c010850850501c2206142c440b51355560070700f00201c0050100700340c00ca40000302c10070240c58018040002a132502c9002240451800f210000149000c0440f2a418216807040c0018400204050300e100728149030090300c0c0c2d845840c6180102c4441d06a070344040c11085e00c050001c07072426004208544640c81c000e01c0c03480c02800d00a50180b26219980c0b5090000304078076010300c0305041d410b0f9601e00c4420181b60107400d08038424001005c030f90010202c00105040080c04204000041c000c0c48000e180314018189258 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 367943255 1250 367942005 367942009
    0x30903031d010207030b0c0702150a090e04080a080c210108070b07110409081c0614100807140417030306040608030406140309011407020313170d030f06050303070f06050703020306 79
    0xb900d07901005041b850003400148007416410155a046034004240540700c0984080103061680301e084104006201c0708400f01e4000c0014030098002d5620910340e41c9844543d01080340c002c60054060b580b40fa00811160801400c0301e0b2407502402c8010351203c080b94507104a203403a00110303500c62896001c05021100218000c00b900d1111840300b501c0125403601c0600c3c1144841c400e030b80758035058080d40a038080021388903501000642c2c468404a40b0b541d2401420011407240000d103071400138241100081000344100a290394560f05004402e041a4488240034400f030a580c04420a5500220030448180f81034043c0b50020030804000d9443c0c5400c1c010001d11800e090350a610001100002058143d00700f5400702028018040c0052000e081a5034001d4490303005000c50b002260307031040081004060045000c004902210082640d42c0c404007007900501035103100c2280741d5035100ca0005240c0c5050004040c218484c11044084d030281d85004405c03224051300301410035105100308503440e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 367944505 1250 367943255 367943263
    0x7121a12062404020405060a1d010804020a06120912020d09120803010509090f01020708040501083702070506130311060f010612090f030810050f0f01030e19030903031d0102 76
    0x40340d01240300c0403150040c1c02c00b04000e84241d0340100e0f0410400624206e00e0396000803c0304a105d250348420380f0401501c0011542c10b0000c2d900030b54490322100e410010706020301056090003010881c0412100c0b0b1a89500114507548504031000d600894070300040982d003c25040090400c00c64402541060350711008848e0105004080c06030b0003042c08945c2c1c2c8c000070441500090b400c4030081d55203608901d070101040e0030038070071170740801c0000d0089001c0b0140d0301c440e00c0003102c913090b9a00669400700c900c6869285e0494024803015401c00c4a400130400900c0050b1141d040405e15240309203981c0b030300805420351402c0e05c40380d82d004101481001841210014110b0b030b01c074a0b0101400c030031800308000070020b051000304100d18003c00e5104140d0401062441040120010040360ba62103003400740b01c64418507501d0f4411010070600a90750f00aa100020303603001d41c01211940c44015284100c091150f400c180c000c100e00c000c1c20020181c3c082015038511840181101c0c0d910030040020f0341d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 367945755 1250 367944505 367944541
    0xf0a271508041e02220b040b01050901020a081303020312190903051239120703140721030506040f140a050a1104030f02030f0613080307121a1206 64
    0x103a040a01008150343e10b42951703c4220a100c1441491808150800e100800740d04a456001c0c90403d8280c1c0010343c0200241d90501c601a00a4400c243d0665908555980220320381e0000c441003903000300243c0c8003005111083d407010034131995200000c04e20310591070040b10045003017160f00507013400061404030350041585050300e0115181d0382064a03150403078030300070101c010a545105401500070300b0700083c12100d03141c010a4030344544240319002841d204001014000c0355240038075807008030a950041c10f1090182c0000e505e0b00148900c5c4d8100e12604294000009480c2d90a00c1441c0c5802d01c1246000000c041c41081111005041d12071404c2006143c3d88000e41d85200040117a002a04441d00c0c0d1459482015591034031703441d109a0a6115500907802071280f094a44610f090028440d401101d00700c48102c9481c80355a150140350303000415071801c1203c803e8040b407800601d030044c00b114241e40b0030030001109030b990034440c0c15901025900c1240d0b0100f1f0510445038000003668803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 367947005 1250 367945755 367945793
    0x50702130e0a171204050a0b06030304150c1b06050d0b040504030c0b100915060207090e2a030106060801030506071418220903021902060f0a27150804 66
    0x83c81e0052005982100d01902c0b085903006400e40c0f04010400030f0100c0d40d101aa0312a941d651610784902d81415500d00840c082c0d091108000c0311002c034580d008541402109205000c86214401210f0510000044550040020038400f088200f4520001e02654144000c251410060307454580c070010846001a440508501d9144011038250140151031002230080c1401c144008442c181880041c03410510802e0014043d464000c10060f0050241210308188000204500380500c0c81e4440600c10080300c41902c250b403500c10035400d803805e000b404000d0085454000d904d61460800604040c00140303a02704002c008509042105076a2058411708140710341c0c3c3c01c405209401c0440d50b99140070003041d194900701e032040c400d40b40c0140c0000c61003610079401d030307091384000b4160802110715646000b580580c1c01d10401c3d00400d41d02003d00114030080c585031020702d1480360a880c0b0408132100c10802c81e00b14032814030199121402403554a1200e14041a80749441d456a0a4207040e6012040c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 367948255 1250 367947005 367947023
    0x31c050a0311071b15020a020306070e0a080708011b05070b071101090213020d180b0c07080417070302010206010b0a1704020325080120071101110d050702130e0a 71
    0x4500c10741c00d0781e5050340d01038060a80c114113805100321025003441240c01c2d0b00d440c6003607448070f20702c08907200c110160b000e401010700340c40b8494142c03050500d1078149900701c5151040001e04000030801200200652000013620403040403c52603801d800b07010000600c0400c00043c1c000401c0c0e610b00d0780d885692482c03c0c841c0c0d03805080340c0d5130143c145800040d510030b04c410304144600400c0e0740202100301c40300702c04000a8a0351509041850031651000d04140c00480001c2c511007440d00c014a91288155042e0b850070f80c83d40c1004c01034441c443d024400503440784100340215601009075902603c41d2040c16828800c10300e000402072142c616100c43c0d44010038003c60219101001740e01c2e00300b400981100d14030340c0d0650302085c039200e040c803498410b98202500039038104480d2040d024403103001a09239145c40c1d1030740ca44400c08e4410090160420606100d8190212030a20846403403d90a584842d40c2c0c1021b40100a0fa0640c0c24425840080c500030503490b0000b070000b82c0c1152140d2028070b031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 367949505 1250 367948255 367948271
    0x303070f02102909060607060209010302040e0f162c30010c0309030f180f1511010209280f0b0408150c030604110c1b031c050a03 57
    0x49003050340200741e510300c00d403d04160540048079400442101e401500d205016010341d0810801040c2050380c1068000004200200108006800800461760181800340ca015606c0e9119102a5822a141001150004c01348940c031607030724041444c420f140d80f8208032070154004900407828403001406a002040782e00b17001c1651030710744580720121551001240030000040400001e225501c841551035441c1c050381480c00d600a10a0b03c4074950103542c1e8200d0300f0700e0301005031003024048000d500b960590f61000252146090f9601010300b051610001034004400805000801030700383c0482143d0041c02007030010340f240385444084150000394a400702070314042c000201407250300103180d60001483c0c046904070100d0003d1040380e11301d034100c07040d4180e040c03442100b04e2019180a1044038041020030158500390b0040c40b21000e40c0e4151601c1c00581d544064078089907083c001030008040036072224149018440d10780c00480a01d00352103400610030700202144603c2c00e050050550315008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 367950755 1250 367949505 367949507
    0x1903020a0b07080601120618020c01021216032732010b0a120c09021b1603031709060a020a050d1d010c1110050915010608150a080303070f 61
    0x6500c0203030840da07004040c1c1000000140341800c1256914081140c1600c00800c80383c007846010101d40c4945080307004640c1d4500580041c1d48003a08a240d80c1d90240306c80200310180074105402010020018000c844080341c003c1d00b07541c6c0c55960402c0c0845800781381000d1562150000070101e502410314490424101c00c106801c0c001007841030090100700c40580800360741540542e9101504941150000341e80d09010b407000c01882d0030040c106151407404001c00700c074a4003c0d086141880803105641c1052440b50b07440e0068510318034000340349001c070410500d900902c014081c240686141e51301881c0010707015a0b0f071751340a000c44400b990b001803d08a080d1090b4107941404100b80c90a00142041441e09004600a130001c5102c0d5440d085000d40f21900480c8c1c1c0741e01034410100503004244034030701c00b0001010014450503250041500c1d080c01c224803000b403680644203079190341245061403092050390880114119000320003c2c0818003004000005481d8030203607e15110030749545140c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 367952005 1250 367950755 367950763
    0x20903060f0c04030b010b04061418044803020f03130f080f070318060c020d020a031e0b07030b060d0b120607051c110a0c0c081923190302 61
    0x40040c110b865980004547d000015004000710303802560740c41e91080e01503420058038030070043c9203190014030341c61202c02818030390011814031118501e0038004114828158001143c000782048140c600520810b4500d44c3c8011015154600da190031414040d82088a00880c030020b08121107401e12030820004229208107401e03459035100c00b0080e01d03030034842c003000300380d400409003280070031101015240001040300490045078240d07034500c036000c43c480d020b001c05a8101c08050303802000b080342c0400840c0960740107064a078800400501504107a003007042c80e645000d40194101410112075200503a120780944076a100480d50000d0001010b170000303943c10041400310703001402003a0030803202e07a810a000d0300c21040c203503458204c1c1c128003041881c2221032000e40750030510001d2004101442c40340c01d20642207446440d8015040b600e0f030800618011004240140c40b4403485500e10800408940c076040071140902c004c0c4004240441039925101d03090303801c0e244010000c50810038140700300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 367953255 1250 367952005 367952009
    0x11208040317030a0f1109100302040909030225030201120209030f0604030e0316080a03030c02030d020f1e07050a1515090e0c090c040b090d060f1e020903060f0c04 72
    0x103407041c0000d5001c0d0200d00d20075002107a460084c90702e000103541100b5424010f00003100d648064a905e01026441004990800200003508250313003400045000d8410f0720800e0a9503000760000c2c0b109101c0035400c0c60700390241007a042500114000100010703604212065804000c0c3c910241c0c5460342000841d1401458280400e11445032130103101c14140c2100ea0f60b25402da00380e003500d81585154045610b0b0300034034811148294092941c40300807070710070b610040d50a0810310541c0c0c41e00c600c28500c0d030240d070030900c0003a0300741750001000000e02094842840c51031061008080c00c0802e00d8851544464020784090102c410551850640a075a44d1009050140b6001881c0101d80c4031032a190041424003d03040386032251100c9414030380341c20541d00d440b811203040311614083c00c084840a40f60041984143c212440b020b0020002c3c8440c000c2c01018148403100058541084146200b0052240d13082c2c0a01032040041040640740400c0f030640c040082114070741261940854a46940300c1c0d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 367954505 1250 367953255 367953263
    0x9092d0708120d201b01050702030c03070b04030309051615080405030a0f0306050a170f1603110105070c080f01150b0d110c120318010203150906010c05010c0c0320060112080403 78
    0x45c501211900c0546000c101125100208a6591901402d0b6a240304040011080758014000b65001030350b000700da00d61081c800d00d8049407508107030ba280346c500074800ca036038444003c0e0840180004200c001c0c80800034011803134803210a04194440d0303516072040300404c0c401c015581d081c100c509400303600110f0042c80c0103499441d140350340c1ca05440d003124500c4081aa580144800d141100d1030001d43c0c01c3c034090104429a19440c61a641c0880c07044c0d200d1000c0e81808030520824020a0501d1800002420386502620f600031082c03008600b120843c540c0e02e0320344104502c0501007001c80c24203540440c0208040001c000b21035a064400901034500c0550035841842c140b051030711100d002450013840098001c6200c920440540e900303030300003110440020103c400c1409014500b0011b6207401c120181002000359005458060a403010b01d200c1c2404955041c2062040691042154210380100c0e000039038503120907503d058035800c061041000c5001c03800313040c10502051000b240d000b1540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 367955755 1250 367954505 367954507
    0x207050f2e0c0e0916090e041716020d120e0d08030a0b030a02030f1f0501050f0d030509100f090e011d1018090209061e09092d0708120d20 61
    0x4050785a0b17000400d103801050000301000000203030000b000c081a40503e9000041d501286005002e04005c2e03005400821b402560140c00c060141c3c0b1070a540c1ca00c510b002e4240b00d20b10354214400500f03400c1a0700c95050007410584040750200f805402540d42102410101249031841d1a00181c83d044008002a61502824040e0071b04440300050b1004c00110752a40555043d102d0a42002164024070425800810410440e03080f403600c20000318000d4800e081c11b90400f04078902181009162000c0384000c54a042201e801c0f060304165106c0007810807a4400700c480d81801004501080d0040c00b40c0c0c0f0b081c1114002c07880c2c0ca0300c03c118480241a2000e0f504810160303030a4044090f0901000680c007907a041d902241c847e082c0790340310f8094450140e11003800113100350140403072000b004000c4a50b60003206031169443c00e545c0d503800c59103032900020340480c40c841114a8200300c00780d03011120540c0507081d440c20803940c0c24250f5103000d461250004c0d0b40d040062140f00e139440b07040460315003000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 367957005 1250 367955755 367955761
    0x61508070f0e0f070c02061303060906060303110f1e0f0a030206060108011505160c09090b1e0f010e0c0f1b0708010b0a050d050106090207050f2e0c0e09 67
    0x8a9040200110b4059154660181c1c5500304100b500300004d5031600b00060b0540300c180c0150030400000c0c602420760000413404199030391900d20450300600c80031190152900d03410014964058508110340002801500741c0c4d105051607181e46200101c80e000301c03104800740c00c003c0610148142d140f9403070510241c4402d400c40380b03002902c0340e02c102c468a011962880c008034044044088110340617040d611074514103071954819608400307040004890507100c42c10003064a440354040c0100710340c86a45500b40d00d003002d090700aa5211381c0f0381d20302c088800c0201008008404081c40c1411121021030f1301c896030b1120340342090307070380b00300c0c8402d0444d03503400074450030380e0003403081541648520351059400080d2980702141c00d88091240301584800103000522903807904441041e405880307640009807071695081c40e07000780e030810803003903c00d40c10940790f1084025007402901c031104451003000c0c50302ca10320f050001c0011038014101000a64271a60a0f480c54082c100c500501403004141c48610300e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 367958255 1250 367957005 367957019
    0x130609020c030408300309010b030706020f01050a02030402030a02100c050321250f03140103051e0c010804031b020916090e1009020a180b090906030303070c06150807 73
    0x644284640c0d056880307034034181d00d032800401d060b144045c00b80400b00500f07400030301c800d010603400161449007595238407008004a55001c10a0341c2c01070240d9000750005c030340c0c4614100c2c2100d00c0203000c07290b2280104104401a54080b0300032070302c90b50403900741d5501200a8000c0381c10f000e030400010030741d01c400614140044402d034000412a03480044005180d503c086400d0071143d0141c2e41d0401c81c0d6070702c2c5e490110fa18041c0c14407c041400d945000039400e41080700000b0340020a0b44291803640285030640390703028102d0390080b600703480c41009242c03440981c0002015008002c0024007080b62020480ca0803a415080070407100ba00200200507034102085135805c40b034044240703c0040f50391200c0008644545440a0f8030944a0f00204007000f4030300f03200100650310102c000020801c4038082c2e94042030501038583c011b4100d845030b0b80e84232441c450511035042d0b405050b0600c00e9105004208000341d21035031840c0015444200860700000035010b00c0c0e814489c0e42c0028810780151000441c0203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 367959505 1250 367958255 367958257
    0x1f09051b0705160320060c101802030a080d0e0a212705191a0c2401060311040b1602040b101107060f050a1107050405090c01020c030303010f05130609020c03 69
    0x5c0c442090301c0a103010316880420849100710720b5a52200d420040d02910212495880005001c18240c02c140b07910209a000a0410200034411038180202041c40c68942c140c41c4103001a41d0107000090260031500d1300c0e401c40401c0100381c0317001034040340865020010b205001d100c0203400c6040b03500300040340e410500001904240600c40c050514410582c4501d0b15529003030044901000080c490581308849006d459481801000301c10700c140315a01034801c3c2c43d14402051038000750312951455040c00c41c01026100b50052007000c080c4140010b110075400b903c00c0310b0b440d040d000b4081100c214a88049009002d24134109030b030160042d116a040c154010903116041e174205419580d0554031880c0a40d200f04907142e05070300040301070054504040c003c21018541005080071105015900c40c0010150313101220010140d030404811301009507010080014040702c2100950305640c104400a010b0110500c01d45103e1960004003540c7c104055219502415031010150b60f200c44c040038007a80d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 367960755 1250 367959505 367959533
    0x921030609071404171c0206070212040e0105011d04020406181d040201051b070b042903070302070204021c0b101d10020c091f09051b07051603 63
    0x1616030000010b107481e2042c80d9900c2c0225440344800d041c00e040000140082e50100007008640c401c40c00d400213500c5030041c0000d0070300d03100c0e8001c042524011000a044c1910402400900c10050200740606502e40390307054191802880e103801d5184912103c41a00c0240380f20654100e8030020780070501c1c90340b0100b480260052004d030f0800580c0e03129422040c1290741c1428800382c00c03441011800540c400d00040c0840600740e00b040c20620784440d00f85003055100e0340302c1034100c0c500003820070040304021031035800c61424030032440b0551200c2041e45401d110040c03100080650020f03814085540780e078161419186074811451240c0a4208144018241052401e2160129001d41c0b00c0c802c3c42648894107100410303180341d0f100642c1c5024800c6026400d032001042d07000b0a03036070300b140e6182e82509070311581041040760401081c1f122000d100b01c9082c0c000c1c000c66030074030302004161851141c420050220f2038203015612041800c0440c2420350400d0f801c80404044940002404044001452 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 367962005 1250 367960755 367960759
    0xc010e0a030506151504120b0c0307021c14040810110c0a060209040905060708150a0b07170408060702030a09062606041e02030906010e040c0e09210306 67
    0x10542541000c2280104035484014010360140d00041c0e288103483c3d4003014001e2015111100940314045202d12a8200b90001c100309044170b0b040c6418860325612040d049152120a94a1420035400c001e4484040e40d80e0a08805d400c407401c22100ea03c18000c01d0031803d80300f80340c1c13a1540e44422000e5222100340e2128105681481c00900344088c9040c00c82d0599090f182c001d15513650341d0b80c1c491001c1e4000c61602c40d84141c0e110f00402c0410400e0081c0c3d8851303541030f034824885252110401c82c02c002c10450360750040f0b600c03042c14020b62001d0700c1120043c3d038104190310314a11120b1050314062085800041030b42c00f07400b0a20080d1034000010b042e4445130354541104068884404807207140030616814035000b10101c003040108601d40d012904807002400c0829a51016201d0400c1d00c40c00428200307101d27a0010800003c0601881081d001d00819441380e030b62420710fa1070707035000001140980892107280c040030964803d001c12124040a20000350303e6410500c3da0720700d0b03c09030803c031003440c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 367963255 1250 367962005 367962017
    0x1608161110020111181309030c06050901020406020c1903050a0f050d082e0305030a051201050a05010c08180a09050403081b04060f03090c08010510060806030a02040b1807020c01 78
    0x500d41074018010000c4241c00003070500c0c180b07140201020380c00810700d40c0340c5030001280d02e1041b00811082c042c0b00c481c64060740b5240c208880500e0420121070000744501c0399a44144420701029a02140c0340144a1007250b8100c001104070202000b440a00d9000500510810b84038004020950f8401c0407018010015a80d50340e1040b44140c5100b40304884c0310300b0485294510b02c1c0501405000003080d44102200c2d14070300c54603551100c1c5154801e41394000880c0d8040398510341c9140d80480355014203c00d488041c4141c0c0b0380f000203170078a650240d000348105008100d03807103152254005680c2000d001000c0100c90b50f582c0c00d44200070031080e2015000180c1c00400118038951005017120390035581d00c003051030a460040111101e2010400d640101034840040c0c0c0302007031911074008041c2098000010302400c11007000e0070210410b6100500340f02e490700411030160340100e000c100081d0107541c04034040000701d00060310080c58850201204844c5c8003807201a07035000800243c0141d080e02c1d02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 367964505 1250 367963255 367963279
    0x20703170f15060724020d0617070504051305010c0519021609050a060509011805060a0b0d2705010504020901060e06030c0903030403050a060504120504050616081611 73
    0x25200340004a0b07034039000c20949050101d65041840061a40074018030f02d019070954002010b4010100c4402e01d10307001070b004900c1c02c244602130700c43c100007070070041d04840151010f60242500c3c2c000901c5040d2247d50703100d00007522440403040011a5543c000001c0040c901900009003580d04250142d040a40030300c41240c810390300000d84c55460503841c455a0401910f4031030014080c0c140202410b105d00d44520300000c02d034a03462840c0b40a0f201585400440c0850002c00000302c54009050034403a03034000b4010805035405a044606202d04c4140101d55082200d50aa2a0f5410701e0740c1c03072801d0b4a8003003504090041c1903200c68001e030710807110704249980c0d0b03401c11218541400e500560128080020803140c9800d200208040c5101900362802c082d43c81d00d51604100d84e203981036581b5500c60040104002d0b07010026051011142001400d00b810000444e02e01d0140347d81c3c17003040d107402c90346d034105005040003a18101d00340b00703481c03407000d55251501c070302401c90140d010340c080c011581c0c170 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 367965755 1250 367964505 367964521
    0x50703200f150a140705030a0c031808040302030d02120403030507021c0f061b0f0305041a0702060109050c270102070306060f081005060f010f050d0f06170c01021b060d02070317 78
    0x9045c001c020b20f558290441e1110701c080c0000340929001482450355070007034880c4084807001d2485220740a54441600c40f413460040c0340c105010310751540c0c11034101e0403142819101200031b03a41540c0d014035000380ca80130644042004a603500103202c03010070031040300304104005814683da6061103020142b09aa5841404101e010f59482d0104c0100d00304010581c0382d54803941c000c030790190041c2e0031080c902c0800d03070150300c241e00c096692030010703006a401408055594043d040c0c001c4000c074103003450841c8a44028454400e1403580c254030684400f00300c5800d80c401c201c1080595045a400c000b8180c2c1d41d610350300c698034207201d0070840f4029800d000130031850510031030f4800d03a4041c01c0c200c1ca41c405070300115582100005420305004003480a031b03400070528841e20941c41e9400d000082c0755800d214450307020307042c0030040711040c0d44a4030312400c079a40d020908a1f00d400c8040880160014000000360700e500841381c4102111340701040110600d9403094502512590301422001207462b10a4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 367967005 1250 367965755 367965791
    0x50712021c0201050406050f040314060609010f08060103142b020d0201110306241602010e061e03131a01031b150807140705150601050703200f150a 65
    0x1d800ba000c5402070208011660084000f00000b084450440346483c1c1c582c2d685920882d0100381084560b4005801c0000906255070752502510901c0030304420149440c13101a541c002c14000101202d14400d0340c000d2142c0c00f080b004082c00c00c03100c4a0102c0d0103580c1d80c41e0490031b046000c030030014480d07031104000b4140188210020280010586441c42da43c001c01d1005041d500e13000e4080c1c201e284e000350842400320102800c944142c1c0e40200603011514000100381c031500c00e209a00c00d08082003c080503259030003403065100c08103000143c40b030b07680b03156101c00c03000130301c1c400307031006100d4988040c40e10300c0f05902d14142d07842446242c0e4440d12060702c000d02140d0f1030058204000c003688404a9550085a0141d4080d0140c641600941c0665000880a4200c10012101c903403040004000321104504282e0348000286070540c240798a64030018414454403800d40c10240400d98400d90742c240511001000c52442e00c11500c481c460b40800011052003102c502d218640b40c09403180c02d04003105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 367968255 1250 367967005 367967059
    0x4050a02150a0e1005070f060e06150d0204050901180804030c1a1204110a031202061f060305100504020c0607020c03010605130f0617071706061f02010905071202 71
    0xa0380d000c02401a00302845490008001300c0303401c0c030005002d04000a500c5044c00e65446214440104440e040b50420a10300140500b40034000f140340002100d00d030711003500c04c801017034045401044c1602e41c3e00c2044e0042080640c0060420400c034040810302110a005000701c0b8841c419011140780d440561559602d119014406204001c0020022112140d020650080d02034800052081c141c1400155502c0440d4012524044141401c0d0744154043c802e0036801041d81602c0c0e1003803e0444403c0300c000d1010300a020605980d039001c519010003403507005010349401b501c115a0350900c13501c510364900341101d401c801031042091138041410103008220444a01034094900e0308401100c0c6e00c09801186d00020060fa9600c0e40050342d49280d112203402010558050700b07a20b411b022540600c8410854007124640c082c00504c9507580b103041221008800140d0b45000ba5011000304030b01400100601404600c24140301007aa514255200d1411500c210b60794080b580301003044070f940c42d04103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 367969505 1250 367968255 367968257
    0xb0d0624052b05010e030d06060206100501120e0f0a0c2612030c090a15020c010e10050304020d0c0303091401030c0801090b06040803030a020a0809120405130b0904050a02150a 77
    0x940308800c8602a144042c50000b885a400030694000c2c800c812441c503041031010750400c50700c9180402c83c007030b010f0140a03000203021100c000160700707110000c3c0c00c4a0044102c13503584c0380d41d00c1202441c440e090107a003803101008010f4808030310660600360b0b0680306e42d0058084001400291803800c4044106c180e0040ca900005401003c03c01c1a24400580005000800001c41000800b940c3d030b0b61040040040c0000c24050f80300c281110b00c00a16242c40ca880d143d06000c10340901a01599421080038414640d42c507000760740e6601c07840850b0083e0011368008001d087c694102000f016000034900d030503a1510340b03851034101006001142501d2490001a02003094480103001244c0c59405c2107000d1900941b07858942030340c840100b451903004486c00300f102c950205440d03044951144485070401000d0008000310b419030b441004c0144200d1003140c1c0325803150303c006c50303035041e10b6002901c1c00e042c001e022688900c0c050a2243d112101000f080344a0f12507091440c000d0760100065030300c26041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 367970755 1250 367969505 367969549
    0x160803060a171b0a08060708152d0a121419111e060703050d060605040605191202190201150f0e040f06020a1e0206070c060b0d062405 59
    0x3c41c600c1c10f00003c00100819000812100081203c000401c103041c0604074590300d90713840d4074090000341803444c440400e0310b01c1110010314007035000d0f0b524500089011480250341e4030301c0c880f9000040b808001c65002e811150103810700c25080c00b180040c5028080c02c0310b000c1c0e0ba510000d0040c6001107a1001c0070052900003040107003045400c00b824500320020310b0b0840f509082c011100000e050f900003030400c80014200080021600c15103008000003010941402400c040c2003400c050660b0050b03e074241c1541101011001090b4402d88000da100c13120481c007107654119241c07000d032940381000d1018001d5030078070800345c443c010502010b0b02200d040708910210349043c144c210070340c60300203802540e02400b652070340008542c5500c020b00010889480d0106000402480d84110740340b591b1000e41590001010800340e00d40095980c000640e02980006030003410ba00000c018001d09580078180910341030031039200d405040440c440425041581081c110b03a076004100c61307034a000c1114058148 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 367972005 1250 367970755 367970773
    0x9150902030a0e03030c090103060b12220c03060f0506150906070201050c01140613020c031204020d1401021c0203060310050402030a12020d030c020c01020705120102160803060a17 79
    0x1206501440d001031032448049500f408010780d01d89950801d8801011084c0700081c00d5080c3e680501c00d80004050901500d8205102d81c034a800ca4098010310031789112485850704030030043e856901c400b440350300a940e0500191281001001812000e050754a00c600d000e000ca103803880c0c400002140c401d0072121061824071b104007881300b69040f03510100e040c40414400300038800e1081c058810070004c4040318420a1401c0010400d1140710001852292441041401c00400b030110417900c0079100154480308a0300d603440844d601d00740221004e40030504850201c03120381010f40040c4419064000114075a505640d2080b0403440242c640c00c0d85944044013440c0240380325040030380d20034001016079500681d01d0310340c040001c00d00c050b9440107030840a80729030313403540510400c0032a141910080c00c0540502d070000c0c0d0b0340c5c142802031900c18440d42d0040c000402c8d003501124018a8001041408542c051400d035507035400c03d803115407043c1c4c14001b0100f50300c0c084600f00040d00341404000c0035500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 367973255 1250 367972005 367972019
    0x9060e0f011103163c0609080c030d141005010c0b0a0e060c03011d040209070c02190f1a03060d030309020a24020606010807020a0213020c0109031101060915 69
    0x42001140c0b6007030100340700601e24608800300e01e00d91a13000310940c00140001074a060308500000c0c5810405009a1482012803600780c2110f019043c0d102000242e1456036090a2400d4022078000c040342c3d00c80015800d841c2141c58000c460b1601e050102c2149a4580c204d54003803d01450003040d000518218a1b400072801071607403143c001190050020303144004030155414000201c40c10008040300000400c02403011a0000e800d403000403061080d241050303030000f00c100d1406802101007110506006081d0354403d498042c455000d00c052030407117980d440030305175111b1203031088001c0201004034228815440204882c898007008101100840070303540e003a401070841e08026600010740503404903000100c2d60700305003240c101e030384107013110146200024644000140060b040040070070a020b0903c0e0001004c07150301d981200d440c0240c18881d13203403034024010601040e00560801107980e09058110b130541507880c500394000d2180ba41c6507060042aa20090501154038642c150200500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 367974505 1250 367973255 367973267
    0x109080322030602040f0303260103030e040b120f060606031006140909010303080a1503021507110405270d0210020a0c0c0b19080c0f03040c03081909060e0f01 70
    0x819100240c1c01c0c000c0d49a03201c071000c9030010b401c959880880c0d82030610906405c900310410807211585d95081c0c405c0714403940c0304410010300c0b0007410b0050001d104403032507a654102088200000e001c04101d451b8070404165140c030640301909041c02041c0105000c0c0c1800c1046905c0b83c10302c0d4003078100d0580f40c060b040710340e00003c081400145006105102480d03540c8040140210b0081c0d03600c0ca024103180810004a603a0b484d45043c6109542c1c00420050725186540c10300901c00c0152aa15501c0c00d013803000d180300040e040c1a40c03103071400042182002d585071001254907403244070f07105100704081060360340b4502501d040380540c0c0914049000b205841d002460461027902d000059402659540303601e440940e001031554407400304541c420354000c541240c2c0700c0c0030b2a00d000031450404001d0343c0590300c80e5004d064201080040000c00b4403d03c0b040a80055604c0400d840d0303100c400d0189000e420325115004000070304620740008000c4e120790b1900515540003825001c842045c02d00640786 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 367975755 1250 367974505 367974547
    0xf0c050622050a11090c07020a05060d0e0a06061e08070e0604020f0a091716030209130203030a0507060b04090302030904091b060e040e1203011e0b030c07030e01090803 74
    0x9a03912607001c603000a4014800c3c10301041c03050164a103401e00c54020015071150044c408030b6603035020301044c805a5501400b007070840348191400d5948880030b50000014102d01c03c880f80701c0307118903901c500400140d80c1c01603040720503107002c20700307010030b1a908580740110500c201e04132640452010f02503191103c11541c0c0003c00104010301e005917803141d01105401032a00100490440701080101c10303501c03010001c90b140703000040c00d61500c1c0b00310040b0f404c02d45400068042e110207400900c00143c0000c101c4000b070b400034200c0340c03510030110300180243e100271f10840f4018140003442d42c142c00c1c0b030b020b0081c0e07203035240e00618200072600083c80020070001d10255081d4000788014143d03c410742c0030b140050b2000e50f86500c11410000140000c1d00d81d141e100400e03a0303120504c2c0c0c041100b40d427015a41500d2900484000303511540340303228082c00c2a0781108020b040000140516a4590310040c4441c0340310b62551800e41c100c80006685101181c0301d90216900b0410010444807004420045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 367977005 1250 367975755 367975801
    0x21100609030506011503090228050603011805040f0804120615050a0b0a020717030c0f030906071511210603120f1b0a1202060c190807032306010f0c0506 67
    0x10207407c56000140701443c038503404498500401d480039100f01d0904554400b60005640492940d4908070518015441c1080d02480c45692003020800b001040e2084600301500140840d4032580c4945200c0100148000c0860f4540c2c5007502c5614210140004041251002803000d200b940c034029080082c0d50040c142041103005040c0f0108000c40d164442c1220b00559500860302d9020024140745080d004480c2c0c032100360f00500240282d0b507103950480e4107095019036001044a07910940c0005442042601120072502168410403800032000b080e4403948094030303400c070303544502e401d164440700c20721003000c0013000400080d880f0002c560001c110f85044481c5403c0003254a1014604100d806d440449941c10504a429011581000b800350011142c41c00b05140404000d903006070f43c000c03c032103842846004000260041c3c020745c4580300d200400034603406080317507035a0900c803032040403641240030480c091020340070f40b4822003d218045034004000c00058484010003c0c1d2051500c00c806 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 367978255 1250 367977005 367977011
    0x50d05060f070906020a03140714071e150f050403060c030504110904030c170c030301080a0b070f230c0d0f120204050d080717070501020c06010b0a021b040221100609030506011503 79
    0x340007500c10345602b0000d01085011300350540c01d01002c0c14540400001c0906081c1040c101403245100c40c4610f102c4494031818003020764844004165914083c541c8050111031400c1080c5180380d8043d0000c512035482154280c07000e08114007004105101a03a002d00060f14003002d02001542005415400503042845507040c100c2603800285140d200760072a50860300640e41035000c10501140c41a086409800c2009082c140c611000b0312050a1100412600d400e94100648580c0080c040303c0c01c46050360269002c1c102e1007600a800b0110300c0c00207000050100003543d24040041c0b00740c0b000d50354010481080343c0e019840d60308242e005118140e41103031110b04440590380c5508028043d481c0316400150300c50503551807042c00e08605900031540c220040010700a41a8049180240b5120f0950302c0c800c00701401c000f0038020701440924400c2000000d07003202c61000c0400071203124181100480c180306458000444600d50300d0b100040084c1d01030070050000c4001002c800d40c607402c543ca000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 367979505 1250 367978255 367978267
    0xc100f0c140a061a1507060b04020d0518070902090d11190e0103210c060917040803071401110403080f1e0702040e01050702030a0c030207050d05060f070906020a0314 73
    0xd2400c0c210141d000301c692996400040c410903800104007622111308440b10510200d08060f1806180308100000717101a5980c0c410f51860b070750360341c140c598424480c41c4c01c018034034218280300c07010000c110700010355200c0c2d0100000c0c070b000740e03000300c603428200034000c91079501c1c1e0703965401c8000c50015042940f1041c9201c1e002203403100c1d14102c400401061204407940e5156080607445000ba4039110440e500c08003807000316054012141002003540010b0000d070038080c904200d4242803407503c510b6514500020001816180000a00714450151014400c0c001d1102c060310300300d88c0e90031007010491606000410110b449100540342e8102c20164407440c1072001015030030300c04401c034201c00d01c82d400418050700750b041620980807203420600081201d414103030760207552800f94103c26030401c0004011001018400e1050740010301e0041d00c0d0f041c0b40e0916103401a214042164001c10403240c2800290b05141709141000860b81c1a4002d0000b41d6061b80742150741292030301c000700010700704003c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 367980755 1250 367979505 367979543
    0xc030f120315062703200a090207020105040b03150315070e090610050a140d09200a03060c0e060c030304032a03030b120f010e010b040905060a0507020c030f0f0c100f0c 74
    0x8101031b90800701d0f01c02e0991076426420404002c809401c1a290144144400380051b604170040310103648541d18845c1e1650340702e41000e810038101c00c41c003540501a1802022003c1e400300c00c2320780240081d0700eaa007401c0e5290010700c448124201ca0156208031a081c4040d0001c1c0900300a115150180c0741140000c50159010f041c15800700440c0402e05555601000510050301400d24000ca9010300f0071142c1070403080064494901804040d0681380d8446031040201e002c0c1c081c0d0260520050a4203403a440744805070398598008640035000b080344c1484a8154030800041c0c60382e2080990300240c051411030300c04070002c04030700030099081040490550b1304003a0030440180000c0709500041060140f047d030440c02e46010000d02401035080542d2400011004100300390b014240e0500002c80343d440c14400c80ca4040d814000c1ca815006250045048032000308088030007840312422100b079003550758140030950441c42c50780c100140300042ca0a10b00d5100c0c61003e20814011041c0040e4000c020364 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 367982005 1250 367980755 367980773
    0x7050a08070501120606020a03031121010e0606040503120309210307020f0f0d0804021503040f0b060618040c110d0f0201360c030f120315062703 64
    0x40400c00340e200760420462981d10401c1075441c1c00030300005103d090300e4520041e50b00c0c0c0114200070181341c0c444580c04804601a41640c07100b0242030031034400c43d5070394501408040341c01c0c0101081250020b0004029060403000c039021100041c0003400360300e04a100f220301540015200b20a42d000300f070310503c442c018400d003c08015518503072465981c1000e200192816982c24000407460300803040704107045401080600303140c41c89041c075a80035580c910000e00d01074540380400020940120034001801031a90400f0b1074a07100746444d030940d403180300800101d809400e4180e0b49805401500704035504050b00100504906401d100184c0301c0907119440c14103202000d45070015108400c4003c4150b0309008080d10480424558485c241401034015a80b6064051a000c0c800f80040f0710001c10641d000ba5034003d50304500c03058031080340c42c078000e0b0712030109040c030400003400d0101e8440b0480f07a41000d042110071544400320034150901c00129001035002504c02542c1c865040000820b610740 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 367983255 1250 367982005 367982009
    0xf090904060f1a1f020c120a030f0302030c0f071a070e0f0a032001180e01030b06011b120201090204020c0703020102062d270105060f030f030d0e07050a 67
    0x7401007814101c03140b8080444284440034014a03145541c0300c101902c510507011400f000d0fa0140120950301404140d2404225004594010800006102c0d0013100407403e000070a00caa03035130362174450700c0d40300c101d05074007050b149a0388116082000390464494140100f014030b10910705881382d4810075642c80713481501151f030034002c2519008242050314041940b1580c400c002c0340c100d1403040c00c0d9180c0140d06101c0080450840b80e00b4254030b0150782c0120080f00d81c0070f00c00304d00c080407180c8490a80c0c126a1081c8403c0707a2507013a00002c00c00c598000d506e400c9079180080440c880515a58642540c0d03085181a4801555a24110030002d0b850b140000c0c0207003600000209a428598400249000c80040c407941488a20740140d120b903041c1d42400f40c1090300b54428030681c0ea100c0004414588030b09a90708900d81480458900d040750040d00800c4c8100412078425452000381e00505841e100d209400800d1600108500e0303001d407440c1e90041c40b90841880803204965190008180800656 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 367984505 1250 367983255 367983263
    0x9011704030c0203070807060203160303151205010f0c02033c03160f080703050603031b010f06060e0a050d0f0b01060c1b060c020904020409060f0b151303080f090904 73
    0x52030304901075040c00c2000038000c0040100420905248c56002034403401a151101785016040025406141c440d400030b00e070526880d4900284680e550364880401d4100420450b0907509251406103d0903040c030032104070701041d4000c0c51501c00d988040c07001c010401a108403400c84989070340b00b8400088031114205441d120b010a80e2818444800c0c19540500d02c00d81e41040500091102d101d5486090613400c03294034200400c05071a4400042e0442c062001c492241203c0521071000410054200f182000101182000242c0d10703a84100ca0903450780244507003108618030100030b03c0c245040c0c01c54003e070050203111000c924642c0c5124114900380d01c0540010703148052070082c07250b4080c80c403a4040200b00342e0305049140540140241200803030191060380543c001a0075500c0c2c03900718440665004000f0001400030b1000303000102100440030b03002d041100050f010404810080340d40303201940303040303104052940e41d50900700d80c1311001c0c0a641483c01d010f200100d40310101e519000c2c40c40f03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 367985611 1106 367984505 367984517
    0x5250807080c030909070309020f03061023120303040c060903170a050c01092d0b010909020105040b210f130303020d0b03070f06140f0f0901170403 65
    0x2c1e4880c090342040f0117030b04200801d50b16620101d0f03280d02c222441c0401000c040185a9251002c58242c0810449407000f404204014009209a4203200440b4041f0152440100701c401c1c02c0da0000b04055800032007440108410100820080d1a49141034520f8078619101d03441445021901046070f808001032011070280320300c08035040341c18100000c0c000c5402900d0114404034500f5082041c01100d0a40d4032020203e1030399411600360804076032022a405c0485120040026000c12814000200000111400c2c50805400a1503241620903241d1400b001b20350b1450700f0040c0040b044000c10800c006000002d6004a1015a010b01d0010303220702c0041e041100078080c011040754540318030940054001e02c2000184203032600340e5600d0482c0100c403510912540245d601402100b001407007003020160701c42d409000c5440c014504011070008500d1540030b01502031318240d00081c2d0b = true := by decide +kernel

theorem cover : BRFrame.Cov 367805755 367985611 := by
  have h0 := BRFrame.cov_init 367805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 367805755 ≤ n) (h2 : n < 367985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
