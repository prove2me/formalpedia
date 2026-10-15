-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3923
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:04:14.974784+00:00
-- url     : https://prove2.me/submissions/445dd563-e9d4-484a-9e8f-3ad501ac75bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 705395683 ≤ n < 705575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 705396933 1250 705395683 705395689
    0x90d051b040b01030902090604090f020603090f07050406081e031e090a0f08071a1303030206240d02130207020414010e011d0412022806060f050117040309030213020306 74
    0x16000c02c80a043c1440c190400000d41c0b18203032020f9002006860004a0111506111000311000380303003390300150000030484464001f00e15081054080011501440d49580402c420364002d4042c50020754030481044508210342c0f4001e032000070408040d2494030803004c81c5003200f8429159900c2c200000060035a9003828890007500c01030801e1901d001404d0304060800d9150b501d50b2240e0b01c00412400c0402c20300c12542d20440b0f80d40a0011042ca60166480c54082c0d21240129001560303140d80c08101100032000243e402c0f0a040002d02075400121140c0c20811001c0d007036504940b140d642800560016101c500c503500c40781c000b034914507007151300d4007020410704001608030607851022000c0700310714400034a20141d0402c1e07200c00348203884030300214101e1030704414880c20500403150304408400801c4100311282d001d07004903028024140c03200c00c4040445098403410780000c410525200d0040100109641c10501c245440705420341c0d41d4000904458501804003245503002060024500d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 705398183 1250 705396933 705396941
    0x52e050627040e06010b1b10050402010305071821060c030204081b100c14060c1305030a0b040f080c031801030f230c0c150a06080303011a090d051b04 66
    0x41d8125800d01c000c00100c0c0059480e800188101c42400d0360110b19000e0b0b030404c401e8113041c5108050115100001c0c0d07400d144020340402c5c3d8041e8003092910010880c0e072440344803800c0d40b01401c42d0f405035206192200100c041c90b5030084040c0150080c40551001030014000d90008c0700d1595009a111070400c50350600704000e001d14040e2811006807007180a80b81d1313101030245180c5506042d0f21560850819000c2a201c4211401c140d01402c41040054042d002c00380c46156070b40f0030340603683c0fa11041032544e1030072810005028002864001000920b4005103802d040748a808440c2c140f0a80061a900d142c1090750050140071550a1081140d40c0c584034011154064900500c03a0800c0e0040380425145d03003020220518030008001000b41d0715041c11034001c00c60041c100d42d054500540054020002a00d070301c9143c600708007001032010300000030b0fa41a00d01030b20151010b0544001c85a82c140e1140c002c554102e88041f02000c040f82d4203000c10780310801100c4462412841c4603040000711 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 705399433 1250 705398183 705398257
    0x1020f011b110615040504021c05010c1404050102120f071e06050a11031305190b01031401050f1914011806150c031209061b0f03052e0506 61
    0x203500140070440903e008213204500345000307460010381d90300c40f070011503420004055040d44506821000d0020803005504c078007440c14242d42c1b14105240c41000d040c7c0303103108500c02e51b0700503444040d0f80c241c4c200107440105240d0f203042c040f0500e40f001c1596601220002e01a00c0ca59528400340c0c81c106119540c080d255002c46035050030090b0010041d141c001c20300010300100040e0074482d510b00200281000000350308000c0a10b210000c010600e05041090002d000072911001103c01070031507000d050113a47e0140007c0ca01c002100e42c2c1d00d10250692501d400d4440c0c000607180c2c0146402c00190500040c081c0507012101e01441904680f464140c500a5110704c1661075071954034090603520041107050542c0c5441e141d00b0282150410501920140d403003e8040ca140c088420034401010590b00340b10341403615030020403130907048241c08803842124203030005c1005800c50780c04d0b0041000d040c5000300a00140d6810306845401150301ca0b00300005404007400484243d00c4100d103005000c1281e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 705400683 1250 705399433 705399467
    0x12080f090d080412120e100b060301050f061804020d0c110d050a050c073b040c03060903030207050d0e0a05190e07120e0c100c02090f0601020f011b 65
    0x42200007008000e0305000f0b0014201c4030380015a610998810100c0c503c112090010a03c60a4000c68410303440c0c5402604034030b1020b1500380e4418680c1850300a481c104c2d0002840719119401d107900307000c00b69001d22807800310442c0385011003039582d4840c40500400c2c402c0190000344507407080301c06031001f611721940200c1c551288040b98103465001c02100c034072038060300d40765440b4904040e807645000c0c0c00b50030802400041880b00e189100c4841490000038a00274000d02c10301d4a2180c111034078401c20f0703070040c19442e01960b0500c082aa00e4200000041c4030740380043c5005007586403207007440c0700c0b140e12200081740c4800341116441c000c2c1c070b05800781c0307822500c2c0c0e40140d45c4403008101511061190482a2941a00064110340140d52031065520580014402e206060b04500d8032414401c401e41d1040c41101c00c007040c200e205882d0240101c1e4040c0c03c1458031344410701e0380c00000a00408041c1184660781c840186420280030701c2900f081d201e10b0305c1c1c103440d42284003c0c240c45104030781896 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 705401933 1250 705400683 705400693
    0xc080f011a03012c010605040908221503090c0b071a011715040201030b03030a03140109020c030a0305091906020405030705060c0d0e0d021f02010b22050a0912080f09 73
    0x602d801006480096041c051400400880307062134501c1d000d01820740c802648035113450020401d01414400411000f1700003680c6400740d40460b01a01030986c000c4c0207400350f1200413403107240d0150082d480711050b42d0040d0003443c0c0055980701624036641c0106030441d28040511440d8a040f0303104a030040c09003100c50000031541c1d4910301429511502c0740015000c0c02c50360f0012405690180c0d0062a810710b0240690fa0b80d440c1c08000500a84100b00c20305041d502d00d03000018101c000c910076501d001c03a604025510344511180c0c202c0c0541009403010640f4099140d980d240c01842a06148a45108200141c2c685141004160070702d0400da00c1540a51030411002000000200c0e485418400c03509100307003200c42050105c0e60000c4440b10084d0031401003004400c800203401124440d01010398020321154001c01c0030322102240f04064525482d4003120807442c2200c05410096112100c900300080480e440d444024010b54108548404141c11031b0900804c4041184495401018000200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 705403183 1250 705401933 705401951
    0xf08040f2103020d06091a0d1104050c03042001050403260a020a0c0e0402280e040c0e1305120d09082110050f040e0a061d160803160c080f011a0301 65
    0x1104008461f200c602c10f042c41400102040111461070000950141040045242c5102080801e602c1034400b90303456088450041008480d070002106000c1041e0342c1c03070382000e1a42d62407900402d12141803100405140b81460000e82c01c12001e0805680d20394020400410203003080d2200e031800d90020f441c3c051075001004096114086c80d1030aaa044050120180380c618191030105501038000300401030850040c4418402c00003a02e02c2502c0d08520052555215041d10989000c06000001c00740c2d00507000c0200e01d241c000b0040c0010341800e10021900c1842c03036980c031020781d010a00a045c0910389050b400941500801d415501c642c07080c800f420040d08140004800443e102c0c95203100d0307500c4a00c4000308460030301400300400e0340041c0c20300c008030210031054000d00c5a03034500c690300e10401c04104850712941c4034120860329608051407400340e4031018800b4155000f001a14001c504070300c00290f00c50308108400c011000c000001444409484000c000400b02c007000718401d170f050481d80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 705404433 1250 705403183 705403211
    0x130b031008031e0f401208160807031d04051e09150103080703081f030605041a10031502180910080303040b0906011d0a0f060b04060c120f08040f2103020d0609 70
    0x1b04400c560080d41003925440749a1000e0f0703040c0e41140005080b558085045810035400c406450244092685602c0c800f8030844d09010448030700702c82c44034481c0d001c010000d0b43d02d2a880c1005401101d00301c2903841c3e41404c000a041681000c2c0c1c001c0345ea01600251440a1552103c0c1d401c0c2c020200350244000c40c2c1070041202540200c5000240c01c569452010808002c120003c40b0400c0c0c0f09112511605e1518681213400d50900c0d2000b9100d00807041e03004007000c481031089540b0800b0580c4480e4004122600303001c03c000e001007003810702c500c40360000308054508202840c4110b200784d10800d41ca181128200b41031074810b03800141c4802c81e42b8241c41c000404d00007901c0c0d014141400004200003413404075400341090390700001d0791080005001c44c1c90b41c0c1c481425001180941c40600c2c0208176170b8030440b0784101c2455200d00003034010f001b180005440140c82c1c02160700900100c01140c107501803886000361410401f0002c694001101c80a0030b8103806164000c040c0400e08120780c0280341c0c06 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 705405683 1250 705404433 705404459
    0x70905010510030f0209092403160311150705160e06090106080702011b09061709060723030f07020f07060e1005130b031008031e0f40 59
    0x512418103465800c1d6501100c07503031703054440c007035002480c3c2c011f01d05003198103030703489040d90340c103254807840b0b00703043d600d0070b0800199040c02c184075852142e001e07600d1501c41007800e94a07118510351152b80c80456004001c5d00b80040c01019004502810405c0f1411811081540c92580305020a2160f80d080200315620000c0c41411906e85003444500750355a0f140417401090a4003040c8424040c000d8085c0609500480407804d40d02c2035128524080e0001c051003003180c2c0211041000750703100b900011840d0303120b07a45d528419600c41485071420b444481c114415600201d40348042130300d07a07c00300701403d5410040d0002c45d201c1000034015031401c02c0001004a0591110140585244001e08260601c603c0450380440b282002c1d9555540c0c603075243c00036552043c2c801009040305035030003054456000c0121004500b00044000b8110980d01040c609a0402000c00070480da05002c0c04807100200b4011000082006c40444800550b6410180301c880b206100581a843d44080a0102a0407111 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 705406933 1250 705405683 705405709
    0x19060206070804050a0b070201021c020f090d0215030906060a06050a02060a110c010204030501020a02010c02120a0c0804121a09072304091509020a090908070f020307080f06090709050105 82
    0x2c1c0200032503031141031440ca8804c1449004201c2c4545200b000000d88c1e041d03026008a83d0402800351007018524600380680c012007a103190303800803c0122503c02d1415030030040306107101030164040926104407000498104442c3c0281a820580811a5074a0401a4403000d0700a41c01c0c02420b080d50404001d60341c80d0020030821406035a00d00300d00c0c8000d60503041c0c41a201100009640d03940d2031303242050103034100c041080d0140d800d000c106c1d045580049032410381c038042e0303520950410801e10802c480360102000155414801040f01089500e9000d00042c0428018007238915000c00440504c03004240c014407101c0c0542000d0380c1440004955050810f081e01c3d2a48521404409400001d00410b1b81007030081960000319810150805282c000004540c02100c940e100702d80d6960200f8140c1d840140010708030042041030100080321007045807400b5002a0485d50700a0301d823042c0e41c0c64074882e070388042c5580c1d00c000200700300c1850030042000500003918090081e540341c1000b1444820500c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 705408183 1250 705406933 705406937
    0xd0503040b0a09230708060f010e0f0a0b04020c010218150d02090319050a0b0f0103080a1206210b0a02041d094305011e0e03060c091906020607 63
    0x414000c040c040a510800013040703050400200e0502035200465484049100d04001c1c1e0040c117001038902c03000031700014100d0701e5080d0003500540e0f0b2030400b082c85420080405055980d00c810070001d40c3c6851000d418045d4010000580e250400701326403601910408200380300d0a1544481501c5e5200042a603811406100001d070300c03080340170300190420b5000c80c03002e8603080382c80c0f41450500c84005502e00c292070041a8080c2d02d9183c842d1a1007400c2c800740005400c294040166a0039584104110780340202015070001b0305039103c0284800034004d540c4031100d403d0307845000c8070a00818800194011060b68011890189801001d41c040c50b000000781e4140c0000500248485000b88410b542c60399480702e00c6105184801d400d03446980d81580501c80400160314042041c901d030510744c2c0152141611b1b01070528103880540000311589041400400030350101c201619101005060b014003510f108807038a41d0102e00c14030900e51003000c1105405420320100b04185500450b17000e810003e18 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 705409433 1250 705408183 705408191
    0xa080c01030f0f05090a03110303060901170c031006090e0a0c0618030816030e090f040809010309140601150f140f0405030a1a0a060501050904020a0e060c0f0d0503040b0a 75
    0x10300c1041c0b0040c801115440415400c103004c020380110045814036465110383c5642c49240e1035240d00656a000071240e043c0c108e0003142c0184141461410f03211011340c8a4001c40e000e101906002c241005143c481c1e814586450300400e04c0b074200ba030302801d10901040d0004208201154544092640c202e204050a0003402e02c410130340e0380b100808410246400c140d038107681d8888805820300e00c00f603d000640c0000d01c441c41c80c640314074042124500034001840601f00c2a1503036201c020140c0c2c000503625050540d2a031814000030a800c2425540b5a83c0b1030142c401503252410b40000380f02e2400f0308104000c180344400420341e401051085050090740e000585900d0601003c0301d65115640016505209800e5041c04104200d481d01d1800704800600e4240d42e2a504414000c0e5121401194042941407005044908241c1e018111104d800d00e0311100c00146400850140d03484a0350420240c3c000f5083d07440810403c200005032100d052622a00d1464a511040c0c102100a0101891643c407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 705410683 1250 705409433 705409451
    0x30a0b041b0c020301060b210606090a03030e0a0e090718090b010305012406020309130b040603051c02070501050d1a030105010605040f0f03031b0618120e0a080c0103 73
    0x1158445031111000c102202200c16000e0340c05040300d400414103c2c4250701b4507101141241190056908003000d4429110040c0c1302050b25260000004004035005031007405400e0343c03035481d0b214010003075001e074452103204074121040c42003020280c0c0240b181e8903c001c0900c92007901c00101a800c030303082d1f50085000700c00400042c03400381c032210130050f0804c0401070000c4240038065100103c05010401e41d11140b507a00030081e20b02c40124403c007800342e00113010006160611b001c01024024550600103003c600300c90015080300c00e690401c1e502c5038000c060440641040c410301e0010703060300e80001c1c100289000c0c0020490310030448052551904d402c160206d107001050b504000c024018000d02c699a16000001d09a80151040545001907a500000e145c0703182800c49003038a0300b5555600303849000010001c001380407070604070307101c903a104400758000f4200d54011480e103126211112a0a0000e54010491129505164480d4129440030040c41c0400511040744001c01c1c01e0105200342 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 705411933 1250 705410683 705410689
    0x606040e09120301030b061002070501020709020a0e04051519030c05010c023d0c08030105090603070909060b010f110709230c040503070b46020607020c15030a0b 71
    0xb030007000203038940b10103c00401008807046040384100e034280c44503104900c0c990030403a0f4401040c42500d0141e00020018041d03083e0396001801c210000c2d080090501103940045000c488040724050b05043d505030f40d8001c0b510748940d404d501c150440d4500030500b400d6450300102e800b5948201818480e5408103441151100d1600a00702c140244501c032001c0240000c4151442601c0c01083c0584415070a07050620f02035421907515940003c0380c4d90450303080c9418000040d41c0680300c990300d4410780c03000241c40a420f004600ba540d115843c0401c184058000141180304401307003110a211102550704107044002986008583c20030002140e0b040d10b13000c581516081100c072001e03031803141a080010311a400c00c0100100c41c002e90449407800d81d5009204501d02035607000381078012001302e11000020182c9a40394141d440e51041100045210510602a41c0d400c5191400f6030005020403070b43c1a01032001e20a103c1e400c3c0d424840c484100c0d08a00303c9c4d44401800740281a6a4807208400c80e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 705413183 1250 705411933 705411943
    0x10b0f03130203030c0105061c050319020a02030d32070210050910090302130e060705090102100204030f02190501020307030302130e0414010b040c0516060902060d0e0c06030606040e09 81
    0x10340140030740341d4a103240d8034024040e0808403281c034000c05000441c0c044e5201c0391000c00d2049e40d0030078003950404a00f5590301c0034868142244c0d60462103000c0c105d60140e6420306c14284408216148d407a2000520301c070103181000050049030303000c207180702c1700c03101c002038030044030340700d40d4101c8140d05080d94214003610309014400310560400310b004d4100c060701c1d070804803560541b070088807a502407116189400d4150340301c000e100310003034000c800803900e018001c0c005080d2824050065607008402c01103034000b00e8100360b1041d98680c1300c0d08205001d5041c01c2c500924024130648517403c82c20f0904002035600d118500e0f0080c1010790000c0c0e40c0b2541001d411740e00340501400a400c3c40b59080c00e02703040c610454814469200d42d407070020704c4c02c05403500b0700c5060201c02a0b42c6078a400e01c1c0f0070315042ca90400000200351000c0d0745952130100165101c80c000c01c0706a01c6a00001440700007164035a1900d41e080f8552801800100180107580e075908050310201c1c1c00d052218010b80c7e462003a684c0c01c0c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 705414433 1250 705413183 705413221
    0x302130f06051b070602250801020d0902130e06060f120a0302010c09060c110108091615020f1209091015030902011b21020307050f03030703060608010b0f03 69
    0x140c060032004200c1951040041c40d506104202500c41900741d03622140c0c9415191013074001591001c031196880001104600713000783c01d034012913506269541012800c2e40d016009100d80c09035102c07030b15400c5241080024110700032410003044007400a4074400d41e00c800c00b414692283c0c5240880c04d61555440c0103501d01c2c49c2e000c0080d1303882c542e024a0080e010b0202c4503030b190041644003030003040c0d041c0314910b083c81c00768001c02e008108041460066502c000d000e042222140565003640c4100803400f40002c00504000c0108580c0b0b5006643c000d003800220301e500a9690480e0880c10600002c10007502c40504003141c0c0000b9580b00e190782880b81c0d2240b60300028040c24055400680550181e201e07c080074005c0e2282c034842c034050b03254620411b401d030000410b280052409000d54414500c08110150b819004691a040c0075440b92494028460028440380d8000410042600d525005840003401e00c1e0402c0c0304194100003d01c5a240103004010720611004000284990b101c05098680 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 705415683 1250 705414433 705414449
    0x10507090506180d0c03021f02030702010c020406170607031d060c0901020a1205040e0c03190903020c0a091b030501060f05160606030b1b031306200307080115030212040201030213 79
    0x80400c40d151091035601703148400d92143c03c0309000c17002d0304221501d10381d010401c0c55003c0d5281800300d9005580d001424101030ba00030303582d140080349480c0203001c03000c180c000c3d2400511962034804402000d40b0030b208444814101d0484800148850025040b60083e0b001d00081352507a0681c00100c1c81c084541c1c1000d0990a680c142e01074111350048000d1042d5810f4840070401c5a4900241405506c81501c2e6004071145280051003104440da01510501e4401c3c410303580d0344048400000d0b00039400d0342181e107030341e0341d94100d58101c1692810b002c5040070550800740312942c50003034054a0b5130b66a1542c481402070010788040007007140124000041da000908114581e203904100448050459106480000c6a034201e4a90130f170100a692003080d20031081800b080c1316941d03910107400485440e00c1c002c00d20311441104101c00c1c00180d4854143ca0351030340401c0d0314180c0c04400b003a8043c0ca51006041c81081001038551120200a9020343c0a0030050303620488070052030003d00c440d41c0300003c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 705416933 1250 705415683 705415699
    0x1b0a0b0d020f16030e03210702130e01020d0b15030714090301020f120f0103111207180b100e06040611160f06031d030a0e061605061801050709050618 66
    0x24140482c00698640074025a19603000d034003204c00389950f60b0800d00000c0c7c0310401c0e5000d0302189404042c01001003501c05070040c184041490400b0060315203004c0f00800d240d4010501451800040c0300d00d0007400c50448000c400d003900407085c13801500c4081c101008000c0c8080101811240c060100c81e4400710150007196207000381c00d01c2c010183c104070312801000d0b10480108103244403204204c0d050744d1708107010300848002c5504011401d004010050b072240156140000c00300b0145610344a040509400032401e030705004c042142881c2e00c500a00e00303103c81881c810240e80c88070030a540c15607006040401703418000d26049413600a41c0e0240b2817103c080701001040a250050001007111419201400320300345051411007a40d00e039031101da10a500511070381a10b07c0c81503180c00c0d801500900034500d050140d01100c1c07072440c07000105031556885001404841c41240d868164401e50341e100810840c1413566006000c1e801a1240511405020810141a10700c1203050301c00c1d200014981d81c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 705418183 1250 705416933 705416947
    0x60405060d0b0c1b01020909180a20090f0114010810120c033e0414090f0d031b08150612060a09020c1504061407020a02031b0a0b0d020f 60
    0x21540c2c000c103551340c03141003078074081850101c1c14000c0e111b50143c010981c0301240d45544031100ca01d4408494442031b0710500051b000411840280720785d00356440150307403c0941d0600144510418090940c000200c0c00000400c040c610b5500e510070032130303000d18000d0807076110070205440ca030340190010f1100703100e100400c004118401d400c0e402141d21030700b00d120743c4444280003603203401c00da071300e94030350700c4018001c0100100b01401080c10303114002000020500504c9144806810b000c40317506c0c840d64040040c03000d690000700080a400e0b00780b40303014040d5910350504d41220917900f09011052054a00c0464090b50b81c2d10186d04041c0409010252110041003800c0b10680e0155030050241408900c0851000640c2c001c44603000084e000070b100c40c01165040c4000303410024001c2c3c820070b40ea0501006004500c4039140e0080700a64000c2094644900415007843c403d290310100045500c00410740c075072944c1030004101d8040c00340403600c40000c0c0204034040d1040001c0c18450000c009400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 705419433 1250 705418183 705418201
    0xc081911190e1f090504090c08011b080603070f030807020f0405070323270a08040b0d0f27060b030304030303151502060a02070206130b04061205040209060405060d0b 73
    0x918006903040722002001c1c0152010b0f510407060040203880010b110070000d00c09418a07420108003d4421981c5030385080e550709840e07013107600e4900c914441c01c8120041c5034450364000d0942d0340004084000c0c0420b58904001400f051107d0b1100400d81c001c04501e100540d656850601190b030717400381041c00540b43c1004020000c00400b080c001c0c90001c030068100f03000024a41441c1314840000d0000000d81c41040000d581d0010001c4001781e078416607650381c001950300c0001d00018004413040c03030b44503c1c0c0c010030304054400c14460400090329141703000301e440300200c0702202c1e210b118240d03040040540e030400c0405010800202c2c0c0e01840001400000c02da4540e00801c40400c003145000b41c0151600454000c6044146009005a00ca000480c5e0020071650050110350710003413010b4504640551680503002280c1c0c0102070030080428200640b5400c15002d24244c1150002001285083c0d80014510030002d45628000e5503140001441d9440ba080b034030030226000004074081d031a0101e01c3c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 705420683 1250 705419433 705419447
    0x6220f060b130e07080304030506071b05030c060f010918110621010306110f0a0e0a03390e0f070507020d0f0611030f06010c03031e0209040c08191119 66
    0x110300911130755400040130071010042d07c1c1582d40c0000038100701c6d280c20300100c40d120140341c02601c18240f00d0f03c1c0c6600248007000100402c2c4190b80107450b081c0303803508440050b04416801008140d040c02c10b2244080394200d0b004500c0d541c02622070031a1400d03800415028000e120071014400800d005180c040d400086005040f02d2280c8010f0001d803085403e0445140030708030b03681001d00d100340076840c030360b43c000c100341540100064103071906240d0b40c4e100d82d5404203241c120302ea400d500c15164240c0c481d12245449801039504000d2480307192034041c0010590030300412004c46502060007148001c0c0c400d00c01c403609144c0040c0592195080e42c00d00e2541984121030440d40c4500d481400c4c540e0a16423015644103400c540100450b0b940c400c1c0054800850805085040541d02c821016104410b1101044500980f6500681b1035005000340811a60082c015a05200a120800082c450000001c1145070200c90020842100b80325600400d406950701a01c03221240c0d010240c14541d0004c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 705421933 1250 705420683 705420701
    0xe030a05012702130509032701080601020c03071806030611040e060a030213091a1e1b0316110a0303020a080a0605030c1903050601060203090306220f060b13 69
    0x203802c00001e80005580102a060341030000d4200528480d22000c10140d907211691140c05e00301500d00d8804103861958181c0c0c0c130580c131900c0074103c0600301601c2c5e50b4420201a4043c1c4280001c1800c4600300c00000d503501c01a104050184807107001003201c1928075005000110f92004007408818007800720b11425420900800490b1030080c0e0000d0014074180c1484004c494000d03004015012030311341e810029020102c020740d8a06820820009a40c00c14844e80784a6a150189171504400c14180c1c4000e094014044041c2064500d0b001c2103541340c54000c503900302e4034004c00d000c02101d18140c10780b28009202c60b211407500841c0c602c9414181c054008100c1c0f1545030b66887d0199880160000840b042030240030741507441a84c00741c16a00f01f2107070840c01c4200d201070040c041a541da583c145414000d030001d40c01a000030030180d0850508020440c0c000d2101541b4159a804003c0200c42c4c0e84400c0750040c100c624040e010000b4050168032030b42d089003019162084bd0384070b40148101a0101803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 705423183 1250 705421933 705421961
    0x50708151f031e020a03140c010c0b131b0608010501030b0301020c0a0206090123070320150c0c0d03060609080309150c0313090504032c040c0e030a0501 67
    0x30300080c81000c010210107103034814096200101e2810340d107a909601100c00c020318400d0381480000741c0980d407071080c1c4100a6208601070b050405181d18001c2c06c00070700d480b8141c140700750565140001940f0340c18484c0c0c00702c600480001ca02220b428900395a107107882509560443d18174020440541c88a4850b040e21820380702401501c403080c090500b01d104500e0903034070300c0d000783c0c01c80070052404900410810704140b4010101030209507144c5241d5480340e0140e90b040400103554410160401b0249031800d0014009044244079418104e844125065241500752081000107011107428401c0c1d46101c000601100c20328405e100c0042d00034100d90040c2780108004420003e084980002142d404e484058043c91030102001c00f050300d150810080001140028001407550101c200301440082c4011700c00401d0904141c10050034480d40340ca10000c4020182c0c00c0101183c1041422000c40742e010f03100002c1604040c4070880b0035444000b80304e43c8c5406000340c00000e00a05401100301d0740282c0f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 705424433 1250 705423183 705423223
    0x3080a060509010302010c0615080327060309060106081308120708012c040c1205070906150c0807020a0306051602240403142101090e01051b16050708 66
    0x2035801c120302d0481c01d00c8020300044030020200002104d540000038444250480400f4032500e8820365030a680000003440002074031070f00310180c0d002c2d400c02c06034020482a01d04514504182650755103c8005006000c24003050034041103004a5004000c40c00a8115038003549580310300300c00c1c1e0100706050701c8650008151800104040502d0541e0014101d11039819810311485a500d4892841c801402a034401009400014004d00d860354030f420014071900107820700505145001040f1079240d084265071050008100c901a07170007210740132035a50401803160700c0d06100e10018440e49519040107000c241010700f40000340010f0f0301242c034802c10741d809456041c00f0138090640b0314003250301c2585802e03882030085808680111100c004024030700f15080c7c81c0c0003100300100701d210f0590f0209410240c0d003400400151580f0310482c0c00342103849000b401340f82054011803901003d40440b02c903494100044075154076810004c0d03100d940351b00c4801d449000e65102c41590720360340040306110b01c0d42c0392 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 705425683 1250 705424433 705424439
    0xe0105010f08151207090c0504050112090b040b04060b0406090518151812040f0f05030a0b1504060e0a020c0c0a08030a0c03030b1e121b06090d0f03080a06 68
    0x80042e588151180405012102040400c000003000d0100c00380046001d04140450809524003645810a02684855544901d071000051441d030f000a440c000300c43c1b41481800000e0405050540c016030009a4801079441d18109a4010003106182d039074414a45440010740e00344680140d40300344038001440d492490700600c10307926100c8403404039110000d1840010241070402450543c0c080c110400ca400000e00c200301c2240d1075010b030300030300f0341c503c403c080802c83c41c114081c144024010640150509a50035034400302c0004024010744040c0b80b480b0b0040784643c44940c418001002c56540c91440303401c0c800d9215000b5404ce04100d5801d00030701c0c0c41c241041c02e0a5000c0c00803113501000441c074000d54a501141c102d0f0f4122412003c05865810307281c0340e5559009144c03400071082c0d2002e41601d4070901040301788007010b40d1840309500158660410012000c20440c03035103105454142e0356183c4d0b40f000602c0b0400c5158018000d480c10f40001c814140d0044045210b2800c2c40c00400400752 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 705426933 1250 705425683 705425687
    0xb01030519050703060903050c060106030e2416030e0a03030f050108030309030d0b01090302040c050d060f060c020d080d050f1807051f0c02120d08010b0f07080f040506040e0105010f 80
    0x101c00e1001d00b181d030010790100001016644a4143e0b68042c0c81d240741005c503d4204582403000a910080c000f0340c55504c601c0070010144a003180c2a040c1a10200c182c190300201801140d000a03d0701070f81c0700b414503400308120301981144640450b2001550320040c5d003441c2c0035008006000c403022950f40342c0000412540343c00001c40f401000000c005500b4207682d070b40404007810a44008a0412202003400001a00c80e4000e43c0b404081c80e0303c9054840d40e58070302c00030849800760700094111111207010002c03180c21010f1000b400307805444c0380701103244030300308940d0034450416000c9200e481c05081000300e11044803e5400b54075090035400c018880503005580c4e0340464050550f0103c14084050840340001c41102101509410617180b110841d80009140d0300b48107640c0c5165400400743c806006134054441805004000455410080c103005425a41c0c0160321004081c1c1c03400180c5207100c0d100c5c51b002c1c0c070000c150040107940d4450f241e90036071580304420710616000c182c07042d902090f001c4c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 705428183 1250 705426933 705426973
    0x10e0f0a0c051309020d2315060d0f1406100f051c050c100833010305040314071b05040c080a151d1b070c062a0b010305 53
    0x141c1100c1c940c580325040804002d070f01000350410400d001d6503240781000685811080c541031a00480d10503003400d00b01d00700560301d000302403a04d5060ba00f101240c1c0c0b1605000743d890300c0d00030300207640070400100e0500d860300b10350405031806007051301030001036501c0d0200051409d110760f070343c1c5440c0420305548402c0c1d0320581c141405802d901c9010800c2c0030120102c0e4608130000640250704490031141c130f510228002c0130003120030b071000500703184c10000c840a1a0b803d052400c4002c00300c140320200540c4001030203151075607115040544800101c4c041c140700e2241d002e082d108010f002507603903a6600e403500e03880b0742501d108445422b0400c0009030780c0c03506100c3c012064180703454900c525500c40c60050000d01d02c4070014840b02c980c950002c100c2c0c00100c4400e900c2c00d040c52110141c0c504168120440c2c41000c41e0100d64522410005000010100b80d4104103e800604100c0c0120b00d401e21041e20700c9500f0400915002071540100c0180014032100904890054065410b6124108d503440085 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 705429433 1250 705428183 705428203
    0x601030c05010f0309060912230712110d0c02030d0e06030a0e011e050103060609091a0601170a0203100602010621170304050a05070b0a09030204050907080f010e0f 72
    0x519480500704265401440e11619800340c81c6800201001c060350303010201c0f81461803e5466410074030300011039a41021250100c1a58010241c0401417541d901401da4483d820008011a1000b00040c0910340107d4101d07840134016000c0e0381c00250801c0d40140303900c1030400c0503031103803140780f00004c06039005100744004400c4c050501861a90b03105a990080c09254000088541d6950216582000315440c4811105105540818103524509201c02510515004034a480d49028a9540040c1d0000010303044e46001e20240440c0340e60709070050701c01107560707001003100156a10170090b4418a0364000c40c415031401c1c4c0c6170f01903240ca40400724200c0e905405540311480c090001c60007120380811707021300a00d10441064142a21903900141c81d60402e5504403032682c00b218500c400c2000070700040d40548041100d03076007020701011008048088520029000755510340201d85246418440d40f0040c110810403101c1c8022041d5845000f41006410f40740d56024810080f040044082040343c50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 705430683 1250 705429433 705429443
    0x60a03030801141305190b09060307062006070e040e0d02060c071119061202180603040602070501091401060503070b041a0c0115030c0608041a1e10050a0503060103 72
    0x6603082200f401c0c1000790080f070340c84d03000f124440070f111030140c43d001c2e0501c52600d44c8841a0b0001e1030f41181d000f510306040c0e40c1b62084c440c11040100d41d0300c0004a00c0f0860301031f8a02285400b2a46100004441e003541d06000103000f00410044101d401c00740c000400a000c1d00d003000b000b0303096210280c4440604e6500401030b080b100c00309025046000141071701c43e009541d001030f01d415034000100020100076030b2181c200c40c5180104074a94006070540501480081d0943c6080c07182d6100c050350300c080b21899481b446011000c80c3c00e11265034180c601c0140c0c4003008011a2034103040c018114000110910100e41c20098041150700303012403100c1c211090a240b16050604101c1c0d182c1184d83d081d00c564041c40c0e4280800590140309001c1e07400f544040c90400802641141455031180400390000740034004d00c1001d0000042250030ba9480c0e42d9075840d0710308010b40303582c01185030b81d01480d06002d00c41044041484041400c26020000b140c03022110880c44554850605860308024400500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 705431933 1250 705430683 705430697
    0x20105070c030c2303120a0302040906080709140f01150903060f0506030106090b0904020402030604110a0903031e20120c070e060102190f02011418090903091c14030a020f0105060a0303 81
    0x30307001c469401400e1011f06c24180541090b4440100030211069640b00c060746a00c02001040a4042d1f4071501d103019402c0099403041d480d014140454245040c80340d880035203051012090703014820001c02000d503602c07810a1016984124065020b0601a68070910a519220000900940e1440b40c0000e03500043c091000a550f00c3c1c00300002500005d104039006619886096612003011000f020414619150038459504504000b00403e1016100d6a4440c1c100b01104152941040c0d0005c0000360000158030f40441000c1001d0030a418080780920506c408a0b43e245641c40200308407090310070b0616518090794442004990350050410a501406d84540100000c10b00340d0307610052941c0181003400528200001c1d03180d25034400003101d09118081500041c8914198980d6904182440000c5040210b040c3c00600c0020904803121842c61009c8005000c0000030380780b010b2491421020b4070340302c03212014082d448020307001c40711599500c0d00c1d0002e000e929003d0340c01010380b90550385400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 705433183 1250 705431933 705431953
    0x608040204150815130209012304090807060507020705060406050a260f1005100801060e01090b0f090a0f0b070b010b040f05090c07050a03020c010e0102011a01030207020105070c030c2303 82
    0x75010000392145c000100e85a00207009a101c10a00b81e000700030b208a00158411146943c400340185c0c000c40300c0c0724604100c05400800d6095056503a0103402580c00251601c3d8a1026482d0901c59030019420640101e00090030340c2c0c020029080f240e503181c0b54008000251180054042034501010110068000c01308d24592956034140c0e90091100c0d030110421511400016400c075541440107001410120060005c1e9600c01204010144282015030625050070302a03201c0d40110b500b90100d10901003070b4400700d940e0b40c504100003410141000d00c03440c1d071241042c074400d510840c0c0584114141b40c00000341890100c0c1110211403801550810f21801e1004001c88114090003044a140090100d0004900c050140007902846600140031020455001406107481d00520905692612100340c0c0000b031014500440c000c0300b4a401130b0b0b100c1191005803024040d1890203841360080b41c10120401040750ac902c07058505504038100003034030406000f0b4064030f483c80c03e540c05802c03003c484 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 705434433 1250 705433183 705433213
    0x190c092004060507170d0f0c03050402030d0e0a03020d05060103062405040203060409150c03050604140a150803070302060106020601090c021902040e0307061407181a0f030106080402041508 83
    0x34190107445607181702a503082810010341590807507400c080c0210f90f2070091002c075180324803820f0907103035150400748198a86500041e44038854440341105100070010852055900c03003a220015541c004e0110250382c84d03030b0410310364423002400122030310341c80c10b02c7c0c15501c17410925542410882c45a4068815824030040c44060b4102800310750b0040d440780300c0f82c07000601008604005089045002401c1d0501d6640102520340141880c0d025900d80003585904070150314159a0091400300003007000307892145181412a290752100c0c00d5408045a910105035010825074101e03841a13003212030302c2c0d88524a0904542c01c1420384030159000c40b0382070f4600c1040800180002c0e000800c0000c01240310513040741554042c40c402c42e03045590b5101d60605981c0c1c00d072400d410406500d84545220416954040d03811194003c44507084050030802070100610401c881d51644055140382c0c403540d450170301504048040c0c0d000c0b4400c81c24086403100c1550b1101259040740c4032000109103500002c03c81c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 705435683 1250 705434433 705434437
    0x4020a080106080d1d04020307020a060b01080606070221060403020319050a1e0c1401140c090306041502091c02031912030c020309040c0507021203071112190c0920040605 75
    0x80e54015088401c400c00c0f50b911b43c03004c0d42c443c1c1010b4001d4484a40c09281c034000705c884d01124036040c080c650051101c0b58640c4001d0303464555043d079940c0d090754040407104a070300c044404006098420b901c108401c140c2c1c04000750911400d4605540f8450045103402ea80c140035498003500080c801c00415052040b900000586039034050400420a03025500e8014843c000724006142e20b0391034915421982c3d0304140d030164030108861b011810b0540c61f0340040c2d210040500050540d50110744440004500e81d4101d40055000070130403440c4181800445022459114060f84240104554807540704010054501c0300341c1c1c001c240c0c4048603e440810341c003c1c0703610300f02081144003d1055115a0302c0c1c621400307600d05a1511156141c1d103c910421403400d854810080141d0424407a8400250300c004448609603012200d2907020301c1c0c0202e0941c42c11001801c021040b05a902482c0c043c4820502c004c816240c141c407041c400403004003130819103070381814091801020704000402c2580c1c42140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 705436933 1250 705435683 705435707
    0x40e0c03090c064032031e100e1b01210f0609051305120306060d0510050f04140103021c08030f09010c0f320403050604020a080106080d 60
    0x7400c108100c4403804413491400e0403580c1142c00c243c809900d10381944a41040c24024846880c41300c4178a510700300008000001a0445805480d041907140c140da44d041c01405c40d0340e580a0502000da50500020507a05c40e003060811454a00d0240c2c1181c00700e07400700b05c0032250313440d2820342c141d080c2c1107200466902010741816018540300c01c8807440d051280d0302036088082d400440200d450f508001100e07044810262038060890f010404040024030040b414101c6110341e802d00c44d80701d60b90100850b00f0391040c00d0b80e00030014038143c01c11205240d1145090b007610016644000324940c000207110464140005441d8081a00401000107207070000403a4280c0151101e00e03050b400c043d644148440e0825600e40400000c180d081000300c0303030244240c0c190710742e00d4a04500d101c4070000c00034200d0b4241e120300d8055140d0201c03c1360350382e440322691210070320020b82c24507903a10303607034240240c07110000d8408a104030070506000542d603505015880c00c5c1d41e9a403000c1c1c010500688415546070031224 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 705438183 1250 705436933 705436957
    0x30402100219050109061104060f0f09050406120b0c040b2703030c07080c010201090c050f030a05030307181d01060f020f0a0b010e0f09071701060e0705040e0c03090c06 74
    0x1507280480c440c6850b18080100307118000110f43d09a452800000b0384401d442c1d0901800c8040c00104a00d40c0d000c4410030b20403000d4204404003035040c01c3d00301e0b0240007580069070071508244002406035100e0080c0c002c401e0207150b040240e501d920554403102d00c1944222213490f40180300c0c0c1ca602010075039036802d1110003841803840014502001c2800e41c0c0044610300c6080d00290301c20010010188100303490341400344003c00011045645805003181e80d030043c280141802c0303040103d1501c04103e940903003900302003120b4592500840c0140520b11200003080d400074000c1d8001a5595640c03050143c000f894164020141c2c280f030340488900b84400110030852141c0014001c612009011454a56006a12016580d07050042842c4405005404040418124400c100003958041007410070354004200340b0701c01d0f012880416014219540040c1c990303115810a02c216942c000004104131900c03da000e0255560f01981a8214082222a80700d5900a100c080e105031500303400a00d190b8001c1c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 705439433 1250 705438183 705438193
    0x105070c0302250e01170f0604030206040605060f0301060b130617010e1003080a0305160807080711070b2208060408161401020c010c0e0d1a07090b160b0a0507050304021002 76
    0x8660b0646250720070ba128020070800544c0c81b210710407086c40040d0011803024020813050400760f4000703607600300080002e00110340c1e580202c1e24a98400a1030b02440314028001e005142d1501841c003107982c0100f038450340c0c81521000014135940500e0003810341005840b107010340c41c0e02c0e00e101180c504900a010210300c440350800400018504005020420559500000c56141c82000143c60740e40c40c6003101c0500c0446002c02407210360104603543d1003111071922403840390b541c0010300d01e0000e0542100e251158046006d015a80c1d40b4607280402c1c080c22448150f0007689d50110645a26003564054007081040085194240e4218043c00c04603110300525111340344461030b0542240c10443c000c441a035154110020003da100c084489100811200781007448070380c2d56940c15010480c5025031100381010001851140540c4415000749603420840b960782c09010440014043c040c0d404480f04c03c11070b80400c24600d02d603ca424400c40c91521028907644480e0204150003203007001000442c454 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 705440683 1250 705439433 705439439
    0x24030a0e07030f03050a020c040204081f110a02061f18020c0a0b15040f050105100e030a1a01060809060c0304030e0a051908010b181305190c080105070c030225 70
    0x1030940003c880d90081c0c4c0d85035226032034050000e041c00140c4124500c50b90051000380102c030008140d5a500c140e601c005903000e40045908107001e481c00110b070b0107010703102050280b04a500450140d1040741c07404c1c00c01c005003641038448075218250b401080c45030b052409014120302c01c10b81c01401800856001c44088004994034508110130881e512090341c1c03822000c0c1c2d2458207241c0a424480f544130881440b441d0b04150201c0c0d01c00e414000c80504000a1040008480d2018003000003915042075070208da884040502c91403a500030710844002803a50000968030400208003036010324504941d49203141c40da601c00b00c804c10040c0c944a90302c1034020600117155941c400e801616054040c02d4900428540310b41c50342117a00c5d0200b0140582090100c60442090000718194484044590031007284281c1c10642c1c9031409200310302030064804213012007800b40e00c1c0c40034400ca51000000b0701060340d810300708460100c101d90700100541e22034002c403100f400c121041c1050303c0d26034440180819607 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 705441933 1250 705440683 705440693
    0x41e050a0312180e060d0204060f0b190201060302090c0714060106030c1722170a03020d051510080a020f03040602040603051b1e040305060a050624030a0e0703 70
    0x410351048a102982140740d100c681c3d003148070380341c2005080c03c05454452070b1030000700f24201c0081c5010712400028024004558036503000e50007074044441c1295481c2c0e2610340802180d8414402c82e082000181c2c8012520791050242000ba0399002d012540c0d1078403a0800b541880d0030140049480f0008136040c00c0340031000b00400b50085c505c0e680e0100d4944188240078103c02d0200990020803010f860800c42c41d040894982004881000f4170990f070382da03050a0020000e090003140e02d41c0440c00142c00f20b030081d4560090f00045200c00000c1084e1788030718600b16452207540c1901608054600003407142c00303000345030040e032200d4156009854a040d2100071345081c0e10481e0f00300c80040e4081000d1110079458450f9560003590045407000c4c8076031101004440303020350501c40c54400c400c0d229025800100005a8000f1a8010100c440a00300740900c000076060403200c46015072184440f04180301ea4031014410024140c0707000700c1c42c42c1c44d5100600041c0c01245803420461040e1040000090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 705443183 1250 705441933 705441949
    0xf050d020d141509030a080f0a140a0204031b120b0601050c150f0a0b06030411150f0903060f0c2a0307142e0902150309030d0f0e03041e05 61
    0x1200480900038040480c040740e40403120141c03130044203a005002400c001900461071540140d030400044003969156100b640240040f1385004050350030703030801d000d03440c0d00c15000fa000b07036881141c06030002407210322000f6208046106202c14201c581c041035002c10340d881d404a401440c18500307a4a00481800240e14000400e04801b00c1e05011808020000703012800c01600005800014010101c031180025401c0c000030380003030b103202d14000c00a00d81d942c41070500c041d91132480640c10386400741c1c0703010802c40d81c018207a002d00a00558000035081e51419403c24803440084110320b090040c104d07103c0310503280c01c200d1112401d034448a8018005000c1024100c01885403c3d201c0496030941c0c1c07528144a28441c0e00060040750070404034010070314450700345401c040c101c00090480d41500000d1244188800b20f1502120000280318800b800400102902400c0c0542400aa00e2140000d01140d5000c154190b0540043c80244403115184c03100716981e06a81c11040c6210ba140c00c0019049 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 705444433 1250 705443183 705443213
    0x2060928061b17060904240f18051606020304230d0819020c03060f090c0a08070816142e0c0606060804032f07031a100f050d020d 57
    0x462a016070324002031000c03540a0381c0c421310588102c4841e0805c1c0c0d0702c1c080c0701c0103986400741c0010300202c0d240400070043e038001c0b007550380007000074041d0500c48d00032001459100002521036000c1d903e100c0e544040c104607030108991040d4025460a890003c404115036800382984035490001e61040c0c0069a0341e8003682d010314041d0350b00710750700c01a07075071301040078289104100155040140080305a40d008a46640c0c4810411040c5030565181410581000e8545c0001984030818840102d00c03810009407001c1514104011185880d0075842d403440340400c10300c1003031003050100000002a0034414500b0003098190142c42485503e41c2508030b000c000b50003680d00020b00040020b01c2403016a0040340018006070a104a032800c1545009054200d58001682990001d4003030600384c0115840079441410702805030360b13140381c0720b1134a2094041c03075180005c40d8600180c0820840c4822030341200890b81241d8401e08010303e0034081c40360000d0003c0059a104401403407402c085000c54003a10320b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 705445683 1250 705444433 705444437
    0x3608010b010905032116060e0c100e0906040b031504080325020c040c180f080c0909030703122a020d02010e030a1107090905070602060928061b 63
    0x10001528000401d560001c2d0700244c42070344802e0201c0303006400300c104110030b1466030042c0d9903504e00c4548000341100803800e00500c076034a841d4045101c410081804012001304980540b19240c14078421980c046a0100107648201c00c80003060b002c0c0b0b4590301c04000c0c1c42000e0107880389001e650300544c400b0102154190340c00d00c800000c008403181d41c6001c40c1d583c2220740e0000ca0710500600002599002100039050180d5a07400c40602c103a405190070071685600280200c4000341c503501c4c40c043c103054a104090721480380500c21100f6240088503544140d8100c40114180580341d1001c441014601448090095a0f040726800260310002180d400ca4440000d0000d8070300d000034000d190002c01c051a07000c5914100c0d2003e1500c0001c030403141307018000e00d418a940403011782031034142151680a085042c0c5040440e000300b20010881e8411101c2d20b409641c0160369244059498641b400000129424002e101c000003422140d180303e107460203078000080b040f29907490b0402c020004405640 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 705446933 1250 705445683 705445691
    0xe010b0406120903050706050603070b0a020c010e04110f0d060f03060903020606030c0f0f01031b090e0f01060c030302161401050109060f0f14030a0b010e060a0801020a360801 77
    0x201c42500025040000c02d07a4000810903a40035481c02000b50083c40300c0204a10740701c0c40402c5540e0360420188000d0100c01c00401c0d510151010065610720b065030301940421808990100e45d4503107441500b0172003203103500039450498214410011540207001e5184071030307590f4174042000c1d000246814055845903400064404960030080d2609000030115442603201c140c41d810981c4501600c013480b540e040d00c50450290f10480140d02070b000e00e0305503d082c1c8140f1501c1c2441c0a41c0301002c00c0803100c020500704003686036000c441303540d41c009000d03450201e4032070b41c2c0c04170001c1e10070b90081c948000f51b941038886800280e03030368a100c014945e02c0e00b8040da4689005101c417400510403003004041c010fa104860b18500100c170021204140f0420310b50042d06d24116406480070300821000980c45100d085196031100c140ca500d814042c0c3d60340740604cc90400104851300144210b4608a611b611904404001494840850310011200c0000407020400f400c5428201d084258090840040041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 705448183 1250 705446933 705446939
    0x2003030c0a120311190e1c06200a08040308070c0f0606140303091309060b060f033c04080c0a23030f0d0504030e06040303030b030c060307020c01180e010b04 69
    0xd0035183c0d004130310b060041c001c01c030001c0f84520079080441e0640060030300500300d202100000c0c100b201202c03060304040d81c958103200100551548040e004e03040c1035803059030780c034444400d1700f6450140000c0040421080750101e40400d00a00314a031740456549040c040d00d01c40c55594455003d035002c82180c55640710107040c024001314a080d805a04c07000c1e802503082881c04800aa40070800f07403a05800741d42e60389420800e00203540c100300074442d00505990f5848001307140614407503000700c8499a40202201030b08820f5000000c4d20503805200b400301595140c101082241000c0c1d02520417200004100b1000e025142c0a010740e491060041100c4000b881c3d0101a411042051503214984e5410810402014030503040680741c5858400e200001c0c6559145030590f47d404078000303c581e10a501040010030144e2581044c0100241030b001e03123100300008070611040340801d4407110056003028400380840d5104008000001c141d100f040c4400d1035407881e650b12680c601780c000060142c8001014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 705449433 1250 705448183 705448187
    0x50712030e040b0405090c09180d021b060304110603070309140c0301051312120b041107032d0c170406020a1e0b1920090a090204032003030c0a12 64
    0x743c1c3c290340300340c40038441d500d06404005d13201c165510905114543d0380c00803030104269051001484001d800803940d2403402c2090185d036171080e00e1071240c581140364850f908a41000029030f80036030780c040c42d00c11128556104011958000404510415540741c0711440443c488884030407250304c079200a40a2800440305050a554008014010030041d040400c800141480700300030b8a03901c5440c2c9418640600205000603041c10002c00760f10034200345140d110403d28200400296210343c131003000503581d10b50505260b43d6109034142c181c1d00700b446403000140c02403803d020703074901c514500c1ca180821428498102d8200780c00c0080180c1c400e0a50708100403030681d0b0320107000500002101d1000f641e82e078250400e00000c1880b0280700c0c55455040c80c0300c0e03a03034000145060300c07018514508052210f00d030030346410007000648256058140000c00d802a8400c80e42903a402a62500401d140031068081020844a90681611040003135142ca41d905001060310a4803c1e80110b05080481c900 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 705450683 1250 705449433 705449441
    0x706030203100f0b070f031707020102040e07032d1404050114070203070c03061104120614070c03090509040309050a080c0f040b090403080703110c031e03061804050712030e04 77
    0x300d141c1c401c010010a0013041104001d403211240c1c0944680510b01c085d02d01110086d0180065140f074400510503c050f80e40c040d0090429551000d030b410703400303070307030340b080c110240e4070810004408462850225114034025034002d8402985084021079403000b803104052055070708403001e071001d95403281d4804030303102d00f41d16864100d043c40c40250705124454450b10405081e0f4400204501e90710900025070281d81010f1b64020000e022560542d400c9a050100250144a1501c942d0707805000005510301d02607020307000c1003901565459065400c141c24401c00d400080c0054080c030107868000941956a181140003504100d40504812084007080c002c01c0450300080314400c0d410804501d078943c9483c100c0710b42c0590140b034000410386600e1816070060615114640103000c002400500d00032001005000007003040009816100010a600610740003d460441e400315040ca9089104000020526007250041c019280d81030754840c1c641d01125240c00088012505910301c110003850a486 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 705451933 1250 705450683 705450689
    0xc01140603120d0e0c06071209050312070318080d0903030f03090f12111608120f0f0315100f110a0201020c010f0507020d080301080709020a051812070603020310 71
    0x30040c0580ba48100382c50b0703008400c0c161154584d5070144901e440310801501004000c0540460303565400c5080c001ea41032a44034485003c618052000941424001010107405c130125900500309403180d03a04440700c1d21341c0020510014119400030506180501800c8040185d0351105a0018658038018040800c210300d840c0030700d07160907403480c0480d00b407031424503803190b000120000c601600b940c1950508001c00880c007841c8625108102c54000482d41d00d419a0014001c803400c040c50782c1141030580c4685110510050800c0c4400341d1100c0041c070255800c1444103102082e03507105240482c3c0100c024869070030002d4070400c402801d43d81c018030f0301a9000c050740087c01043c403132a00080c0d07a404808400c1030400070808815134a152180d0146c0c1c0b1902e5000f861040c0c015024103000549810030f0160484500545400090600741d61084940c15200b50b200c20342003120001001c0004c82e90140c4203500445a402c80800381d03c01400010040c082c140c500684a0800c42801441000e144e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 705453183 1250 705451933 705451939
    0x92e0c031808061b030106020304050d0f170a021002070203190c0e0c13051002061f170a0218040f11012109060e010b0f060d140a09110f1c05120c011406 67
    0x5c014015964003104860907540156200c2204901a103031a062800400350094920903002c01e0460703031440b1000c010916280154202c0f4012140c201c01d4a0407841030b03880081d81759000c80c690744020044103081101023130068609005503030382c920801d881c400080700e0b91300d0346410002d031071000c0c40e0b00082c1240c0545803d8400b44110a01100080c1d9111005852401d00f003920241e45070404023a820032001401d98022000b1224108072140740c0d6030501e19800700e00c40c4003084603511544403402c200030302c1942c0040180ca04a00b55071100c0d0b0340d62620404d041d0410043c030b00c0310601c10b00d00c1007991001142d620400030b031582c010f0034090f0498404004400059040484011150b920462296001e24044030446d50700c00348442618010700341c001c0c49111005203501040341030911a40034106040c041c40c452200f04801c1070400140c0128004007550065003180203c04032107404c0041418a4803500454180200b9200e161a40b134106010f910400da4407200c0300318070540101c0078190070860039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 705454433 1250 705453183 705453187
    0x5060f0f060105030f06040b040f0905011410090504030e120f0c12030a050c070302181b13060810032a080118080c01060b030c092e0c031808061b 64
    0x101c000800328800513000d0011800f925010980550f10b9520244100c3d900600402c0f200070b500040c00f01a01e0314510917510fa5203816400300038400d0760340001d03200310000711510b080d040c06e103581d0030003c110260094040002040c4003209a031180701c088030a00c90464018400c00805030840c2d0b20f000d0181003510701a6800740b00743c044405000040d201f41d80e08038280662903000e0455030754545010742e40082d52200703550805440c80e4030038044081c003403680b08403141ca00d000224a40c140a10400c1480c10020450030020441305109a0f80c1c580c05c25415605500d070995a61100700c3c1d9a660900c8244201044c2415078a15460f248410300003010500000e004054003a2020380072420039800103425284005170b1030804400a510510140040c0c44820740c43c0c2c00e05400180c03950b040b401e0040e0050301c55401080424500742c06c80c10340c0e0b140503442d428280114007822a820700c48104120300348501c500a9001070081e40e6410300141064100822851400711410016950410000140c066003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 705455683 1250 705454433 705454441
    0x102160914011a0f161509140c0a060e01120504080c0717060411010315081c1812051606030c0f030504050706030b1903140601150c06020f040b0d1505030d0903060b011b05060f0f 78
    0x3821040102f1034050f401d002000d9801080103a65032038060700c0c000c14051401d02007004210058001e405010a0001156031094542c040601c1c90075540d10100001d0b0b21000000e000582d081441c01001c20043c94041008202d00820518009580e00302c964550440c0043d194100c078904522040c505103803a00320074906800180041045090160f2010a00140000402d00404200c04d0180c16651000c2ca80c007255100c400400521400023110002703142240f0300b0451038424000e41d4001c54000014003011450620140c000308038410403190003101844014014002c400060801140102e0813045d4441400781c00b54145101608020010000c02a580407504d038060b1116507003d610440c01642ea9032003508240441c0120f9108882400c40020360306070703078002604440c071000c044600843d001e42d140d100301611031030358040c2400064a0000e0030400b04415402c04481c0701418188a4074104610b41d0740c4e440d51280e600103072550703030040051200556148114171352040d0300100003c09800c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 705456933 1250 705455683 705455689
    0x30a0c03061505150c0c1825051204051006030f020f04020a05070b060a050a030807020a0602070b0d0f1103042001021b0d020102160914011a0f161509140c 68
    0x10182c110300c4c090b03440c0811071900b8441c0420030b1030a01c580041095600c150b411640840c0e180382161408a4900f280d040380c408004c4000c0740310070310350b400d40700c0504003200c104850b00d40c4080240705541500ca00000740c1d50b01e5005100e4040a5030060085110f4040c0600504c5460f0241803807650083d4410072070761090719401029216010303030004000301c40340c0300d10000400b03400346074101c1c5501070710a1800000b00030840b8003c012240c0700391031007003d80760b460b80305030784480aa100703040011004000c0011610300e254403407003402c0380f04803000446441c29a03206806d9001118210f8010403480740342c41c0d02140e00072080c1d268400900c01810070241a0b10b8400181c21840380184c00740171840464011a070081c415480d5031440440140400d5030b1720440540906149403101a8410051001042c4e01c01c0041144400010110085103024001001c104856000c0e0f25500780e6001c2c0c484041d4006000300120f000f04004e007100100f8400a14280780407078840d150320840c180d9112001d15101a2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 705458183 1250 705456933 705456949
    0x402011709071e030b0408031306050a020408010b101e1101140403090801050c070204021b01050705250b011e0902030403020a0b060d0b06040c031d030a091505030a020d0209030a0c03061505 83
    0x40d03101f40c1040c0c4a440e074880c010100140054011701a03818102004008115a8080c0c41240c0c819002404401ca1100600410b4800b010545000815803880807058a060038103d0100f2090380ca0a96044404100c40c18211030340016103503810300e004800d200130300d503010328a50040c004501c000c01c014103000d00c00614078403030301c42c000b80100d402190b0310f80d040031019065210681944024001440c2410005220364807a142c042000d902c14004c901450481850002c4085e50100e80d07810a43d01f0078007401002c581b600101b02d004099544041254803841c0051402288039400900c0585502d14021050500c0144664040e007030510f0607101081255100036004201070340c3c0010341c540440000c0b4040c0810803d442803003807900110070104e850000081032014540e130365910146446201d480788804407022410b000440c02d001244418110b580203207aa000940d1005241850311000300307080c101c030b9800948200040000c2001844030a0054120700042500380032180c505120000b1400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 705459433 1250 705458183 705458191
    0xe15030604150803031006031109030a061107050d1101231f08010c05091512040615031a0906090309031e150f040606060201050606070204050402011709071e030b 71
    0xa035180c101c2000300650b8031691502418158064980e1791503c514001d0918031684600d0340000d1600c440101b5411000b0f00343c0e45030780c600401400074266640c4600015080402d02005d03513440401103c400240e08205641408100b51290007060380c6203581282180c500d40c28a09020800d42082c0380c0385440030600c00d61021036030010402102c2c0412070b20140d4800b54014104543c130f402200d103005a0460064030f18114115400d50903e00a440340016601941c120f070704020000c4408240080c581c0d070400c44402400f1003030564440c0e902c0c5c42c2d0940d5074410b60340d428801d030705540500039100c50601042d83d0100b21400154a812012004240d8600718041d90010107280d80c11409030202d0305100b21140202903a0f800c5510741440f0f0310070024200b064a0485a4602d000b100041081c010f0207890311981d030003000c4508004180d000d00c00030b410300500c202c1c10080b44000c03415054030116106801440e13450028440141071404460215444e003c100020032210113003040015518601c0302d0b48 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 705460683 1250 705459433 705459439
    0x2a19020d0f06110c0714040c02030421020301110316020d05040b130b0307110607020a030e0f0402090409030216061419020f150403031109090708070c02040e010c0e150306 75
    0x410744440c10903a00900304210890000f0500184070032410900044082c2a5002c1a041c2503064446408000403615402d03502c030003580003408200300c481c19000380b41d64100200349481c084e0701a41e90019003100d184c0f01803a12001c2c0c2c04010301200d4400c50350050304026042c002005a503214000180c0140524810112103403000145121b14043c040e0780d107001410014056134503406c11a4007e04509044100b1580d10301c180d500003925039100107020000305401d40c40300201030081c4801d00c400c002c20401000d030800d800b009401c480d0380f41c0703100c1c401c18540a6406011381514081c1490741001095106204001d052140c0c894449414011601d2054428401100b42140010240e050445060030035030203008001024111150000d289403050b4800c4e40c041015100340050130326a8018171200702c0d0803a06070400561124009e0a089400840c1404d003514941d070b007503000505403000701480e507206945440c80e101015410007540f00b00d00904a4007004808071954843c10240001082184 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 705461933 1250 705460683 705460703
    0x41509050d150c1b0b071106071e030b090703060302191a1b0d020a1b030305071101050d090807060e0a26090a030321060b040504050a022a19020d 64
    0x443d443c00b0b040b0140760b940008013068900303140340c200301c40910310440c0c509001c50404941168191004a00240700794020b032100310001e2845944800500c51081480c000d02d95124102c1400d6070302d07207028a100315429900031a500d402d41c81400340054001c0580e0380300f090303101018030441541844c08000b8840400856440b0b9294000f000c90000601845042c103004460707a4011080e4041080129507005001c9020302c00c01d02c01d40b08100082ca840003030005101444154002491040a01e16050301407511310304007400d40d1001400c580c4550300490305540001101c204010090090300e42e80c0f2000f001030100c3c0d000d00e03107e0494101c01010201600511070341c0e83c4075180101c10030b84610905c0a04152049900da28010f041740c2c0c2d00c603010f1842545600d102426003170090240700192000700060303509151500c01030001a110280c0484c040c0b0781c00b805080740b0035000c0350204071405a9001a5501c2c009003c80c0d01d03003041c5000b080d0813141000d48081002584070301d41903a500c0c65100100b20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 705463183 1250 705461933 705461951
    0x80a140703080c1605010801062001060b040603021b03070819021c0f0e0d08040b0f1c0606120b06042c0106030506100c050c01050708040803041509050d15 68
    0x1509140d110741008040c4840070400b0300720f4540001e402c0400086104a00c2060b84c0c48a00640b001a0240305110000c1d09401d80c254807507000802005003850700200114420741c60781d1220006401c950460b100090b40802c1c2c50810b0a1240c02030141805e019028510300605625401102e1086059401d110f441521012000c07502c2004403110741010b080e190924150440d00c0140842014004000010460848049140350080700095040e40c0500003618040c900010403040d0b421403400241c92140c180100d0101000460301c00102844603900082d6503410301030301034071807100c6020007414070f071814120505a4458404031030540f02100001c8203d12918031104902440000c14480c000c075012000091054250f00700501a20003210b000c14420300758802110603036602c41001d007165000c0e20700c9481550040c802000d8650040302440d14150320782210030328681c026807126021003404c03200d1044d0640d100c811780c805450304803248179003510a0389a912900340074210301d044040d83c0750038503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 705464433 1250 705463183 705463223
    0x40f0612030f09030b010609050a080f0a0b150d05010905061807061206180621050a0f0203070e0106051810020c04470402030405070b031b0c031c06080a 67
    0x80213584c80300c40b024040d070712514002e00700b100e00c3c03284c01e005030000c8401103280e150100d000880c05803114002c0080140d180c8426442c210050204245c03d081d49a051081d500c0e042c05d1104268010b100206600103907244c000d01c1d000008005a07a10340300422403650f1644045010803c40309945804941d216441c840d0400500742c580c851907092041e0102070307610040304d8001004581c01c425440640540d0380445030110101c1040003880f0350040c105003c0040e00031041d06422034000340460714032984401081840380740030b811800208a02107002000c0f0009488a15440b5000b501c954042c80b5050b00c000c1c0d0303107071480320580b8426038407080001e00310f480f07000c54521100c52890108181c411045c03400404000d1042c4c9449164000780801d515504260088a004a41c0600140035442c509403600c80c03a600041c10f50b000c0d00c804019154007203509180a40403404044000d507540755108135011001002e2402a0b035107190900c041040502c0b000700320000f4a5401c9010b10107007801c08940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 705465683 1250 705464433 705464447
    0x3030c090510030b0102060601021b0909010209210d0e0a03030e01020a02040f0603060605060f03010b0706020708042601140c070206040519180b030d0c06020904050f06040f0612030f 80
    0x21803600090030b0b6440052003a89600411030400702a02a42e40750748981c001241c6812217031302030341c2406c41902c4418455080848040c1c0e800000c000005007801804000101116452140a01000004400000051020f2020310044200c034140a600b910644020544141117803102a0501c2611418403200e0f9000707000400106500400070032404191101210082200e070100343d131640e01e026400709190401100b21054082c4649440c3c0c10341e885c005840350f03070383c1c404141120810b070244071110019101c3e90260024012840502d49640c0354240d601d03100f078080503045425681080c610041c901d58042c86250450f0403a00091b030740d00d00c01d001081092042c0e40c441500040d0ba088d2851003d041c00741244142c443c02c0c1c0b00d007240700020002000c203403444000205c2c0d050300306500c41d4540d10f0142c06401d80d954400d200241c28400380c4000201150302c120f510000c003581e80c808006107860644500e01c1e6405000c80101302c0b0508042102e00d000014403402414801c21404030000c13a401007034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 705466933 1250 705465683 705465689
    0x52707080a1812030b0604050d0f08120a0203180303060d14120309030c010c020f0d0e01090b0d20130e0405070e09030c1002120718150e0f011403010303030c09 70
    0xc50305600500783c90003000f030010145101c00082e2524034408100e180c00c1c01150201d81c0b0007030511a80c4840c075160303290202e208010841c1e09410421101010780316680807188100c142e2500140c03203144c01070220a00f418181030782c48454004204001301c0742c1c0c5022100144c65048a51002c6030300344801d00351f140c980f00e02c12101c021071000c0308000e0b140100000409a08240350002c0c44801c1c107503034080e40d50b81080200c440058000010481110740b00c1c000ea03a034000014909107071510b64680400e90701d680300c0d249020042d500c40d171803e070150000d6541d00b0b0405035907200b214609202c0841d80c038043c4009002c1c0c040001d4503040410f0a00c1400c005850250142080c000d8aa04014820f203549511000b4189000d000f10a02c0036039014081c400e032001c1210080d0814895915040201d582c1610740541a4041c40c0d039840100c2e078081c5034a80030303202d102191543c03040ca4500e07204000c03450b03501008031030400200d80e000d0290564a98150b074112541810701040710b1988400581e0a5800c6030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 705468183 1250 705466933 705466961
    0xf1c3002160b06150702090f130609032c1c0501020c0d1e0f0905090709091506180605040b1605011a01110d080112020111011401052707080a 62
    0x6480c1074280404019814000d080880c1c410710388a5080e80700d601c0390b000c0d61030040e43c00505070001608141007204040c0d441030b005209036400101030f070755070021034181c50310680006070703d034400c180b07030312005140040c0d01d2848045c4824581d0116001610400c504041e41d00790b124200021420042c003501038490701c40b948029100114014032000305040d1035802d56041d01c50b2036104085210340104403003050b81c10b40c7d985441782c0f0380c2414280000108080d00384010855500740002d16144684140101c0c81d800e00f8214602910f03006004ac0407401401d110845d0340440002044400c0c1c1250803102282e0300d142c0c415484100c044a0143c01e2000701c4400f8025501b4603503000d00c1c0d001d03030803841500000262110011000d50302031080e5601c00c8111505d01190445005124880101165240340c503c140740a05010419070302d07042c251400e00b001c03d1a4504c817980140003038546407450001d50400c8ad028241040b034109040c5900b250041c103500140450a000b051007900f86030008840840f041d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 705469433 1250 705468183 705468217
    0x906040f09090b150310110c0d0f030c031109090403230304060509060f060f120102040e04021c1e020f0402070b0613090506010e0907080f1c3002 64
    0x800c0040080c00b100303201100c07090740303280014082a0030101c44120b401300240082c00d240808402600050242406200c0100b100344203201080c0c60070484100c0e04441c035901d250000041010181c155404409040241802c213221252032400d44400d4400b121070490784e03094107440b41e0406480c1c0700610740064106002058a03040c00c0d00f840300c01140503a1042e403007081540d80e00255907848200642d004c141c4c0121000100c1e09520b003807051398000c0140282003180b07400f046125242281d003e648005101088502080150f24040d10b1407581c44410500b102300b44840d90b61602c03d400606520410b883c0c007114034800c10764480481d10403008034080e2085503030354564203018001510880340345e44600c22103413180d0000d03410303402441030942d4440014001b913404c20081404003100108031170218400d280c1c001803001010812003284041c60009005030442c40380003e220121488103100910941c0c0d903038108050308040481d8440707400740291080300c1c814034001402070b101d4180f200aca84005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 705470683 1250 705469433 705469439
    0x50730030603020102371e0506010e07050708030c13030c0801090c0b0405060f090d061d060a1b0c111003020d0501091b110703050706110c12120906040f 67
    0x552128098074001d8089460302081c001070900d81410083e40000010654542c00c07910b25002d0420500aa1180070303052801141c10404410044087c0000d0b6100d80c4580010400d440c0a5040250003d0840c60b1261520b4039075100c140030380c03101902079600c0d0880080c04201444080c280f031009582e01900c0040d1a03690b500649000c0e101041042e16000458180001c1c641d061008440c12501c0c06015107003412214031070b407001078011284041d004601c4818040c0058018800c1c5840039109100c017000c001c5409943c1d0b4a0000c000b409032151030315041e40c42d104a164402c240c450b12055150030345881c00d00d4030b0f19126250601c05119006141032110812664140c1c016249540c803004080005a80c3c0e2010710b0709569030312400c0c0901c5010181c50098152280400090b00c036407150485404554907035840b86051845d50010000a200040b01d500149003480006000181241d036003c20351070b0020341584440c00e1820100c42c42c2c00004009106403a050b0903140100148009686090742d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 705471933 1250 705470683 705470687
    0x50f0d05030a0c0215011a1b030304050d0302210601031e1a0904020d0204050c04030c030b0f0708190c0909020705010606090b030708041e02042c070501050730 70
    0x402c0da00940704038245090b442c142840003402900e039007411804000141d1810000c0450342851100340340c1d10310b0b010802c1c80342e01c0700d1602ca4503103a0700301000110790307c0c6081c1c1030550400205503201d03000c25004010040000c02111000c82031010f040e02c04100a441d16001a0010480500c00c103180280030850740c1c1201c0110b40c17000806040c01b07071050800c0c1000d0001c004155a040720029840240700c844500542801c4d4811503201c2c01180c2d00721f140544070340790100403100660003140c01815800810041800307885525420440500703102c000c9003418144080a100349211140241d560340090f0744410b4881d00760100102500c0741c04540d120520f00307140d4083c040b00d0140c8400704030070742400140c0c622034404a9206501555800c2d405403244d40d2405400400c103281d5005040c000c80490300984d8441c03054a111064510320300a1620140004404400c0000200b0209030010b401c100010b90300841142d0b80c0940c4024042440d20701d40c07003d15050946d034001c0d02052005610201e900a07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 705473183 1250 705471933 705471937
    0x412051209150703060f0b030a02070503042304020702030a1205090415050301061a0a030e0709050a090c05092205190f0516030305070b0a09140705130e03030103020d050f0d05 77
    0x1502d2480407110559941d181542071301da45200303000d02014000010403098408002440d044100315101514243c3c941e10f6180c65030700070350040340145145505861070b0f14a9500c0da4856144107030380a6041510301c1d00084d03141c014801c1c01500303d0385c13164012181e007441f4230211556400300903c10429802e4402d01d99101c0f0101d4042c02e402580780c1800422000b51070101c135680c04034950501c51902180d40c40840c00792200364440100fa100b0400f010400c88900e0107043e106071300c1d000700007500307040702d090a81142144e5840180201c2c0505d051240c645d4136202441c00447c900c406590711002141780031450200c60300c03c6601c0078010407001d10108444a030740c480800d8005c078210b40340d01c08030304940c40019550b03201c010041b0320104000000640b03a42d242c168000007810b000100045242c6601c41d9040703110181e02140c0e04005014055841c04011512500070078101c104000c80480200301d41d6440103000180c4100214507001c000c2040800094442c14600c0055550004110501904035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 705474433 1250 705473183 705473203
    0x30708010209150315130e011404060c080103080a2601030b040210020c0105030601120b04090809040c020102030c030109090f05100507080105180a0e03090d11041409060412051209 79
    0x1402c00031003001c8821040d042501c0c0590003090031030401c05c001100308240d41d4a4901c1c500b01040c5c961640c1c0302c0b60f140030302c11102c5100c4024400c41040c40c00d890108116024100c802d42400180f00c01070000c11078181c19900c00803c50b007810748185820b400074407106054030200081c2000e6080011040010b00e07840c23140168802c2c0c0b400051041c0b00720040e40c852488020050000704140000350340b5610481c80e1541b101d084a070009503001c00c0e0404901600c0b20702034181e0391244000307008550b0303040034860741040c0c402e103100860450030076419201c001e12040c0b0600c0d0440b500d419000d000c2c0419051203290081e481390844494245004c0f0100140c6800c5071144003040090000094500340241a2a180803000300ca0f010559124103100c0004e00c0d1701042d5a40b00d200a10000740240c0301d51081c0892280180284c82c404d520900801007600d001001d941a5680004140500c20900050071500281d000d0500150300521200486242c080c0905004c070500640c000d010132820007003841e00304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 705475683 1250 705474433 705474439
    0x30f01180c05090c030c071103010903020a030212040501020307020402090303130e060a05060f310608010807050a060207030b04020625051203100e06030c0a0308120a060302150a030b030708010209 86
    0x705580c2c50801c40741502c1162004034400b0b0400004180d070040c0d0000b4258184180d8031181c813424417001081c219181180204c0260b400040b074102071540400c5111014184140e00a14043c02c10000075228012010300a01031500454020744560f000d01c01d6600c1005034640940404ea600c1051540202084e00e0750741c05480200c1c000300e01400c1a404582e1103c0ca021046850128800321040580b10540c4200d020705044507902854091401c40c00390003003a850391405d0055041c03103000707030400c01c0c40e40c040340c030402c0c2441c802c011540e00840c42d00c4c1140c1e00441506002c0e968bd00206d44a486964510038400741c0900d541c19100802c010512826401001101e000c10301d8065114110300c401d5a402091000c0d8910410200e544030181c682d00c400e018042e02c102c0981d00002c00c14011054100312415600800c400104407540e040c800c0d481101010144007c510b1600810801c1c0181450b4104070140045c1010000d402600448812080a8100c441c0303d40d0354203000c5d000390484816148 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 705476933 1250 705475683 705475703
    0x1015050a0f140405010815060a030b1207060c031224090b1009141c06060e0c03040c0b031f06030605011d0f100c06020a0f141305040b030f0118 63
    0xc07107204000c0c0300449241d07100c015107400d091100644000131700400101859442040c1c3c0441500e582c0d000d00348007005502c01180d00303200c800410030202700038100c00d801a400003004000f40340e8000007140d070355505811f240040c41070101c8510060065005004000c00300e61001d02c0501401c00034500c03c40707100c1d9004104100e0b1260030400da060294050400040140031705000c420290740701c2416005004007075010503011078142400c90045800c00340c03455583ea1a08010018400c42c00c20b9200480c9520310b4074500c0c01d5a50340142110b907004a4044450110004644640715007a151008a07801042641160b488100401600203401200d000695026020300c03641180e40100a80b01c40081c00741113800d64100030301107951690040c500420060f101c08801094040c4010320820788c0381c0c0e80c0c0344841c0503203000c0a041d51824008400182c04104001c610104180c5a00025280121004036015038007200081c03410246c403510440030352a100121050a1040750351a030182c1c86664092 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 705478183 1250 705476933 705476957
    0x42102060601110f0604140f12090a1203080f0709212013090804050d110319050606010305090705031002120105101e05070b0717090d0f081015050a 65
    0x76480c4c0c01c001d0f5255410b0752000000c40c00080b40c8620006400b0461170031290031180c503000d080d281c0408052840c00c217040009e0440484c1c2410b0300d004000c8d00b400d1901d69002c03600c1c1c0c3e8005200000051001d944c0b500000081264540310324100e0b001010031a030880303030041c0e04000c403e40c01c04584004540050070b11000b05c0c0005450f48403501c41c1c1c84018170510398000c5c80503100c1c0107400c26800031120308804000c045144c0d9214004a86802e004401d0514000d1041c01031600d0300034580d4503020a9020518000c001500000f24250321610a190100f0740f61074821106145c004a604410750501030300b45c07628070500c1c19038007520401c1c420000d8102566611418001d900104001d40400903403481c1d4098400c1040056404002245e4038002e86040c4498031590b44444080d109500018640c1c840c4110301c500c00645250005509000741c00d00004c0a41d02034040841d1a21303850502500b4000900100c0341d80d168034009200c0f402e058607280006003002001540504110030100d0900762201c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 705479433 1250 705478183 705478217
    0x1060906060c03050708040801090c030302070e0c03061c170a0201110309060c031302210d090e07030c050d0e061e04050327030a1b090b030a0803042102060601 70
    0x6021034040e81c039119403102c040c2d24210350f0b41d07100740000e8840076010000050b00d03140902c035090155014062440e00030b806c41c54001c0c18a851507000d0508569070009103c071404000701281e0f040714080350f4407400c220403980212003c54070441c0150511040e40c01104004a05800610084181c4e5008010a004141595070280004d4030380d0505c030360200780004d8100c0440d8006680085807190000340d4015207600049a03030f2140c46244500742c00c0303c0e80c0084020302c20000400f41c00c400b0304090790054240301d11003e03040f0000344900704140c0c0761955400642d010701c04130343c0e50348041d000c03c1c0f00102c51900116079642d07040d0340128844080c0708105c125000200d51641c01180d001c07000c0c40c68101c5003000610080059503031025000319508503480700782d60400551258070b00c41c4407194a140e180c41001c4034604815807102001a00300001e42a40355000300d9504100340d844545540c9a80b1f89041410a1421407844c1611318801e80d020712021a400003052481500241d8031041074500300d10381 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 705480683 1250 705479433 705479441
    0x90e0703110906150310090e0a120e0103020f0d091106030c0a230711010e010c0c0b0d0b0603010906080c010c110906150d2408070603050405010f020304050c03010609 73
    0x5403050028112107041d03854440032540d0400c00084c40b5030b1005132484200c041e1603000307503502c07070010f0300f04c2208200403411402101180ea4080000d4030703511304251200155654145007500401c0341c81054130210341c0c02a810748420454000c5c0d403e46030301511408500400303c128050700d011012055002035481c0800032641b280300101c14040c02c3c154014401d172441c1095105500210741240c240c0d44a80412802034601540103494114514980c10000f5006904540c0c0090401c803101082c2800325025080b260115800e02003400c2d5038440d0001403000030038110719501e5014000000000740c480f03a0780c0080007522101010340d03e111060000640d0008c003000310041291b4402058052585861017005030b002e80b0140c0a100e00014191108000768402080660407660b240300d074440c0707070840d800d02c410a0006060114002400c054000b0b82e5205544103a00c101a1a003000908115081d00100c1030410900001e5440342002d1a000b07850707003a01d140c000e00940c83c0c02030003d10682c0e1805 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 705481933 1250 705480683 705480689
    0x2070c050409150c09150509150301060f1803020312070309050d150b041b091707271404030c03170402091801060806040c050a090501051e0d060f020301090e07 70
    0xa1600510a030740300940000d004d480945405000f4846400640c00d039034083e0342800b85e00d06641703a964442d214400c03c030104c841d00031100060318040c00180000303900504040101c0c03070a4281040000c0c0008031403800341c0c089400082d018055030301060f0301c4e04424005401c0c2c152081d290000d00e42e80760b80511044071400c62000d0241c040c000c510050301c44c01c81c2c1c0401c0c644000544003280d4140b007000c4089040b003c00805030700040300100100300d04c2001e0540703120024900d00c054089145018000f038103001d0b60040f660411080722501800c3c3c3c02041d400042c0403105d59036003020034035103410b01809910070843d055020552a4003200026044c0c9200c0c1441503600604496050300c80d9520b02c809008250001246503594807004542d50104102d514820b45c4121043c00e0010f040c04d0a000840074580d003c0d44246003800d005000913503c4000407007103225a61911080320b4082c50001d26041c45a88002d80703042c3c50080c0d20240381205400071350589004c3c0509124503c3e01c0c0e00c074241d50311141c2c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 705483183 1250 705481933 705481943
    0x110d08071e05210603010f1506030c02030c0114060f030f0604200319030e1008060607060f0509070f0b0c071a040b040602030703120504051e030c010e0102070c050409 73
    0xc01c240388102054188405640034a40141024002c07180d070320840390304000f0518890703407940401c0954a4240600502c141e04210240082c4aa02098001c8000c4501500051580b15201e690801d88200151800c0d40a05002400710004a03282d062400405a03010341c0140034882c1520500e080c00526285100a80380c020700035591a40c440d0702201c1c404e41e20350642c400c3e50b0300c040303011030340c00300400c1104111400032600c00200520740075040885010119000b282c2c900c02020034a41c00c07150b1076a200001381d50090b516850703480c1040091041e40120680741e442c0006011615200140c1ea1f000d5401840d824401a0786502e20320710035000312041d8105591242d4410b200e03202d044004c0302c2c440e00841d4003003824240c584410351415085a044100140e20104881c401d1641c840f00072503500d09514400c02881c00d2544580751940340c0030b04403045541d0409902486c40c03100304100d03915044c0d0040204501ca01000c03a0038040d5200e4002500e0100115101040d039241078420410305503480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 705484433 1250 705483183 705483197
    0x10e010504121202070b0c0105090114010b0403240f0c0f110309060f070209070c03180e0f07020a0b070c051e19031707080108060703060501141b070303110d0807 71
    0xe90f80700c0980822140d030407030841c01000c07000900008401c001d802c51403094030000c1070615000006900b180c0060a041d852180c41e0303401000320506030400c83d82600d8000d100e41005400400d034040c03d2030180e50109800d94940b800264400b40a58040f09a01d000d0341d03280b246403049010300710347c403001305038005072641c004001c481003525003240180b40c2d6140a4005c1400d14041e07800040c6090001c45007800071903030900800040560001401c4840c4400100c1c00d510517007041509109240020f21000340340300c035100030940450003003100180980c2e211025000514240300001c01c003007140c0104803076034861844881c40c040e60b158814445c10050000a00d641c55443d0214220041286000d400380705400005002009031152005d129108a0700c941c0300c0c5500d070604807440c040700200244101850041c0a20080e0f03030220b003a1850720074a04509450b100700c0480740026091181c10b10429201d100400010903400030355181000d5440c074181c88100ca412035056030303c940100c80100005400d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 705485683 1250 705484433 705484469
    0x601081311040b010c020a03061b0302070c0911131811030609040201082a03040309120533090c010f021209060a09091a040f0605061806070b0411010e010504 69
    0x200e5840340c070303d032101450402013403001e42d0045880c1512541055468035103c1c009060716594411020101c1825031030110328019090f203810107942600d006044481d91144011850180d01c0810780b40941603841504400c1c0760f070344408a00345000214802041402e04211390700180203507080e00c6c8251000b0741101141d079038039070046a42c507400800d8070304c81c00300c03200d2041c0c0004001c45110b8031141c02003280c90741e03900302403c01400114056000c00c000d0000f0456403000030300085500381c81c3c01000210a40c68017100c0c8000740c44403940c0030388110700d80c00c0a401c10425950002c0c1c2c0041100b02070f252510911020340041340c480906012400e1040002c0200240600301b940c018054179100c1d1031701c1c428054485600c101a82e021224601c000b02081d0b01d14551890f01d442030700303611041c8020802045e460400402c105010341000c40400d6283c0b000c00683c1c0341c889904982c40558007449086841c51b01c1c0c5020000300503d40707070041c0026940044045554041c4089a058440042207440e01b01c1d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 705486933 1250 705485683 705485689
    0x30c1b010905061201080c040b1804140a0f02030625140d0e0c040b0301090206160c120503030406050108060907120c08070608090f03030106170405150a060e10060f0f0302040f0e0601081311 83
    0x2b9001e841103d50881c04000c40441c01c40074400244000d21840484514641c14010075261107406080d00040d0600d140008819140c00d400c00c042e4a00c0b14103200c65110b20300f818002c068010035880d0b03503c06e402e05907100d03d0b050001c5405400004122003c00520000e4001d0601b00d0b20b202e100290407200802514070740c20f402d296a0102148552041080c260700c5001d036030000f51010404903082e602c00710601c07080000382d01845001d060301c000209094945401400c4c1e46405601c43c1001c0203660005440c00d0005084004001d0004e80003103e881c160b5407000100351604c01c442b456103078010030701d0340c500035080401201d0480e0352a23030311354a0506050010703208125024100b2200c80c42488140240340c002c03c1c0b81b003840f0301458a00090702c545040401400301c500101503c0310400c0446080c00040c0e0028086c030b00d01c0c41b107454030350b5680c01e0b0146c05a00038800c0c0e4002c41e0034000320030000a51a8140d0001c0c9224840c02e03664083e82e9100c544080b07040711003558000300403a80c5281c5123400d82c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 705488183 1250 705486933 705486979
    0xb03011412030a050a12240311030a050601050d0510020f04060f080c0a141608030a06061403070819090602040f0b0a0c0602090a0e0f010e0603030c1b010905061201080c040b 76
    0x20250382c6c1c00040d45192051103400c001029603445902021944041007800a003842c020716440068019000c0714540b50303109906c51205005240c42140b036604030317000f0300100b04030b01c01c03044004082c04c554505200300b07400e04a4006124200018441460141d20240300d1b0305420302402400348aa400c216091360199400450340e520b80d0441c03101803100c3e032100801001c04400047c0203006407903030780c14005220700641d8a290458018030510344120105966414205ea91040052030b02d4115900e40559405000d0381408110320100d003050520401d0215560082040305d03200e034621100c40750f407003030b01d42c4c400c1c00f0358011100401c841c150401c0100b102074004121044004012181281d180c013202c0c1c2180702c058074001d04003142d0200600036421001c0a040d00200200c00940c14190801840d6a48449000c2000700b041c0003101181c1c456405034025001403c80141030948400c104403100114031070034800d0030040c4c45045440b1090341018030540c8800318016113090b42c0301101c41d003001864 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 705489433 1250 705488183 705488207
    0x6070c0302070e2e0509090d0918090507180518030702010f02010219051b28050c0a090f0b0114070609110405040b04030306050102031206190b03011412030a050a 71
    0x88034200680c0080300044c0040d01c10b0702d0480151090003070522042c030510b520000c084140c036502054081d80181c0c1c1201c07003d0104c0384004113981355603e0301c0e103510000c0c1075440e00080c2607115030366000c1a151b099000511400c034100b4001c11481e43c0f041800d0540c141d00341b14425180d0010803100c005544103030508401090f20f40005860301c004610402208000490880c00090000c2208140010b140300104159241c04d00141842c074140700f548400c0041907182d4038140400410f41c0c40401006006225440d0340c01003a4107601c5a0384c04c440301c00741c03000049803918140b40c0b40c10650550701a4020000c0d081c600b01709142081455a2518010050400152068041c500a2400d40c2d1340714082c20317124610481110b85541000d280c040c0655480c2c7d0000390541d0024030190304145e42040c5102c1d44200f048441d0480744080441840700c1130310355000f07090344078400400400c501c0903403c40a022285c0c1a0744071581c1d44092819a5100e000d414a000d00103202008640d0340248680382040340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 705490683 1250 705489433 705489451
    0x150b03040212030d0915050601020309011d060301172505060703181401110601030b0c0d1d010b011b08030c03090709060311090708060f121212040506070c0302070e 72
    0x10722802c654099103950402030341d1020301900e03142e860042208100450070a41c580500501035400c1400c0043d480340195452941082058122004130180c200c0f0030700b149c3d040191040755656180c585442c1c440b1825443d9081c1881a12614500350200b0542803c00c0b000c01c450b54512103061501300516940b160400790f0811041c0c046a0341076503511040c04004001c07000814448200050014000111291450100e030300001300400102d40c0c08404240c1c060640c0e5a100d68600032040d101000300710f0032042d000000303280000400056415801400a6042600d0740704a02c50b0288140002821600b4000d1408905002240c0c460508030095900003074070780196000c081c0c9510032842124241d60064a00106000403600380c0d00340000d100d41c0165252a28018a29010b004100c01004510740180607255140b00d940c44281d047c819100003e041c081070b2590340f00020800031500200740c90a07100e90203003d02250456002c0c507028600e03907a150300030700400c2e4a0401890b444100c001c0a03c54 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 705491933 1250 705490683 705490699
    0x1005090903070611030709060801080d0c0201031404060b120d02030904020a1119110609031b21100b030604021f1806120c0516060b120a0321150b030402 67
    0x10010300980140010884c0700c00744640c492904010040500c91540d000700d051103030717107001400603c00c086042506101c19040c0f04000c0901480120001c2851100030b44a4000352424441003144a8101c000000340c11548401010b000c0c070440d40d00d400c80c900307601015030710400401a0300d00300b90b005410240c1450501044001a02140c51305000d08070b11032100d0903800401d0001000101c4d00e1403400d10b402036030014208122000070076500c0d100c96400780c1c1800d0000084a046560701003031703440c030103c0150810840b41400c00e1120742e0b41029107100b0101074101200e00c4401e00b400141076104540040ca4254007852846d00f02c0500081c05803030b042040f00c3d800c03400c207960b9007180c4080020304086d80c600040030b4110b10b442c41103500c0e04035620700f009001c020a0488110707040d001405180c11400004041c140d81001038107401c414141ca10890152050b840706041d0005144003101d01c01c0303080d010080030740805000480c1d803079003181007c02001e00c01c1801b0030b540c1c800245a0180c8061f1847c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 705493183 1250 705491933 705491947
    0xb0a02070f03021f060605070221030d020406080a140105060a020f150103110906031b032112070302040806040803040f06240503060921070b0702070911031005090903 73
    0x40c80100c04207000342c0260784850700c80c1000d901040340d1500c903140000e004000ca50700b0329000070210720882801a1188052160b0a0101c03d1a030b13200801e000d901904480ea200c0c6605040c070702a400c240706d0f21011030301031000601d41c0d030b405000d80f44042c80c050303074150510f0b03003801d00b0000e003908402907070011441813040a548280b81001b0146190072011f00400c00d940c55031420419010002507480d000d0303000e500500c00310342c070009025450800d426000040204000000c01d1400d84a200c06080d50583c100a00f01002c4490004044521040085c0c0d950740d55181c0007641a441180310f0803c00d5071040f000a000710300d0035009180c019114500140304a80709403120001c0d10380030781c01c0750002c44076200c9074101103481528032401403000383c025010514011903802d40300c85da40724a20050700101c800307000100d2112001c03280340076401440c41a80f41040c40000756660004c1c0101c00c522490081101c401c082941c1c1a240b04d450f030303c08114805411300c01840440b2001800c4007071544024022a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 705494433 1250 705493183 705493193
    0xc032a0703080a0506010c03121a130c0f081006140d0e0c03071413230108010f050606070819050f070501090b0f01080d0507020307090c03090203010f0b0a030b0a0207 73
    0x5100c4a4000e64601c800c03402c0050101088a1000e400c40c1e040c44102c03007500000a800964040b240020310781c00180390301c001c2d0a0072841c0000a60324540c0300451030500544500994001c488082c2e03079540f4a22010343c0c00b10117a03120076060304c000940144400040041c1c5204001079118a04002401400c01000d0f0140e04191600b00305156540d81080e84440aa401d041103840014001c4002d40c52002c1c803110003241100c1c003140702c0c0034001c2d40c50f030400c0001c628011081c4c00f1f20794108980c81d0115070392144924002d007a5007900d6074010b07041030080340d2240b40c40b00076640d109422265092411b5001d16502e0840d50b0080b2003881400010f1040742c2010108074042c00e00a4001c10000c80c03101d810b40340c0740324204001803c5403404680314005010500d00059007901038091400d141d50341c0c1c111400000d1400010b0b07413084252608111600c4d451a034580c0000030040e200390001c2c06601f841c1350000090380c82983e201500100031020400c0496803891445802c420140300042c50000107840d0303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 705495683 1250 705494433 705494437
    0x20c0f150c0f0f0315241b0a120206040308070f17090f0319030b0d0c051c06020d0e06090714010e01091a1b03120a051806040c17060c032a 61
    0x21705400d8001031a4500124105444044004c403103020303815114030004000b6800c07900401c5640520301110607002010708000308912491170b5003100c0e03104070348914072000a6464900322030880c000343ea18000b040b1000c1c09151109103030b80113a1210070f00481c1c8098103000b02240181a014a4403d00855500841d8140b009011000c11001041509011220003800b80c51a5485c107c1c0910308614200b00410508000d240a41d181103d2440340b10f0320882c01003210011609001d07250b41d00c001602c0c61042039030317840b13000d4008042d02036451a5075022070b02c644802a0b40309000e840c80d8000042e140c04c0d81700301c03203180b0069014140400d0f5152a015403440d90307500d032141201c04030400114060001501c0c41c100804c03291102c01949044e440b4101183d0000300a000c610046440e03102250f49584040c06d10a06000000100d40c2e0500e0242400310303080d4851701c03a82c45000c10301c4600d40e64050300490390780d1207140d00302c102c24610385074800508401d68070702503411040007481071004125501140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 705496933 1250 705495683 705495691
    0x201030c17070801090b0319020d02061c06050f100e010f051201031b1a0f071a0f014b081e10062102040e0102040306020c0f150c0f0f03 60
    0x60b6802d01d66050217040c60846085441c040d1007940039001004507048090041600507506540000c4002c10a10108000d8081c4a404185885a0074244c2c184403440c0da2008045a01c12654940d0f141076400c2440400a84090300000281d03111840e403c80c2d50042100741c50f054000c0c600140781840c440062420710000ba0022546001018001d1242c585d04031004409800408600501d00d03051b1941032802d807080320401982c0510104864040c00702c80f0092001c50086d0604641103450140007444c5000803d0140281004200c2d400500480d41c1052014054003502202410450a0100244050400805c01c4040000004081034000050043d0b5410503460000c100e01310355120101418031440150110f0b13040e1821404000c094180080400c0142580981850003a0240082409000c8600c0d04207640c0d07000003400030030094550b00400c0030040030703c1070320545200416080e881c0d0303806500d04264002c14070b000c940b043d06044e00030508071544a4043d460511401c51000b000c0d0400c40f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 705498183 1250 705496933 705496937
    0x20d0b100510090e010b030709090b010201270201020105010902190804060b0a150f020a120e04060e09030403021801050906150c06010b0405040e0d0909111e041a0a020a0201030c1707 80
    0x83c40800100c41c0e801c51003030160074038030111402c601c2d10703000051009031640f050402d00743e254108080c80b80d0013903010625045900c12038078003941451036002c1107082c0c5410100c3c015848c18000082d06034091080d10b010024140111b0080c41c8080400c460003400a4019151079a48900200031540c072101100014071003480b491290828011001e403001424400754015074110019010002c4c07002000f464060500c0e0501d4a070344950036020a0052500f81c0029145066502c1813200034100000500102c902c00c5070150550411681d800d100f0348801c1c480c247d04003410f80045101e62806031000040d03104c00115003070902d0a8243e220b450302c0020313442108030f08030000d028403050515000b840c2442007200300401d003d682e5088010729504152081814040c0c0d074854180a51250504540850081c0075096001100b0704113070240340e81c0544658404c590140c02d21450350320f41042075403110500f03600600088010b40d001540984841d001c00400c02c032540c0c102c000030303551900f0064010f01041e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 705499433 1250 705498183 705498197
    0x1120b0d0f0b070c02012307120806270f040f05011b03050a180210050c06150f030d1202090a03020301020a02060906090f030409090c0b0a0c0c12020d0b100510 70
    0x64100240b4240c1d0140002003004501c20440d0b025036041642e0070b040d21f0400c1010b0080c01580c511f03521890181c60801084110f0680b49912000c0e8000d40c450300949003203990344c0790601d0302151400c41c00b410034030764038003c1d80550000310844180d1b03189a80c072034002c06212000c5030640d80c440e4210741194510762000c0d03852075500b089440d894400c15a000d100030508100110705030103045042e4441140007031140240c070b03054100e01803080741512041202c0074110380d01410400e84000014511184070742c016102d4200210803841c0c005112000628203803070b11001c00400b040400042e601c4042c003207400401c203c0e40040141c07801d00c024150198603074041c0c0900c0c01d06070355a508101000d0400070035913210351003002d41002d0200c21101142d2801c0320000381c000140c80e0605030801258005400c140003c2004140c080d00901d080d6201c03486602e01e01e0f80c132903d400012100290b00c00001c1d4004c04600205130000e0802c6022903000f1141c1480002220707035400009000004102303964000030700c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 705500683 1250 705499433 705499463
    0x5030a05130f0311040b06130e0603060937080c0102030411060c070612091208070f090b030a0207030201060503010c1d0f060f16050312070f020c01020c01120b0d 71
    0x18641c0110040d194128911044900d19210116194000800688190ba40300001140703581c962040729507a03050204501c485a40c0c0c2c090b07224208504843c900e010380078203400a0910f10005c160807682002d01c1080700c082e4030b010101a605200d0220310101024102202031001c00c0c0303100040c1400203540800980c0c1c0307142c03600c2c1a200310043d00c400940103140078001c2c42e07803944000c42c81800752036241c600f00d12036048886420340604040500900f413650013494803c500d03507100b00650710070410b5484210410b0310070078044410210511454404400510105186200c260010515079009100114405455100003402c403051000124082001d05848200d141c1c1c0010154540b1101211003241034041e00002c900c50384a80450720a00001c0020400346405036070040941c029041402c6a450303078440084a4040942903a0b110041883c180b40045a24400100c900c040e03203040c0d001c0c220181a000055030280361664070402d0640c1c880081605944800410303c0d480f13406001c001c0c00d6001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 705501933 1250 705500683 705500707
    0x1407030609082d0d091505010b120f0709170f060a0e070e0606030c0705070f06030b0f030a020a0302040c030b0909070924150c120305071803170c010905030a05 70
    0xc1000d0042c0f1640881003c6041c80250600365065510060804a8482c40754500700d10b80c84000c2c12100e40c1d00b80b42c24004503408108402409981e050a01500e825031510711000598410032503419000540490052101c6000c11640d19440c8030b040049805c400f00543e8642d041042c1150a144640d690303e8180034091001c03c0301340000d04c021002a43d141c102900408c00070302c40101400da14000020700d120821000300156001040001d0240c1c80190f02d07041c00802501020507400e03c56912680e60031003a00d80401c0880e0095401065500214615804c1c40080c04030800d04500b419600e03c0c0c2c046071501c03804581ea12980a41001d0b01321641401c0391142252050300c12402e50440721083c04800041e602c5014050b1000880c6424031045507500c2112003c4040d000100111038000d80d005049030141c000c0e034040c2c2025210510b60100d0202142c68075040e521000d05140c2806604007040c0d0102e20080c201041ca00700089090031458071641c0c07071030340034000e0440043d60003d03500440c56 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 705503183 1250 705501933 705501967
    0x303030908210f13050303010519050d0b190509190c08011806110909011e050d08070c080309370f03060b10050a0e0d02150d051501050304140703060908 67
    0x134641ea9520203030300d101c540b030f11a0340e80414000d40e4002c07480320304000949008044100001e0038020b212000e115454640001422820381c0c3c0c06402e4140300400500000450190301d224551100080000801c00e140103000503420074001e440c460902079002c1007000003801003282c41c1b0340f002e40240c052107580c604801201c20507c26a0340d00001800300e5552941c070340031306d00e0440c0c900c0c01c610b0101040713002c40140501b40310b5001c590322546041204080180b410301410207540980304001800c1e07940e0085640301d1060030341e134503440307540e00c40581c43c035400c1d01d10300b0840c240201070b103c10003c0c40400440d030109441e81100340e10f0b50a0b410100200030440c00350644213003041e209a04408801c41010300980142010441800580206001a515440b0303101c54501d40042000010f629201c94904941d0310102d1000c0f1740394148070000f07035a035452400d25050002c06956007440c40d030340c0d5155440c0d030001411040c42c0c1c1e40501b20000000c5071b0640134500c01c2d140500401d5554008011902d1298 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 705504433 1250 705503183 705503191
    0xb010c02060f251a0a021c0b0f010309080d1a03100e160e0403050322120207140f2e0e010e010206070c110f030a05030d0b09100303030908210f 63
    0x180c8641030301c080044c03070010b03512440c100d90300490b02c01d6484079075000380a40101e00000266401078000001c660302d85421040c0c5102d0296003010540c01e10344011800d07224240400740404804001c803001c01c090741d90100441408900c41520b00354420030000381800300035801c84e4002911060207515941c0f043c4901218038981e40450307001c0070700d019505042038500401c040c1c18440d0100c00984040c00c4517151081c1c400f030b820030050141744603203002c0780c680c135440130400c00510952901040c054403580040403040002002000b51402032820130101a444803516a6416070300d9007070445403403080c06201b0b5410100e84030181c010f900d00b030004100105a821850465100905000656401003d072504964001c51540d48007005180480c1c144022505016014410f804182d024040c0c040040d140031008900244110307a1220108000c0200960710420003a00c3c3c6402080020b00943c4030290b980e01c200c4c40a82000c0c0c07699a9000489840c50380c00d542d003000c210802c00c0d401e8031150210340c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 705505683 1250 705504433 705504487
    0x2210a0e071203081003121107080304080a1b050613050f01030c051914040e040c12051c02150c0a02010c051305010c0224041e12060b010c02060f 64
    0xe0107107080c02c24140703512410809820b001010b00411204441117800c0c2015580200914814a24049004141c030a041c2e20052460240d9003002c50441e03030100882c0c0413284290010100e129154a90b00c01044010303103440e4403034003666400101620740344041c6c00d92804051400c0281840d05081c081c4c12906681c409042500c0c103580410081d4010007907c515032240300b1070f2121508441029038010003681160703c4442008039000a9150502c030805110320700c41c60361444a1981e5140b00825502106001030071071b08820310070051030b0051900480c3c0150648120341409083c0c0a4600a8480c140c60a150b00400014000c0c96207409005550b140012403508034a008060004801c1d110864000e007810080c02e40030542c00c0d5a01c0c52030813274084000203c81c02d85025040d807221480d07132042c800c0305000201100703d01010305e07038100c19900300c1d0703030b0a04440caa11038030f0341d0f904006000b600a214140103205003100c0c0235031100801b801081803214141a81e85140310b1304018210b0b603007805a10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 705506933 1250 705505683 705505693
    0x1902030403090b07110307180e01051b1e030115030b0906060412080409020a030605122e02070609290421050705030d05100b0a021f02210a0e 62
    0x80001c0d80b1940400032980c06000c6103860326410300d0300902140604003d1036061140c0704021440070f0340c0c200180300545005c10100220f4095071080350a940c0110307603c80250401d007011f4030900c1c2c1c841004010740001c040c032580061084105403403481d00280c0000c41c041c00200401c155444c1c2610401c102040222108545441c01200003190341c45140624585640300040070010071224106a9000d04049481991108400b940003001400c01d44038492190313100901c82d00140d6004640080039000d240c48070303542c2e0745004d02e005281040d0490703001c0c0d0704e5070300b00010700109560384205d0b820f152280c0d180c5040500e5103203003219003000520740c042002c2e84580522001a035100101040c40400102c1d031000c070080300d58151100e0099800241c00350000041500c1020080c1c0d0065100d000d000492011007911050364040d03a028034103e40016a02040c01019030311900f09102108018941d00941f07049124003400c11010032000040961154031010720443d03a9182c010140201c0d50000100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 705508183 1250 705506933 705506941
    0x90f29090f04020c0c0303030a2a2a15060f150c0209100e01030803090111090607020f0f100305010e0a090203070306050a11030108060403020d02010b030c060d020712020303190203 79
    0x2a40207003010040502c6240d002900011209003400403600b1018000d068a842c0e00d4a01c603800042d0107042c01c56002c682c65546500c500500301c420440601c1c1c50b6544400e03071041c0e0114049203402c10b2442151014281228103070015590a1380d20088000101020480900d4003040d189a03120075000b070b1401c144060143c40004d948018140750143d011541010703e034803246050700e0f60414075003041e800340c0b4000002000748101c05004501802c00030000b0420a003c481c803071a090700410300a1030f4840d03010021403000d8542500c0451010000414481c00c444050000445402c215201040800c0e11200100704c035400304c0b10072650015000005014583c5141d00203511100c09010042226a48101040035011258030100d01880f0155243e03940c0e58581d0412a0740e100d080b5000c1380188191420001000e106001e001800c1c0400340c01403580910304420040c07907402c80c984c007540c100d900f0b1101c80e001c120b0381042c440c1000c031180c0113140c0d40d00b010407203020b000f1080c40310f000d400740c0104140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 705509433 1250 705508183 705508189
    0x904061203110f100f0e01110c06010504050103031b060e0d0f18050a0605180a0603060305010b04150b0f090604090b0a1211010503040f02100302031801060305070b070201090f2909 79
    0x20020f80c8100e020000700b82000c0c5c0c00d10fa00504802c2c402070391540c0f034101441603050480004100486e0904c1c02c444c1182e90351030030881541e109010040001d464140034618484410640141e651301c5450049074a0f002e54829514041ca80805070000aa0421850014a812100d600c0040100340d0500005a090402013500080f042c80381c0c0081003800120705a1820920900043c024801400c2003016580d424008016200c00d0005450551070100c4040c46441c040c410908a01003003251070075902c1c036050308414150002741c1042c001040800c0380c45140d541e110014000b0340090040020200d201106001d81007203242c0028800d40f5114404102048000c09003000c03617002480c1c070660700e82c3d4500d0551903581280c07000a4010104142c3c0701ca184e9003540203188201e2203443c525a01456042c01c9900361501448090a40d80140d40c0c240310324040c1200414181d40103040850303050381d8907540000c2c5601e95500c4100350b4046000c94400900c0d680d40480b00c040000014142861001800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 705510683 1250 705509433 705509443
    0x1090510271a06010c150203042a03060b0f0d080408010c0f0504121728050a0e041a210d0e031903090807120c091103040b04080904061203110f 63
    0x854035901c08107200080f41a0b100d100091011540300300c4040d1b85031444020364000e5001079600719113040318424201d21410003450540103002101c036000d41c04610f07684408000b030046520094001010041f09e0205848241174071201500c81c1c00d4465a0301d1a1141103421110f00d88041000c000b0b00746210048a5405002d4405540b8481c4010003506100e10300640300c0405400055014900880e041c1070088010345c900e08504040300c009541c0c043c0c80181120140700c1c03610400c01140f0441111040c50920b0f40c018034482e061007161080315081040003801940401c0601c1141204c1c00c074040103440c1c024480000303003c0d00b90910000382081c002c002034440c0c103020300c00c1c6003039241102d190041c54400c40200000304201400e840305035031a200b452012000304403050b178500c000703044001290002442400603402d4400d14031401d644440d40e503032000c044060002e940c105000d002c10006542c0d9031083d08000c0003100345039140d91240d0f2034040d00000224074010380340d4014420018a00e10302140e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 705511933 1250 705510683 705510713
    0x6061106101d07090e070206040c0f0812031803070c03060f0b130b01020a02060a0c0b060904032f16050112050c0d020c0715081015090b0c0109051027 66
    0x2482c18603542c1c0d0360300121482e14560340401000d00761401801591600440c5090117580a0116410500d4a0784076042d03110402c0e100d80300d040d41c4100e042c101d500404002568011040594514001d0940e200481ca5070308042001e5460184640080041001610800601066040d410304c40d50b880c5d0380002c0c4118181a42801034541c076840f212000343c0c0b081c031018082c6980104295104c90310154000d11012103540c0455071142402d011460a03d0507400d610721590b4140d40349a150712032411100e411f00c510b040480c81500e050035060007050802c2c02070b04c0d03100824803107041107103103444001003291440031290b0750014900f82c28401e480d02c0180481c0e96215000c0d00c00b50792000380742c0f002403500ca10381d407200c000e0705030030210350b50180d9102c0000b500034201a0034001c152511104030100d0380300c0e110901000f190a0307413001c01010400d00c01400e20704548100005094a0545600f41000070020301c1d00f0034107503a070502e0000c0c0a8540425010400811000c1c0846209941d540d2041044c1034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 705513183 1250 705511933 705511979
    0x106050d050406090b01272f040315020a120b030615121b01031d1c03021b0a050d02030406170912120406060509092508010606110610 59
    0x240010341401184d42003074015075848043c03c0e01a40c0d40b8513000708583c4401e42c810010014540011584140c54000c1c802c0800b440a00f034051405d8449003480141410040080701110904c0008045001d101802e100c030a001a0701603501c8643c3d000052042c4494400094680d19014444800d41c800058480d809180f54a04421425074100000c214441485941041d8030030110240c8002e41440303800d2985641c2a2000e005c00704d510b40e4501125000f0310100d074416880021600c0c0103525082c852490913000c2d040c0149480503140010002c1c01505c2c60719107041d48405151001c00074100443e00402e0010302c05541414200f10005008003070013100702902c6500300022448516043c040340d40700168075010590b581c9005400c004000c001142c040d00e809140c054006000c0c10a455454814003d03440038212850026206880061140e0306130076141804600218034140244500700c0a0001c070746544d004d00f13446120280c50084001c0030046c620815550400c51960510f408041404982c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 705514433 1250 705513183 705513191
    0xa03031e02120c01020c1e0d080417040e1603060b04060804140102030f0f0c07020a0e04061401080c031b010509150903030f0c0f060103050c0613050306011e08060106050d 75
    0x19900891070204920a0702c80501d10000309045002d00560040002104440030343d43d01901030943c0c02541c00050310251001e800c440c0041138054819444994042e210700c0d0600e207141e440c1001030185070071035040a55566200414010441c81a200d0045840c0e15454140682802c1000c02042c6024511030f00c0240400b06020404020110317813055080343d01080211740741e184c40b1000140c444000d07100181441920408251000d50744803c4400e0700c1c1c2c0142c034105041d0300d010014844013100500503100755580764030201281e88940d544500038115440100b2500a01004040c06c08801c52603400c048400030045882c1a60050165128904110341c2e80701c078011501c54050062103100c0700d9540c140000520705178030000d09809451020743c00c00860350303013200c0b4001c01682e4100030302001c1c0607540070b402980c149140c80402800c203101d2030311590107a2541c800c0440c0c074143c2d0a0304a035010320030882600c507582c0004100c072401010001c00a0607036503d0004050824803803415524045a15 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 705515683 1250 705514433 705514487
    0x15140a050a1404112101140601110c030307030c031101050420011701120807060c05030417090f06090a03060609050702012f130509070c0b090a1518080a03020a02010501050a0303 78
    0x1d01c4070318a02d80031400c1700902581c042d401c500400480101e5005012072002d1044103822800026076084c1624060000c500e071560780c3d24103840b24121741c4012000c102d40b00400c56203040d020b00036540502e01c00e944004250402d140e0900090400b4802c1d0b40c10420181c0c41060308034541048181100c0c4056903103445401d103030401c00060300c43c0407000b806803800d20340400ca009501c0001148101d0191782e0900c90781000560b142c2c8a845003a42d120352100e114201d80106180c02e1000b030541c0c0704000d00000050b070384d0766900010755160b0b921134034683c1d584004000e50070b0380a0140248030407410045086680c0c20040320090411000b1405200000c01305460030722000011101e8081c28000340310007450310f09410000d102080c03101003121813410020100e41a8403000904541c034550143d14004c1c060b014480210040c001c0310300306d004280301d500f00e407000705802d82e0051400303c8030703654003581d20403280a001c3e00703584040e07202c14010b21a07660100080303136004d010344429a0084c2044c000c0420 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 705516933 1250 705515683 705515719
    0x230102180a0b28110304030302060103030206060103050c18010207090e06150f1003020702010c1a0907080118170d140a0b030c0609090a11041d06040c0c15140a050a140411 75
    0x320844192517880002030200c18180c0014556040302e00c65421140e03140c1d034a0b00118284c500030f0791f00c1e00c603c5500b4003011044c45031840180300c42c1c0c1018811241416a00e50340d001c00d9441b1694202100e8000e40f082c04250b0710008a150710004043d02e02441d403054241c081100e00d010003107990205640031442c00d0031a849299011403280d001340d039060082c5c0a86550003070289050300c0402c1c4501c80c802002a0801d07041c000c07450070240e19980b0042412164981c01c01d00c106083c10644103500403c450309280c1402e01c100200001c08040c401010b1503e07529200c11141d40c050494800c1e44400c1041045545c1c0004840c81224140d903000c801d03445015112001e0310800d003a10039440e0002c1030205046540d0320403240b451040300000d414648440003400101c0e128803040303000065100144c040070844001c0700d0701082044607000581135a43d010080103055054840e588071607100c0d001d10151a029000d004201040503400320078030300b020760ba4401c039410800e00c0d49004d1407001d03010140c000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 705518183 1250 705516933 705516947
    0x6070c0506030a02220f0512151303180503030a050c0c0d08030a0b010912030309080d09060b090f06012a06022811030403230102180a0b28 61
    0x10090041612030510f985000c000c4d4125100005070403203030603100c1c1007000c14003068004031508200e55100780b50030581401505141910312000b14030802c2c0b1405008440000e9440c46500c18202900c500141464001c010301e0300180f512201d00c00c41c00080c04550f80210448080b04e125042c0385945640c40044c0310300b0105014001940004030032480f000303118181f402144034039403500040009114038001503c40d03152900400c0c0101001e28240c2c000a4040d6120000050042d07004500f0003440c0d242032402c0d200383c07034821619103854844401103410b210010542150210007010a186009000200381c00681007041002a0203000c0c2c510090100c0911000d00e243c01c003600399030354000c0102036020020030b840070748076001d000e41ca0400c0c481e20950b10f80748c001c40004040c510b060b00d50384400040004c03125405c07129800c020701d242c1c03c5140c05d10061903c1a01c201c411240401580100107801c000d56003c600c0da10740400c2501000c2b401c0e020a0301503c01c094060011080034003404503181 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 705519433 1250 705518183 705518189
    0x1e030e030d092609040509031207050d0c05181905210606120d0c02010e180709091803031104030c0b12130b0105040e0c04050115020111071106070c 65
    0x5000c00107600c0d1419299420070310106000c1c180d900c40c3e4030801d030078145544494030310800880d803090001c0500b0349026044aa0003c0c803034070031a03042104400400c2d0a014054507608041000042c016448030b03140c0c0502c03400b4040b1401c0c070900340b00100c05208041c40344000355078407640780c08000e16180080d80003540041e18000c0e1140800e1400c4a03012100d0b83d245920341c807400d2083e9400600039107000e045070180070240c0f00213801464207510044d0b800448042c4204e0601280600c072480d26140c10b071407032441081100d07012140f070800d041e01400005142c1c0242081da0b09042d100810038480094048070203605260005040e000121540c0d403d0023aa00b0003019661071540005920b80b906001c1c0103420f142c09131081442d15003862812901d22652401448a80088010000c5191941c0904820020442512800114900000d00701e4100340c01c803940b41c080100080540a0382446600b00c250a030641d8149032a02030f48a030030120b040c0900c0c05200310400503103501004140c1c6001401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 705520683 1250 705519433 705519461
    0x30f0b072706451211040516020309120102250c060e010e040c020f1516050705060109050601110109030207030b0f0f070311070803100311030601061e03 67
    0x14001181d00701d81d129524600c81c2c0d0002868084110b408100a0010200e00f9004484000316440304102045549440c80000702e1080c01d0038500011110306051100c84224401c0511950000300c3c1e0007084221103026040811b001c0b0034940300d808164002044a09100f001c4606100141c42503039120701a21500b004030303c0d1003080f15021901c18040aa420030654450301c400340119860741c004840c40c008110b0b2050000e100b84195020324102640712610101c001d1054801e01aa1400d500e4901344a258500c64a415100c00b0011450700d6985242051042c920b403170f607d41109130f04c685a4424040c01400c01c610355950114107036070b0107500030210f0009008000d0001d454503040103500c5d0b00c1a0301c01980e0801501c8005801d0301c40c040c00886c031451104204003510b4540d240c01320000d000424024084d141308004020102d010040510720410411001c841d809045180102820401c0a413490095001348010300180b81c00c03d201854034000d555a8000e2030080700e4044002e0220505102c2d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 705521933 1250 705520683 705520727
    0x10905030901020d020f071806321c1506031505070207060f020d0c080d0e0c040c030c02030307030b13050712050702072106110a080f10030f0b07 64
    0x41200100160003861030907000e60303020908000c0282e80f140510548003d0582040b5024131090860020599099000c4100025060b850b503018014030700880c0030000120124803015842005125881c1100203025078061111403013a0250121001311114001e040308800355134403a0301c000c0c5a00070001035402080034030313540040e002c22500800d81950824018001c1001c08034000340a86100004003203076a000b02903c4214001c2261141d0518204441400040004201c5000140103280c07030740780071001510800880c3c5c03081004660f02130903150289410112082c0003d0303004400d40340e03c210903040110300e94417031500180740e8022405201000e90b00c2c1c0002d004030030f03920074444500c500d500301c4200500c0e00c80c0d410581c1d90b19503c0c410a00f0395a103645c800c01c024900c02071500c1c0014850703071000c14a004682c5229085810101e02600042c51503000c00c84108410309185801051100c69030880750305684548001c2190084041c0103c0d8040c00416038151060050628058245460032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 705523183 1250 705521933 705521951
    0x1020a050c071a0f0304051219030608150112050709020708120f251202040801150b070c06050a110d080106091a0d09080c0a050106060908010e0a0201050306030f01 72
    0x2404039000030003030324200c2c4500e080100b00c1000a00c40c0520300395144062500300300c03000d0101d000d107a20042c0122a00d003d52000f100b0f100d00d84901800b04020303003500800305605c0001c80101152103507800020241c4c854800e4158100e0210303003190544445403620584031280d801c0a614102440c0d10142e2031520008400307060081d160050014101411010700540d114844c9420940e04165030200382144e602800c0f40c0c0c118032111001071500d400d818800701161030409500d080b82c01a40c030401b101d94403030100003000c14081001c04050011705498070304007003094850100380c1302c00780038035424803030002110b00f1210b001d21075010f400c00654044543c20703c04172400514030031080c0b040e80045403140c400401d0110000500b010342002104032281019085603030070000d0059080241c1d40c10b0f40411104041d000140001c2d03048a014500119200b4a8103900918200d1107a00030041645170134580040d180b4082600000d5580900c1c1540c2c0702e8035054001f03400c2800c070110611545d0700c0c00307000e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 705524433 1250 705523183 705523187
    0xd080c070b03010605211e0a060f0b0711030615041116120f0201090203060a091a090607090f05010203070611040503070608011502010c081602120f0d060603180602071401020a 77
    0x40c501824030030342c0e039a60f07130b00c018241d400344186c03e031145164003400c0c4550203d58043c19601c15882a18000049000745d510035609070b00c0155034015130640c1100294100502c0f4074024a5a03076908194000c01c2240f9249500001c086001800d49206070b840da00c0000454400006071040408400042d0b0031003231291401c0308100d0160224100030480822107142c43d0f40c018810410080e0b006009001d8694400a080e4000e21914508944120350807507135800822a00110350301c00c0d82d52000402407400c0c031010280c10714000354003044c030340c801011003070000ba40d020094036000d6078041c2000c2056407034460000600c1c0960707045503416114072711000500a0f440010541240c85800721406d180542050490988920b070300c180010522000214000035a0001d0303e00d58581380744185c5580c2402c1d8507131008664400da40d442c07d800000b20340c4c00d1401e0500d1003240c0c010249810204041c6107410f02e800b42c0040002409000309070302288003c00d000010144428920344c01000315612442ca00b40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 705525683 1250 705524433 705524437
    0x270405071503020c0c03030a14070c030f0c14090709060e04091b0303030b1f1b0b100302090a0c091503060302151201090504080405060c0c0a0b04230d080c070b03010605 74
    0x20301c040c4c3c0c0c41143c000c4510342c01c2c0882211400d200c9580d407004541d02d01d0000c460300d54410b06040320118046000080410200842c2c0343c18684262001c0d0015850300c510b4003000700c9041c84461190628078184054a50400f14050865200d07040a030030030032980340084c0c020301010307602418803200e2009000e0161009601d035400d0742d1280c2c400300501c200d00380c00d200400042c00f40d14010520401d201019a60041c0c440320702c2c4111040400c41d101e051950358800442c0e040d41d2050381d40031030241c203208602d400150141d000024220810150b2000c2c2001001141c841c4105510300e66915201189544240c000c41c0203150040c005108941903500820140c0e44080760ba19010344080d03001044071040d6000f840e000365003149129040600304010007006034032071814800c0c00c0c81240e040d1a00741d02c4e100080704c0107000d6240a07070703141c3c1c1c0303005424841e80400596003104542c0062a902c0c1e55526045c10111345900812181d03142c600440740185420019000020341c0b400c0800001007841e84080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 705526933 1250 705525683 705525697
    0xb1002010e0f010506030a022809060311041b030c0c020603011d2802090406080a031d0102030c0a1205130f05040c050a20030d062327040507150302 65
    0x8212048100b00c105003901301e4000f078401645c9030300a03886041c09890198400901600c1030715400c4021000820f0014001d0a03650040c0700031900d940040050061480340380301101c60075102400f5007a1401ca1091404405400003018140e5800361010190b200714000d0340f440f51301902842d80d1f03507140c40c50f0b440076102200c0307a0400b0001840000e41c01e03034449400c0e04c00004405071500c80111411003114041c0d081040e03441d821950b00c020020300150100000110710340651118410145c0c0c81c194900008001c2e00d072541594020001400740b1240020f0301e521aa03040250291040104902200c2a114440c1c1d05800880340400c046003910700480c1003821603404640400640c40b01c0750094803c1d00030301e500c1c6004642c08583c0d0360101c513000d480e06940d5482460640e86801c179400da90104aa106403c2860344e00003010440000100444040a00400403605070741210807152144049403007000c5808911b001002c040380c100305040141401402c11260b00c0c0144054503100140290404e003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 705528183 1250 705526933 705526961
    0x141e06070c0f11040b0a060309020315060607020609040902300607050d050a1409100e0f060402010c0f050114042a060e060c03031305060108030405180702010b100201 73
    0xc65000c90250780c031201019400725140c58480340035210f520820000c481d0a40e0071a86a10008030707030350385034103200380503100c10b031800118030085005042c40e10a58910a1084510010900049a03140016520150b81c101c071019034545140c00854041c044500c0003e400080035105011000d00d45d442c1c90507003098150034412a850012005991480d0070364a0402080c0100140305031051070b03401050340030141c10808101100d00005180c00840700301d500c501140c12842005403c04003038046d40460b040d2400040054140c0200d0040d140e08024000a043c030000403141c03c03c00041000042c0b0107034101008100c00102101c100c80b100a04a4044903003071034901f000216455140e0414420150a041f240e0b0071074200307401500d4480d5100740d03180e8060018003405810341802c0000b5445090076101000200c0341c00d150252510030b0603000040c4d1500140300500c100d032180e01c0b10000d000c10900d101c50082c1c591002c240d0040c040c840c107150704010509181044603405403c1000d20411003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 705529433 1250 705528183 705528193
    0x7051f0509040e070e0a0c08040201110c0a06020d020f010213060327030903120305040c0302091f1e08030c0d12091208090c03010e0c0d05120a0e040f0204140d141e 72
    0x4804150704a414441e1f191010441d00004a4059441186d190012000003c211181c050750791000442040b032652007c40140c1c00325000f03000095061000e485101c480c100252305100104007a991b02c0513246c001c440070981e641032a09640c101c005105020b2005441461050b822981002000e00c0c50900081c0c1d074513180141c690607007034468840c00d4400d0f500314400d50790060a40c1c5c01c006d0b401e080980050102c2d000710322036145500c6081058401051841a8120300701c940b98109000011254003c1d20a500103020030b650360f00e80403803c281d048196240a8161010f00d03041c420050148007406450104520700c0c03078684075000811240500240e000310346103092082c04042c00e03502d07199408011034200c1e01d6008070303500b81010600d481da0311690642d01c41c040d003583c14210a801500c0c0d400300103880402c072144142401e1003240c00c3c41403500025441d2a0620b41c081211801c0901814010720152851905018107007003403400d050314020607244001001220743c801746944d9055118a8001c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 705530683 1250 705529433 705529441
    0x303090e0421120c080f18060114060d0f0c110c03071e0806040b0a060b09062506061202130605031507170703020c0c010207051f0509040e070e 63
    0x20181994490369019102c200400a4400c0a000402e041c0d200e60050015181c0803515040d02070040d0700b02c0c140c40d0f5881780640c1c07414000d030f5000200c000d418155000d079a49080741c81c28202154460550b105044488512980a00452500c1c0700d848039501240c1e260120006080030160000480300e02e0903565000503c01346850b6a498044040c00143e255101a000708034074140d88207810749001c00c0e0102c1d06500d80d5141c06690802c07404840031910000c9803c00c00c4a040c08511400b0041c21060018a040c00241e030301040442c0b05804100081c8180030100c0f000c002c007001503003580281e006405119407644c40c041700d0182e1122110480c4a9220300c2603141c08a042441800115400103005040184407281094400040500840f0400a40b40c11601314130200b206224090700d0740c0d580059450044040da5414031007041800350441d004414200000d0f81e5130050f0b20300f0f110080c503d0061000040c4400e651901c2900021a00b16080c1200202c0d49440411304070210317a15003982c01d80c26a5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 705531933 1250 705530683 705530699
    0xf282610060b091504030206030702010c08090303011202010809100608011a040e25150824010f03020d0e060412090b2701030e1006060f020307020108150105070c0b04030309 76
    0x10841c0200c14071800c081c043c1e10f61a2400e10180700740100c15040351854180c032600481c2c000e41c021a04000540c1d1502d4007a5000e0f984603814950110110015506550400b00c00c41550007402401034104449040403e050a00c20b000400c40710784190000c00c2600daa0380491070203045944e80d2010501d00b90101350210b0f003000c0c00b070712000c81314042c0074250303402c01c02800c918035181c0703d40b94a0010403100c1c00403901d5048105001a4003080e41c07601e03030172450030744488025011002540000030300c40700203000d0140d030064800031102c0ea036400d016854154035580040284040c61225a0a100c0c90b0107200c140180c00040640060a603aa0700800c1510b0f103903c07551505c100386200300320840055514001030381c0c100c03180c40c400c0414075001c905100b1089816141c04825501c0c201100e503125410022a6040541c40755800103500255040c4080c0380c001030301102c00244400011110581061042d80c070603421103010607840b4600c1000c0c1ea03140c0c0304c03045054116000440120342d042c080413429407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 705533183 1250 705531933 705531941
    0x10905060907270207080d0203010f1406090d05031e04090e01060b0f0702220e0d0e01020a0f3011071410020a0606090b0f0f282610 58
    0xc0e075052012050400c803002c414014650320702c00718a0f41d560034032201d40040e042000800361074410090258481d41401d84400d5020003da002035042248012000c0f07160702d402c420703280004030407980401050410306046045100b84c0c0030300b00b819800f0101c1303c01841400d80190055480e0880f04004224039006c925080740e0960090b40c0c0441c005100381032240c3c0078a4024194144080c1121442d03800004820310580b10001c110420300391034480002c240d120030490140c1229861810b45080d00c05040040d4442540c0080540000641145c0c48144142035041100c001c6003200c0303110040072841441450f00494a00f0900050058958044400000100031007600c0e4402050244610b400c001c21400b018425a01341c207500a0059201c081062807244200401c462440860f0782d40d00d10080000c0282e400e002c1ea84548804511103400f038580d28610f195100070498200d02c01d0303d00d04203c58681096a0110040c805060007481281c2c2c140180c40401c01504c00448580b4416540b841d0295 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 705534433 1250 705533183 705533189
    0x301180b040e0c12030d060f090c0c020604060c0602120f06030f0a050d270906090e070e150a0e152e1b15060609050a0f0302010e04020912010905060907 67
    0x43c2d100d5181a6160700e440c1d050b542c0c034030500f101107919101d90802d0400540b43c4551103a00001c08030f04003000250450302401d000000540751001c204842580001d2260281c1d001d000100244251442c080006960403030383c1070480760070004202c1c60078450103007050a00b12aa18080d004102d0782d140f08440000b44242e0803075202001d801d0003403100704121500501c009010203e0a0310f84110503c030b80c050880003004d445009008240681040140e90540e00825130f180c10992103200d0030452014500d42c07a03500f100342d42c0800100b12008800040c5800c1e00d40c0c002c124100340c044c045c0130428000e410092004601506c4400d00701602e080b01041005403d482402c044111400d05502c152207004218900c0052038007480c0d105e0840e41f80c4900e01c12115600c107405075a901410321259400c01d404400418084580d00c0c522810319103640c4a80d6410302c0004d0600101c5403403102a55241d8068039001c16024003410509000440035601810b52204c0030341e07590084001240c0000c0001c02c1403002c3e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 705535683 1250 705534433 705534461
    0x60609061707140609040b18011a46030f1104051e01020f03070f061503050312060109051302180618091902071412040e131104020301180b04 62
    0x250540814464145d00081c0502c0e44103541e0404035000755200c03841e10001c00051909800c1e190b0503e101e03181c505985e0f00314510303071043c14003444207000254040514078925010784552400211348640c0030120300f0060221016a80303c01102c00307075078035a21068210480c1e51040c4201607000e00020018400d030b018464118450406040c5d20b042d25881b6010b0080c1e040c411518030800390800e890071a005600c1c00c0320000ca82c01d04040502440e80140030222101b1031060415500c1e6980d05030340c900c12103400e01c503034451110000d0300e0707030713001f000004010070000e0143c0728002840e0458400a500c28049000320484c010450101414664280c510b103032803c000e07003243e04001d83e0420200100040403141c0309500450803000002541c0090104540303c0e4180b4941075403101e031846e0030f10300403ea0004050b5003e000030000582050a51600a01c3c2100000318000d49410140ca00450a214581e00720740000000a021410082d0101d040c00b5821410000c840b9060104010385130840e4088030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 705536933 1250 705535683 705535709
    0x30207020f12070e0108030c0105100f06080a2c011401050f0607050307062a08040308070509010c050a0b16140d0b1c0b04021002010e0d0305090a060609061707 70
    0x441c0341000300302100600d0788581100c502c1a590a50004442c41c240c2081d8000d40010a6090740b0100900919411032416142007600c0c506081a540400810348900381c100f1400d00c1c0810040c1b201a0300c140f080040c1c9a000d010085170711018410103081010601c1b40561070401800c140c604600c041038181d0305e00911204c00004403004000c82038002e4101502c0d140420403046000903190b100d0116402006000070140502c804021514103090306803404c1405240010000007917480806940d002020303042c2661543e2040004079001c03c26540001c03c1441124624014880c180403070078030654078003880c0c8449820041c812190b07509802442081c04200f4040c40d6062422030300304528510025241c14542c5000302c00400b00103d40200c1521000c56040c00d000c15410510101070076400c2c0c90000740f2100b66005207055450114940b403070101a82c0c2c8000c00d444030f0007030052025a81d00408248280c544415900000f01821712416082250001c941e01e420700700812010103e80000845034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 705538183 1250 705536933 705536959
    0xc01260103080714010506010816122f0f19090e10080d052107022404030305070305061f02070f030303062303030301060e0a03020d0609050606040515010e060f0406050307090603020702 81
    0x1211140a4501c0c4605201d49032f050340c642880d07580700302d00f078104c107a48440c640a214205a040d000848502c1c1001c408000c10450b40c176110300f00d045038034620b003409040c0341e201c0983c1d00448990065400040c0140c11a90900c030302000045088002d841912041d41c1e09030361400401d0f203941c0300301d021185403002c41d0000000041c0405001c40e07441142c90050301c0340e52110590f90065420780c18202d045818082c000c0c0300505501d40308403607010409041c10000307801c10100103502c0b882d01100c1030b040c194803100c000302c40d940309021000013806007402980c0c20310784034074001d00a09902d02818442091480848451041c102131400002201030301851079a401c04104540222000460a8115a0007100080107071141d40248241c18024540002d810001c1e25044e400c2c0036010f0865032141707041c002400248503401c42c8603010350000742020209a0b81c0342000c544a4000c0c480c6a00c420b2001080c0021016002801103120f01201ea560780c0150b5125101078040303005001d4081d4011040341c00305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 705539433 1250 705538183 705538201
    0xc0306060201152603160b0a1104030f030207090c09031a01030206040b0a0309080703081f031e0201110d0e031c1b030c02090408040501030609020c0c012601030807140105060108 78
    0x1000a83c0e0444010342c00c1440e41c4401d051659103c1c2c02c2c030706810806c0e060041d040c0007400c10420381058041505100e06d150918810302180260302026008007e02d6021008060003042200300404000c6000c0c0a84102250060441d2885100660302c4264070b010070405628500e1403503050340ea004041d9820a42840c02010041d000384d1001401e1603035460411010400c040c01800203c0e21950303034550325150281c081005200e00c41c81080305c0300d0f41d0080500000d10112500c0c2c4424950a84e41482044140012642880c40440966990054130241e102482e405051903030382c460141e04a0b06404824014100c0f41d001e41443d680005e030180903492034561205030740049140c081c0c50318a0000506400041c4002c409039022500ca20000408000c1540c140c012007000301015202142004010101c041d180c03402090003504000c80c10000e81c0b20000f1001011211429000065100d5a100e00c1c0004080d8480201a64044d0303064100e140c5904050254601c40d441c180d407600d20750340f00d90301d038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 705540683 1250 705539433 705539459
    0xa0503040c0e0c0304230d0302031b07080910020f07060c0f0204050717010b041d07051c050a050a0603050d0e01050d0f05180304030f14120309010c030606020115 71
    0x22035010824810000b400401d420700280105048a0075a540342494034005040d803c0060500d450070f840c00301c40c4140c0000100c4c3d000780200c59400c02690f03030342e00c2c141ca4031b03074001038100c2254481c20302240310020300024001622800f002510031400e0700c0c2c80740006a0b034909035440c0c00f480d03507841040c083c0b250a100e0784c24940a2446000c1c00c40148405500040a603941116150001000d400d89110b40c00441440c050051111408a610b40703401c20400d203401d080c1d00000310700310314501c5010400d1680304400700d030341a280d004800104401c00c0c0e054080908025208842d0341402c00c400300b80c1010301c0d03106e0902101e903c0790040c19031340d4400b130064a148403c80384036411700509110101428030580503021288003444030014003483e200b904600240c0f00c840d8107032070b03984c0240010700010702c4940805450b10f0f081551000b000b00900100c91400004078415042d19034080280858590f0540040800082c10b4605100311512113004030b003228001c801c41d650100460208020039248034031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 705541933 1250 705540683 705540691
    0xc210403150f0605060f122a090607051c09060503160c02150301060f0909020310050909010b0607120318020303041503091b030c0803030903030c0d2405030706050f0a0503 75
    0x380032418907a6000040c0702508800c0d2400300c1d00c46e0004101003d60100d040c01d80d0b1040081020b103a6450801c01240300104c0001086c0a00d501c002a920580c5e68450050301d60741030744041261003c0700c00c100e110102c00a68202100031419004002c110240140300780c0303100e000c034806056024a0f519104840f1103400780405d03038003c0500d0988d8800002000019806000e040e12210662042002d00030188042a44400041441413080c002d03429180315102040b910100c8400c041e544030013a040d401044c0040c0c40e264080c100041c4002000030303510030310f8181c09480e18100320414040f014103174150407045000b03505810400c000c1c04412403000302c00710382e00c0c160314000940c10f05541c3d441442d42c01401401d001403034980020410401410380c404090032240024604504025404e01c1e40c81c0005844c40c9210403000c55080c811401d240e200100d181044010544050352100b4508155003050142501074024a000450054040d1048510b4004042c51142c5080703066641225980c0001e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 705543183 1250 705541933 705541961
    0xf03020706151401110109350a02070f0501170c0307050d14060f010903120f0507081c1b09030227040302010b09130203031219020c21040315 62
    0x92038405030305041e4502c0026110090280c2400d00030a00050b0001d201d0110120305681841d030000001601040001d50312603c0b12803d084038044800d0858000c03403d003c01c9002680d010580c0c06d660345d03000803040c00326070103100900340060b1581c1c011075400d0405a4007071400352500001c211504d5962004507071042d05443c2543c1440358502600b01078801140403222400c1f1001e0920000c0c0c5003403185001c009200742040c58030b0034a107a4511050f21001000b03101400105900144464040c00071102e0207540440010f03547c01ca03402c003140440d9070100540240a00d0311030350001c885030485000740200c8280d01c6d1400c0ba03c0c5941c1c20030a401101440c80140ba1690030b000100198505080b01e0240e84290004904800004240240854001d08490010313a004a600001d6203020085403c20010501c41030750035a606a11061f8240d40c0304280b00516100040210f452032001c501c440c0d13000300141c10324101859a100a031401d0045000140c40101c48540b180313081c0c18698400ca01c000800c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 705544433 1250 705543183 705543191
    0x10030e0f0c090612030304110f0a030b091002070b0114180f040b01061103040b0918070801060e0306150111010902031c08011a0324030d0c060c11060604020c0f061003051c0f03020706 80
    0x1103404900300381026802140c0020f10f0cc028001803403c14402c0300a01d0745c01050450600c40d154079100d42222040c07194034448580341130250f4454a4124008100300078814500d5050308040d03507400c41c0035008480983d01d0120315000030400a10a0b0b88100700204200f0041d03040a05081004080303a1000c0303c940d9000c0071001040145006005440744615403c3d100c0307039141c0d85401e8000e80f114880404051081d041038080288140b851003058506441c2880d003c14035440c41d24480c0c0c014034683c1c0b00a5032511034813840030310304500c08022404451141d0b49450450b40c0c1d900d07520044410f00180341c42c107540203000280b91360554020700301684258541006024030500003003803c00c038001c050440011070320380e110400d111550143c20510340c41c51038141c2d5840c14942c0e58079100c000240c4132620940d00016400000c40007000304d0464043d244013a246c080c104800c2c00c0341c00c6461480203c0b036500a000030b400541104411414031070905444045000301400c80850081d402060101d600a540d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 705545683 1250 705544433 705544459
    0x40b12010e060714070215030a020d1b0212031501050903120f09040606020c090a0e160909030305011d1b0f031806060a030c030210030e0f0c09061203030411 69
    0x2090040c5005007681402404403801e0240000707081002d2070306000030000b410401600103841e07139141032078a4206041c4050300d90700d0315888c11000e84100c80d0b000144504122245196207101c65498400d2903013a001c84101e2184d1070380b191213a00088499003080c015800c01480c103540144014590804010300f56101d80c2c0e1128109506131304544401c0b01c114501041741c2d0400e081030b21880001d446c43d030005240c01000040080d22440000b8170302c0644546401036030200403803c001c9080914000d14070408926111422000100325039581900001e0501e4000589940c072413000703050303016801d801d101e65681c440185481d50800e0403403000e15032404020252a4090560185015460800607442e010001d0f4541c1c0c1d1900030090007191003141218400c00000c1c1c4004d41c0c50b82240d6050300c1c03c40011512071000d400034008009424840e01900c0c0301d0500c8043e001c241c08880d600103c98040064507010184450603c01410b000d069910030804138020454600b030301000342200a11031a903143c0c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 705546933 1250 705545683 705545719
    0x1e05040203090f1006140405040506060f040204090c0c06051501020a03030b1807020f1005070e0d1506030f05070605030708040602031b040902040e0a1104030b0910050118050a1109040b 81
    0x1407581d8113891950b40b0b080a004030480c1605040103840d00700c1c0c0502203030515403145603e9010107010309206104241880c0c600f5143c5805480041406250401c600035074500040c144e00c0f2078840484003075150000041a2541c40d124100d800c1106034020841050281e40560003001c20507501a4480c0003e07a0441c101c1c000700c110f00384030b05032940c0a405040d00301511280341c00d00650912005070b00707020070001c6096020400c0441030b9000c42c0c1d00c0d4042c590500300304e500c01c020705840205031403e040000c01440b10200428042c0d5219104440c0c0c0282e071050100e6560000303940c250b000440c44330104004c40c4280d00a90f0704204501048226403122022400031359020394005182e407900402d04208070b0141004403940200e886905200404451621f41c40c240308030300000381007000e00342c00314100358420046004480c1d2101800c200c5175844281e5031910140010240005600f0b210010f030b00d0f1040ca01540840b0b528032400305007040e4203c2c04000241800703410035500000380c0c0c1200d440c144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 705548183 1250 705546933 705546943
    0x16030b0303070c15082406040e0108070510051303060f0f050103141b0a060c05120c0a29010311040b030a06020703020c150d0c0c061e061e05040203090f 67
    0x183c0b144042c18030491905501114494614a004051040c280c0030081c40d1501002403c00464001003101203544081d40000d000780203d812070b03c109003206001203888030b0009105020f0715802c5607401c1c154045040100c2c1c00744680c220540703015004c41d404100003902c03a00301080d802c480582c04510b0501c80d0301d0a0048031001d910980d41303a60075849286412400b40044a11403910011041002c80030b000070802c0d000e600e104100412a120f502d0205014003071081f40314a0308152081940c43c080e40140030f41d01c04820a09650700b0003800303841c40807410f010d0482c1d20950710406185009a213161112100e200100f02c0f1140c10580320040c44500f540d0034000c90031400d10845005844401a08009152600584075240290003800d0f8902a08205005a40b5209204540030401c800090703401c4a0f000f5480000501ca641040755044204002c620a01c1404550103000c00840d44c1c0c944c8000314410700c0c100e8000046000600512850400d03800465002a83c001221000c00b02462814900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 705549433 1250 705548183 705548197
    0x1302060a080403080a090308060d2118060503090d0c080f1204110102060f04060e150f040b0a0b06040302130902090903030106090504380603150307120b16030b0303 72
    0x78060001c2104064001d104c3d10340084d42040204145061690060400d410180c11940f02d848a1100034042008031590701130f0b00e41e01c2c801c035042a2203440e84041d0005041080c1c20510800006d0086100c61041094a20030b0000e00010019011400010744140c074800ba8151380302e2108000c06c0310691500002424643c1402d13880d140d8038601820241000c40c4800e0300030781150000018054a07240c880c507000e4101390000d40000748404180b44052a000000718202c09010200f01007000f081e980340c07035080c402d40c0681071404a036501e00064104603000403000070741c009006d000c188094101010503800310031034200002815002500090003a090031200d001c10b035800000140031859120f1003d10050000740c80501002c103190044aa884250485104850b2140025441c02e02254040d22016800141c049992030824200107810f0300d6000015038024424090300107a002017080e688914107812402d0000542c50b20103240c50300ba015002000b040584440603001c01d65010b000501d01d03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 705550683 1250 705549433 705549437
    0x904021203190306050a151107030203100207020108060a0503120c0114041112010c090e06040f090605090d0804021503060a0308270111060f090f060103060b0114040312081302060a 79
    0x75a0a442e00c009080c0c40c400d41086000b05100f0760208a042c0340d0300080c4c00a0342880c01c05096025010900620704000740e80040c0d454807405e5511040917106038000c2460074000e81e651001c81e40c882c414002c00740610710402e9011750007500340c022142c4490019203440c641d0b1a00108100004111041400d8010b03202500c2104c83d0803181005485c0001e040490f82a0010007407281c2c2c100000c000d0320709643c52040081c07001d010400240143d8855122500a501d4560104101522420403100408080300c810070300d44181020010800d00071300e80c240c41507074000c102e80e03101a008990303103840703400207072156400100402c1b010000130840030240a140350f00700302c00c084240d0203a107039800b10403070a500326044c0200d10001828088001c546a940014103031240001754507000e0303489117802c444401e5410b150003910004820820b680e0058400e0384000da070b48044244034072141e416607201d0791000800c4503019080d540303200c3d0f0041d021290b1200c03031480080c1c8036460a40214005a00c088600b0300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 705551933 1250 705550683 705550717
    0x2030d1515020f0601030f080d09030909060f120602070c030c0e040501110c19020102240105030601140a090509070b0424020c01020a1509060e1005060301090b060904021203 76
    0x2211084405408031101101d2000f4a40240c84054880d20781e84107000c05010103a20820070800c0c05804001c685001e064034508021001460030001d0042405005e400841d40c203040c8000303890b60400300e0302416180140c010b0f1884e40c8a60381c3d80d030b00035400203104a49092080e5030010104541c460300c00020300d00403d00254520740751030300380d003101d81751400340071403110520000c00d0715007001030410550320200c03010343c42c640c0003800140d00d0224196051440070303060f423117228022000c0f014254122881503040340c0d5566200e06802c1c60524022000541200780060104070004107034111b550803040400540d02003e03110485030f00c060707005420180c91412802000540174a6900c0070403d960b50a00c058110040441c6c0000d4a07082c6005002e41520001030044510301134550013234403010703801075041000070089100c1c20307160501400c2c181c4015250400090440c10180680000c1c29480000154140c0d51482003000e150703000ba00580e0000c2a10b021059652010001000003551045942c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 705553183 1250 705551933 705551939
    0x80a0f05010303110106060207141002010e03030c13080102250807021323103f050d08060603061203090406030c14190b28030f0e0307050a1202030d15 66
    0x45e0039103800341c0c00401190302000040000c051440036840b0345920031603650b91028017400c812400f40c000020400c0300e9000020038005030068800041840b141041802d460156403514071500701d005e0b603010421103142c001301c001c07a2080c3c840d2010075164458152682050300c2c41c0c01007680c01d0b90607407000c20415a02c860056000002041010b1101c500d040300c88110314000c040c003110442e403031041d0f00320030220181411a00301600900048540450005c1d00581040c84041a00d01810002590341e40100031140000a00c1058110700c5188007030400d40c44c43d12210180003400d50400d100f07108900050100c81c50f556600d0103494000d50051003c80010350800144c51074090101030302c0c9125800c4030340c1c3c41103046c200034410412181c000c0d41d00e5448174050ac41c451010301c0c0d86040308030511545e01042c1401a0075600140607d100088208805a0354520385030f540d10501002500c00d50244481000250340d2001c16042c8228a1050701d0a080420310b4540503100d503454403803400c1d000c0c141d0138 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 705554433 1250 705553183 705553217
    0xd2106031a0603010203270705130c030605010c050712020604050409110126010509130c08032502011707091211030d0c02010906050906040f08010e10021306080a0f05010303 76
    0x280d40182c4100d000310300c5c5040c07400c4524948502151541c21000c01a40c580340e2202040c020307440200340151a00e0304035400f84d01c00800900355080d0000100b440c104011886512071158180840d034080010104242800c00001d0800450a4226032008041002080f141c46d1406010f24041c0b0403070713601040003410070024050303110b00107645510110100408012040180110741102c0c42603403040c01540310311103208191340e540400509141520200003504a50001c024216501407050304030408000001680550b24030500281c0060f01d07480c901c034880c44100012941211250408101c596552060700f40e04291160040c0c420181c001c02d00c51071820140081c2986440314a045a004151a40043c06095883c0200700400c640407412001c20f4646100302d80c043c24001241045003642c41c0503440c0604000010a04a40540084040094114025030b10005030380c7c402c1c00c02042c2880300458030002e00415200546845038810700040c0000d200f8240030754001c1d41d03044c0e40b280455411b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 705555683 1250 705554433 705554483
    0x60f06020a11030607050d0b0402040b0f191e120902150c01060902091c08120103110f03010e071202030a2009010b030105010905040b180c0a0207170d210603 69
    0x100ba8002d0700b0110400c440158007000f1074418044034440000c5a00081000c10000e0190782c1000251020001d016411410080302410b06400024502402a070302c4103011500440c4018928000a9504840080303071402031341940304141250000251011a540008a64001c0c070041040d01c1000001c18410300d5100303000e01000740051003030035031500b21f149c4003203075050085007002189070302140f130700c3e0040107160030031145c160743c82c1c2d40001042e5850f0300302218848040554030780f040710b4200a41d07100d4101801000440902c21001d4050f03107142c0304482c030304881018400c070b03810f005030301f146000030366400c5604031030040e40501c0c0001940000140310070a04180c1280070103040500042001c0da03448408081500d00036900813070f0752040500032918101207080c5003c006c8220008102c41042d10030f01030003c1c2c0580d07501300c900083e41c3e8070001d00384403541c04400c01c003034100c09800707030805014255000d81c2c0b056400744204210031040703207082141d11320380088680c0a06042c50303c0f20080802030b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 705556933 1250 705555683 705555713
    0x303180b15011e030509031209161e0e0712021b0607210b0612090d02100621031e020f011401051e0f030a1a160f030f060f06020a 57
    0x3004a048002d07070003103554620f81000d22a04040e11900040c100100900580c1c11404030038143c4017032030800c401c801340c4681d0314061200640d08007a10000d81c81c05032580007880213031008641c00200f03040034004480d40a00070300e5801405403080340740981102038401860401910204542301c09501c0c5542c600740580a410001004210b00688100600760004102c41240d070b4580040c00c401100d010405900841c1d60072404c00351190b0421600410225151a81c44869404d0314400c45100220000300d6142d8081c00203a11030f00c210084280e0200390110454074024181180c120347c00d00050303240035840c040710303900680041c2d120b1030b0f01c04424040c0742a04400400b41000940c10300003c640c104d1a4517000c40014181c40035910501d490301e00d090211054003800b41c40c1a14a41d0900c04281e00b045410400c0418002001440104401420300f80711070319503586000c1e10b2000070040300a0418141c128965030303a12480020426483c030b05d44801014513801078410422281024049240041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 705558183 1250 705556933 705556937
    0x30806090f091203150a090b15040b040302061614070f0f0e0604020304030903050106080a0212070b0306131415010f031e1107060c0c0506150d020405040303180b1501 73
    0x1105110500b003002c5402d00d41010346120f000d84139600c034080040c003122890840c94200041c2d1101103030860f02c0781c101104c04003041d100886155140d42c80010248142d1080b54036941c1d050101380010301c0c0110040c800e0381c0e04604404000b6040d501d0b140c41c070600184c0c601e649a40528010000441e41000c0f19004003004c0202c10040e52400100713505081e0020500c07440f869000001070201030255100e100990341103030003000655200c04e1481c0e51105982e905a11400d80c0b0246040f10100000341042030311f4480c2d2030b850071500e0303800a12100103c1820b03106a56500d40200d111010041081e191262110b4844551a42c0e00c5100142090b044903031020101410314807840300043d4601001c580b00c510505000500c44518045103141f80194080108074508160100f17594503844590648114041e0045d54071680720900b4100c2c102d01c4809100390030444019041d000f503c0d00d503100daa4002d000c0e0402260501d0302d04480c5d02e403c00525812281211207000340310300c4800501806c17800903028 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 705559433 1250 705558183 705558211
    0x311030f1c03111231030e030a0501050702010f0b12030403021507060c05030406050c131a040906090b0a05010503090a060f090b071e0c0b04061104050307030f030206060d080d09030e060703080609 86
    0x205c6582d5004d2a84407202600f8406450000030454800300290103500c0d4008000300240c0c2003100c0000c0c003030240880c1842840d41001c0d0360400314a003014020401070841c80096113000e10315401d1020b1070a0010142407061801e002c41300128103207001c0c2c1c0f0321012495440c0c4e941c03071030180303090821110082c008d08001d0000748034204000c050752403590700752180d43c04203404118010880043e103104a400c6200141c0c140300c13000920410641140408040455070104140e40740c800440b406e00080758018001c4e402030341c0f4000442c45640c05003411120442000c0b8507400643c03240a1440000d9959030300043d0b81c00b0340749803000c10060800f020100d03140b60400c18030700b080e00c50501c006400745c005081c15a0f11004101070b1210801103c00a0102070f040c1e8004d07599034180704010040ca0705041d80580a02000030700149005954540c00301e5004007040c1c145500380021100424681e01d08600384580e03000724805035a21603001d414280d100755100131251820505210709400c003e410018040c0303a03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 705560683 1250 705559433 705559501
    0x30801090b030607210c020109050705040504031d010903080c160806240301060f0806160305061f090305010237270509010b040311030f1c031112 64
    0x1084442c0c02c50030030b00e8085d00c1c14501c0ea603626504100e150a07881d00c00d01d4034050301015034043d0011041c40b4058002d41b50419a65000d000c10768a08440c000c0c002000c0743c050088241496401c3c0b50010b9041c5400c1d03500c45d44aa61381c0c002c43d4860080c0e91517607401003400c0461a0310b403640c103101038030b281d4000d069941824190000a2007403500c00c015410107000813081700761001d51040004000d48081c44044a0350340050320b840341c20580d000741809506580340c00c80280a406031500441001c0c1500c001046501c66101c0951040031b1301d00d081207008200040820f400740050041801260403115030107000c40c003510322040c08402401114094059074200058000d20720303102d0512210309842003a8010a11000f401089030405c0754050181000812010305200250040c0c920034081c5101c0d0755449010142d489082811013186940f185201c0b820b82080c10869482401240c00d001c50340304d0603280d2900054220800c14108200b2300d104010f501c4884080006001030612000e0424a403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 705561933 1250 705560683 705560689
    0x100f060306231c03030b0603040f030809070501080f040204021209160503010b060318120f03070f02010e070b0c0309090c0c12040e041106090d0b0f0705040602031b16030f030801090b 80
    0x240c0074242c084942c6503103d4401414004d8014032002032006002c42e50b42e242510704922480d03403100d010740000d110b050010314000380003c0d220f07055940c141c4071b031442c0e82e80f0740300c00138401000204220382064080c070600121582080080e800b450039a4080d00b400d900c40d4203d10791142855000da0b1181c0c0c1860702d001d515031104401c9907040081a40d044401c2d10500c00e18a181055002500100010010310150a00502c0f406180030340d0040c2e84486014903401d40c1242620100c0345483e04a400c0041e0070001144c3d0364000b80b58061072a81030380c0c1000c151030000303400c4600c00c40b142080440005462050352201740600242c11541d55142c03410703d41032200c440501c00340180001c2c1000d0107031008440a64440080c3c8500902c0100000c00360f86892405070075035001590942c40783e0315030030041342045000f00203072004e03a02c541e40114142000103030f148525202d9000d462031140030320b691080d54400240f0b80d9101441c040d2241c4100503401b4903005220f403030141d01c108a01c91410040034001c2c1d03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 705563183 1250 705561933 705561949
    0x3020a080a09031107030f06050c0408190302011508060a0e0712140304030618060e2817040602071805060105041202031e07090e060402010c0b100f06030623 69
    0x744808100091044143c9070035280d2030000b2401d5403261007000800020003041101c4142d01c10302c6000b0910968070f440b00180c01c54041c90240807420340050844d140c0d4a84002480081c1502074400440c1915009a0140561038a6041007401d50400d50800c00c01055130b0141c1da4903a0182802868078a2500325a80b07500600010b00401003041c90b040360005c0403040060310040e5030044002c1042030f0070031021000c407018000048074150b050035403002e24241c000c19980075032450351b89014614810f0340740001c0726440103d02195854070420482c3d0342e242b0490050000703044140c00a103242400c04901d90760640e6440450440350707042508110003a6401015a81101c1c4d020403034422070740c00751000a0038043c00410400c458024184205079482c1c00041c810308507001c0b800e040119580c0c0d6100f060b2036075000c40b006030219070014a17040c002060254826484481d100381402c2d410344a46003100c94005550111000030b0301e0340428030108801d0603152055a00103400ca0b90400c44c0100458904 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 705564433 1250 705563183 705563191
    0x8030714191502040e0a0515030d210608010609020c1006050307050103020307120504050c12060609151f18050913080306010c06060e100512030d090609060509150703020a08 76
    0x2c40c10920400d000c407064064502802100b0301000c03251404c450380800905d0119800039001408420700901800e0101c3c1c10b688051442d0748409410303d0008182001000d10110604003030b80d00e110000e000079083c800d840c0034042403c8056aa0354001045919180a51b000302000794a0508100229070b4001840401c440302801d0160712a607551000b5186505060601c82e216400c2c00c0400c010000041440071703221008546100c200c0c00039000c020360750030046a1403034200c40540e010403040100003001c0191010300811182440039204500740b507005404080d4408285204007408002030b41d012a080500815241000e80d890040d204011203185440090102d200010220741319901c21004040d10b00d0300001c090208075502c6202c0c80740366408232807080c00c1d0483c035000860b1174541002c000ca00f80f81090001e60030466201054030040010000464059541d000b1410000703942c0c0c01200d204a03c1040942510448103014003408580200003030100b6104101c00090141c00010250704 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 705565683 1250 705564433 705564443
    0x1050909191b02071e05031902011d06090d05070b0a050304020a050d110405220510060803040f030303051302041107020906040510030605041e0c08010b0102032113020a0803071419 79
    0xa4100c0817000007040646400998141c010701043c2c01a1900505c0170050701c42c800e80e030300d4440001500b4011840160310b144294440c804004240c00d40c0384c0402d004c2c1c4d005004c0c405940c4095a2500d40c448142e001512400c0420f0707001c000c0200350700d08110301e50018a0f082e00c207048240780725510fa20f1a9402e4406440c440c07a80e0307002007185c89a2900d165654581c0b46110085601b50b01d0419998415080039841011800d000c008262018003005880c06c0341c98041c03595807102e042d0780c0d0540282c5802408616903a551944000c003680e41c074010090b4810354184030aa44140500504c41e107250300511090182d03080105111040003074800c100110b0b074000e03100140ca51654980b1007401c5042c43c0201c9103401142080c80240208003044100701c1c0c0448000308900d4000c2001139840f40100340c1038400d1200180c415481c0d2040114030654402e00c41301a550200416038001491602d11350800c51081c0c0c0089082000c02401201800309013125800070710b42814480c1d9403c038011940000100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 705566933 1250 705565683 705565709
    0x1090b0313050f152d07030e121c090201051e0f030a021308060f0103030e240301080705090c07030c0f050f0d0f051306050901050909191b0207 63
    0x980315140040101c01940c0501543c83d485002d50640d59220a15060320405960b06400710355440100664444990101c0e00e032960942c0d142c59080440950050083c000d268448081c905c0b10381090010078000110b00403441d4641e40d80000c110702204540381c5403008541360589000160782c100099a0b0540d4030444100c0c030f410804040120701e0700900c140f0b1051100d000c82445141c1074203030054460190b14105003407400d40e89012869450030103480b8140342800d0341d001800442d10500421400c0341c03015101800754184a49562801c0491240b600604c4c00080014080d448080c0400002081c081781d0301819030a0901041c02ea92040342002018852150040390420035401c81070804681c202081c2c1d0711803101410307629200c062940d04140014080307440554582d01900c02c0d04c00c010f01c03e042c0304074040d08050f4190349d9a0b0003c240e283c107000d428442008071759600f00c10140700c0d044082c1d1002201c01185559816a803035103603044038401c0701218542c070781e9600040407412a4000b0903404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 705568183 1250 705566933 705566941
    0xd0e190b0703080f15150403080d0e280605060d08070c060e040b010203040b0706090227010e0403080601030908040f0803090406080f0604030c1a04050c0f0406351e0c0402070201090b03 81
    0x11400e07c1030764001800203c020a503844401210341c0010700300c01c9404140c442109010000340c41201080301c001947c603080400c641c1c0850965404039a00c800c010b4003505410109071100807840e00a00340441c0c0b1305d00b110506002003907122005161f0040c0035101030003070803a504000303902c1c0e0065003e0040221000300c0d40c4400c4c0f0030142c0010b98080c0d0064089100445e18410b244903d03005200001c0706452060000070342da4036404541441641c245c2e58030322031a1908801140501079480c01954801c20030311000c9070109501820b0401072400c00000c2d0390300c1780c120f001e100940b00c0c4c40c2d211f15101d810441c8031082003400450382d6540142e061070584e560008074913180020081b16000e640c00e002c80b25041100700480040d00c2d920800048403a8405241d4140400007692528018902802407410303864200d481a003505404018204403a100e405910079a0b482c540042685141d0900a1408480d03400d044140704a00401609850a6151085503000641406514802c9100e0210004005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 705569433 1250 705568183 705568219
    0x40615231e2809050315010308030907080d17060616230d0c0308151c03020a05030a08010303090b0403080f03040302011d07091401080d0e190b0703080f15 68
    0x180c40b0b80080a000c0d841d030b100807414065465212001003000304140c400c020999150010310304100840d90110500c15a09640e03407564a500098010051880307a00c50111321000c05001ea02030801c0e547e035a00c90030b0000e40c0380c5441d214801500d22401408100300b0080070b50606403802400c1904488901098100315400d000d040e25005001c0da086e000d0407003e507003066400640b1101484c001d036100c01280c1c0750042c291240401014000341e0100d60410010f1000301d500e01c03400e603410f00a0064405c0c114040d200d490641c0d00004003440040c030201c00500405402c00b44071006070035408882c50505041d583c9072001d40c41050201305503504040000f5040501c00d4200d80c48002801441c1042510400c000603583c0c1194098503100c1c0e800c01e0140c42d116081b10341220304a402e088014050014401002d8902a0810f4800b0341c02c50b9005803c1c044420880c581c3c0c200030810340c0d030210342d510034505004140e2407000c4d241340503421142084c002c05c1603140d48103494070103040301d041c42050341010362 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 705570683 1250 705569433 705569437
    0x152306090d05150a0c030b0a06081902070506010f0e33061201060f02120301050d06060e0f070f09060804020f12100608010609060302060f090402040302040615231e 72
    0x8001d4410020140260312182c0e802500402c800349003400003001707888054041d038110418140d00301d01000b070100481032144da815900300320f03041801c900c403122605109c0240e074421b03801a0ac3d6903004100400801ca0f00c10b2070300005100070b444070300c1d840c18a0b00301d4180d01c81e810a4504041046a68410100810030724150340301500207280300d070390b00d020741d203442c15440091082c8000703d1030103000b0b200700c02e0004c62180e042ca1401d503074451840c3c0c200010030070740c101c0324501510744690303070000401c4502040703543d140141c0e00014202d410b450101802080ca2051400390020820000c000b00089a0030006454005604403022004801d65001241010310280300c0100944a46d6044101800d882d5201d4801e0315031403c000e201c29515800c0440a8405a10000303412020400c1409504400c107409842d61005c02840589419669000901a901280c204108a01c2c01c2c0c0700c00d01909070000700303c0b40440c00e41955140038032020840501c19010b019030404500021100c40b80c800464001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 705571933 1250 705570683 705570709
    0x3070c090c051606090201141c1505060417060705070b06010806010201110d0605180705160507090903080f0a0c0203040603230f1b031003140c0a0915230609 69
    0x1041ca00745607410904017a00c40b28005070701042020300c0301004000c8002c101c0b4541d071040c0f90943c40464010f01603100410b1074138001d6503c221076031004646561200020002401d10b1000c41300064655182d16007025400350044003405400c21000002901c0042034590017602401e101103a5a92540180e0142600811829880100140c24004001d15a1040080e80c0017903c1c140901840441510b039a0314042e00d405010800522000281d0400f10b0300c55020f5030b10030b2083d03c08aa50340c603041d40659004c824210003084e040000c201940114461032a032081a40c041480400161071000c1d4403840349014003410546c0311448800b540c0702c84100214008c000034000e162074a0000c81540416105586170f4070845100c0201c25086054041076070300808503503185101e0741d4510303a1911100d808851002c95240a0100003040700ea881181540040c4400200420040d2003500d802d400c120154003d00c44c04a41c40c5001c0c0c030036807801b200d800751a000030b0382d10556845002c8001341c0ca500d0242 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 705573183 1250 705571933 705571957
    0xf0f0807020a0b0a020c302e0b03010212010306020a030e1902090609160c020a090c030912020a0519020d08030903070c09140708150303070804051203070c090c05 71
    0x303000054030030b0070070b00401d452131640d0300360740c904020f1408100000c005103030004e174601140f010314031294144000b0400040308600c11210b121080124204a02c803000c1000b103140540d601600014800a000710355540300e00310021480c01c002c110410280c0c0d0011301010344241d0f0701040e000e4038180241d100c10320300c1c00c038081102c80c020310b07040d04003140c030264000c02c070301400000700860351038103003508103034003448103090b00d007051b00c88056044404414403002030342d0100f802540003842c281d13030744a04201c0003020303a004907150516083c8050042225204141150700130303101c00003c954003082440c01c90a9040d403d1003021214000940d050780041c2c0042c200210004c01d006114200100800e240c41c803d120f11f03060341341e89003014001c41d0400b203a19417524900b4800119007500c00d0f0b4805922519001c80030300e00021f0203010901e507030080c40c811514014009001d00c418500200f802c13000c10b80c40301c019860301c10541c2d038000c1a24400d01c200340146440f0032041e022070340141c0540f07140c0c045039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 705574433 1250 705573183 705573199
    0x117031209070b07080d200d020a03140406090201090e0c0d0f0b151c090b0402091f140103050a0b06090d051f2324030c0907050c06070c0f0f080702 65
    0x90405c0c1085038032000c40ca00406283c140c010f00c070903841c10301040c0b40460344c440c4c081c03c2c920101d0003500a540300c00c45100416594082c25030030302d40d02e0044180200d00850000035901c0043c0300142c4209035a0f0401040e2018100c104101c41e4114011108400a103860104420f41114070a50140802100311903115035a8039003032243e4482070001d0b100039400601c42074a001da1010080d0202d50b50b800c4042e00010300e40c0d0000d00941002103103950414a800407049070b018054640000c00d5045412028000c01c555403071400941e0315000d015040060040d08200c509100400689148a9080e509024510b240e0600047c007100344001480711170741c0400c5c1c40e031040100110500a20f0030003618044c4110b141e28031a4561240c214840c4140c4103101350030f400c0c2c0b40c0c07114800040c024002c550b50b814800c2000080700d9403641d0501a000d000c891301c61a4031001d030007076902c1c05e0020007401e030b40030001043e001c2d0010070b070b40881c0e0600c0150400710010250481c0d0801e81c085202d8110702075084051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 705575539 1106 705574433 705574447
    0x40e070206130b0106050f09090f06030c03010605420712170703050604020403060204031406011505070204050c0d33050d060e1908030702060117031209070b 69
    0x287c400e0032820800e0740c1c00024204002154454508601d0006000301d600b400c001c400c8205008030024403946d81000007041c0c0c83e0f00300741c07070160b03642807161140d16110403100000d0380e0701800380e407800800820580c011802ea40c4408411035080c14614152901148502452620340000701c48002590f11041c0c0c046015000107409164440e43c20040040028203910081000718400d01028603001a00c5400a00f4000141c1c400c1c0c40e5540d100c500d05080c10b600c881103c1c52554100c50001d141e845180605045009058143e4800342c130700903030205007012020700c011030f103a540007051003091078191000c80800b03114030809030000b000303000d11000282240c000101c601c4841e01102d082c00c0207025503032510041e044090320110700002c28006800da051180364090008003807144132000b0244081c5589100c2d10007a40401d044000c04106490001d2242d50020550340c0740300c1d626055 = true := by decide +kernel

theorem cover : BRFrame.Cov 705395683 705575539 := by
  have h0 := BRFrame.cov_init 705395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 705395683 ≤ n) (h2 : n < 705575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
