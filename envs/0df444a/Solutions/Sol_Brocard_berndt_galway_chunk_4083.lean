-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4083
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:30:53.481038+00:00
-- url     : https://prove2.me/submissions/f7e49aa1-e83c-47bf-81c7-044726aa9ab8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 734172661 ≤ n < 734352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 734173911 1250 734172661 734172683
    0x703020c1c0e0112110301050d050a020618010f02060714070809030d0306050a1d012714011e0e0c0a0207031a1512100e0a050303010b04060314150d020d 67
    0x2040102214001c066a43c04a141c1e200a840c0c042814040c0390b900e41a49000c05081d603291200300310f412003010380b045d202401a4101400541c03580e400a01d200f00e0010f03204a014110000014044101e0102c00c40854000ca0140205213034002c101c1c102041007540c4040c0c8698103030401c20558807c4050b00d6038584500c04111001640680140d0100da10440e03c5a075615928035410421002c00c0e03001c40d003810058801841201d5041c1074200001c2c2e01031a03540700c18030028260034129100d40b5204042c0301004001040f42600c0003540003141c01d0500c0410714440e143c81c2c070144070f20802a000316800b0310049050142c0b103208000e1b0707800564020101c07044400283d44101d003100ca0a592081c00840214101c111508090340b6080d103504900300140300c50040620a24000c04100c021580c60b1b000d40c3c811280401c10400203503001e4a5002c1d455940c440c038194001e41100d141c2c42d400005c40290208100315044160002016140f0036140b4900c2e20b0300b81d10005035840c40710340c1c008020210007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 734175161 1250 734173911 734173963
    0xf0402091501180f0e250503070302160b180a0302061302120607050705150906041407050604060305090705180106140d05010602010b240f070606030203032701170703020c 75
    0x107030400304840340c614600d41646c031903048441e0ba030320801c11001d81109000301440c4000d0b100384000d681c4010305180044c14140c002c0000070800310007600a03920840c48500f4061050703000c10001d0078050100000b440b2104841d90060344410005104140c480700c411111002d42d128235040507800000c0c14165201d034502208081d00e2500090415101d521941c40c04150044041c0d072541d014003186030040c18103a0700ca40c1d944200745041c1402501b203005003034000516494090180015003203a84010074140351050704240751580a50200d44521552042c50039207091800090303040d07441601e4410203080d040800c0d070807a0700c07900303101c2c910051900e4000940e40c0d5041d03004010060085078072050740d4030710814200c440410180c400380110340420900040c40b0344c030f00003130495920825002c900c0c0d0f5566000a41942c0083d0112511504030440c80c0038010424085001142000d00305600008040c00c02d41400d03050042c20074061550000d8528956003003003082985041c41d5540c007884100c22 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 734176411 1250 734175161 734175179
    0x6081b062a120301060914010905090a23060f100e0a1212020d050f0c0a0203030d051602030c10050403171807090b101422030b0f040209150118 63
    0x145001c0718103a0142d1040e16003001d001004580c1241c1142c1e03910b4000350b0a1041000d00c940b60012142d06220b580540011652141ea00c05d0b4410000c40e08006200042c03070583c155440c0c0104400018920200700700b090b50381d601640811131900a0b00d0440e002c005d40c08064618840f01c815040e8030a09144c00050344000740e00103480554494003c00c2d5519032400c500740ea582071441000c20103e0340a0021540403c00d00002e8031640607650210752030600142c020030709552200c1600c01245848604101c0440e048150b4900302004c24401585040200038403544c0340c0840440c0145c0564440303004c94280352159950b020010807401c00203581e810804400303121000d01c1d0340c918100d03008941d000104154284201c040c01c07400070f424a41a0902410210f40700ca10864442c960b0b49c2041c00304000c003c1d22084015079aa00051004600074218103100056800040140c14214010740c20440107859010002c1d4105410403a00e240002c8a2307401a0383d03016480d1f01800e06160060f07000503903008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 734177661 1250 734176411 734176477
    0xf050f0412120c0203150604090602040801020c070b0f070b060414091020030f0703110714070e0408120a020d0e250506180a0906080105060405060406081b06 69
    0x210400d10750114504036402503a0840d401c48010703601d500164015150b130246d00860560140c40200002070110544e50b0b40001ca0300a504007500985d07002c0398216145d54108404d9025003c0d0240144c180002c140c0402007034411103500402d01074a000100304143c4413074009501000c400c070b4071000d05280502406a8403c1c01c080002045070034100d101d010380c503c0b480307191400c224540a03646540e46000003000a450040d080c0400c05998441141c000d03201c0e400a81041c0d40b195681c051600144414139181040540210850540c41414080001e40080440307106826030703564880c490342c40008810081c020858a00b40c1e842c103122010b1164200440e0425070302d507040600d116070008001460f210600305000e00ba40141e41000f814800181489e26007590000003454410300340c0c1c80304002003d50f80c0343c0e804071020740c0d1545c0c00d0001d60700d418059241d1004080e1401c02c1203500e40502195902d186c40c11a03107803682d8403c0c2e00740715070b11050119581ca50f200503c1c4480e8883d28680050860 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 734178911 1250 734177661 734177663
    0x106150f051c0c090e070c0602090607050619050a0501060c021e1c1406090d05032203050703030c0e030c0105090d02040603080705072c070c060603030e130605100f050f0412 76
    0x142d41c0600411041410304200d80246c8450761002030200c12075807481c00a42c0410b0b00103522080520182001410400c0803e218503810011840e64901d104501c209440740036100c01078042c01c1000500c6001d40c05100c0c6c541064044403099200502d039910940c1807000c45a00d140c1090703100001c010480c111101688000d88030301c0c258090512485401034642c1e906407140800780c0c006103608402036224a015541101000500c003441c038003603100f01d01c0210318410301100421004600003060507010300c0303408000b1a590420311058440d0170002038461100d17079040c0341030041c041410290342c1c49040031500525400b0b00208131054407810300d1081c0c1e40120004446610440c500803601c071070401320f0541c0b4100e450400241e4008166411464036034010074160801101c60700d0000800c3c860700915004600948600b8040c170b01510501c4207510000c2154090a070030b1a400b00010b448440300055802c5080c1b400044e400c82900302105c1c24410748503a5880450b01203070102e005500201c00b61205 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 734180161 1250 734178911 734178917
    0xc0d1b080d09300e0607020f1314070806030c0901030212030405030a062f030609131e05060115021506121606030501061110090510150e090106150f051c0c 68
    0x5804040000c403400d8031001c3d03030945c10a4044c040310005040c50b4240c003154000007050322908405481c0e000084840c1800d1500942e4428420b201010350000e502c183c100c1c0c1c00790003030030100c203102c00405c500400611009005a00b00c211520030120203105490140000a042e1b804100c080e091000250608001c2c2824009110a25026040110184506009550103c18216914801000001e4100500c401c01c3c0280b101204800a83c0980030350303064000d441c030007000f90b8100e81000c3c6d1900307005030440341210005540081c112a000140251000520342d000195a0380305004500055030399006110a4894603410200c8584101c000005a6025a074100070300d03a03079401d0466420f004580741c900603030001012409079401d60b4100d41907150085040703440e4031600b040400115031209082410081e40c503c002c0c0300490341729031040d4011201c4002072040d44e08001d07004d00c541e8050b00c1820706214210031304150307e5004030241e6042d5941a01e110200f0410107003100d01406244d2580000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 734181411 1250 734180161 734180243
    0x1e160c030203070e0f0a090201030221150f01050d0905120304081e13060503070c14010e1c05030f04110a0905010801240b130e0c0c0d1b080d09 63
    0x8500200940b1303900c555403500c1582640e845003d404401484107140690406408000c9000510301721490303549090320400e21a0b0320b61802290303812a01400d00410b0303200d001800c0d10044183e07800020b450f103441d03101c8000980c0d11441e1412520340b80d84103201d0200490080100024000020064851195070011002c0c400440c003110303003914455580100b04000c04110284000c41c4102c000e03560007150740c00c1242400c8072a450300c4081c10038000342e041007a0345a4041414200040c006036401280c45a24004415102c40c00a8242d0000404088610101c200081d06218800d002e00c10740c1d010140542c002e484d1202985d5001d03110901400c0d420f9824006540e02c118074902412000c0920390011000550500ea001c0381c02d907004001454000b0961080864180c51080041c0e02400511560b00d84c0c0c0c1e5554000300303040680c024041d070309119039089180c01007200340440746039455100710816a03441c08191240c00a1260000103003030740400b465007181440218091401c02061001080c803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 734182661 1250 734181411 734181419
    0x306010603150f081c020c030109060c020d0e0a090504022403011a0703170a0618020c070b07050d0507032001090506090109150b0f0909011e020903031e160c03020307 73
    0x8807004240c0b20360100e0344c0c491040314095805171200c60008112510540703400c2c0440c0000642584c2c403001c420f40f0903944d122070804081c4d0f010010120440030900703250050649400c000740e00c1da81c0912a0403d8103440c0c100160440d40c801c000003040303043e400101c61700c2082203180d10b07000c0c1c1c00c01d028a07903400716602c00d49841c4901107015614141e6040d42d8a10755030b242c2800d01001c4401c003400120301c20362510310100700a908400c0c10618509002d50050301c50204140a525000c060b5103e85080001004140046500400c521340324080f02c0c10300641d22403807440e04480a01702e141302042041000c0d01070115081c0190031603680f0300d0050044649546614920354221001c1c030800a040003100034440c030100480340c0098005200080003594540740000200c1d040c80412202541141d41d40e60082024440f030107a16880c01701117410460400071281d0100381c0da8864243c012000255040002035a8054601280d11400b82c00710540040c0465140041007005140000c034802c4c00f801c10041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 734183911 1250 734182661 734182679
    0x311010e0f0f01030b03030d022106010f03020901021219120203070203070b040507030807080d0507021204030609020d060e010c080c090d0305030a0e031218060f01140a05030601060315 81
    0x4a040c040c024000162400041c0802c40c818200103062410325480312500c40c080e96040c0064000791401500259450b2800d1480301120001c1080840740400e06900b48040b0343d0380540c070b0300d19000c510b00740180d49109020040c0e162481035981d8074a0400c1c00500c0300604035980b40c41e0350b11007256441e001c81d070b00413800c1c404c0140c1c0021550341005034000c0c00350401182e081c900080d040b43c01b800c261880c26441e62211030280e8440a8141d416940000e01411103c201c5e2050551044a51000d40000300f80c0300707886001ea00c038074031006c2d0100e51180884000d5681b5440310910b0954828030800010441101450203402d001c0405130102d003a080000d49407400e0070040b10040310303000382080f90700d05042c0d90a4a00c0d0300068113542400d40d03200c02c40f820401003000103002ca0702d50070740c0c4281d80b86852100304c2003c0744240e104c400103810150501c04002c101009007815207500c040d00e003104025400c081030140586500556240c840d03440000b800d0790f00341d440982c4072041d507104810465240c0402c1c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 734185161 1250 734183911 734183927
    0x911040b0a0528150203030402030d0206040804090b060919150309020d0323041410020d020d0503090a171e0a0507170d05040c0602010c0905130c0306080601060504031101 75
    0x8280c01c5203400211540b4031000503c40c4045069401007030229a4803120720010001c00f00d40000d002d0f030300000a00041d481c0c20004c500000d41c03903100030181c070729041e501c2d40030754040c1d80b048905054441545c001c20f0381e142429a005040044c01c540841190385800800120b8036118200c050400310360740407142440b1307014848060750080d007120702e0b0705840d40d81100c03064103900d42c041c07004441c1803c00c815614044014001084401d401141400c0c5001c20484410200c800e081d0542d841401d03400328031500440c5444c0c2c413100d02d086c0544c490303854120752810401036680c02000420250940c45505a07403401404241c1105a0880200418140c10031341c144900002c12002c90703006e00c80308000600300c0103410801c01750400030900b448040800103007550b0065a003103915050108043c40700945c248240700c540c51161400b43c810a182802003240498244034007810326441c0c4e0140c50301c0600980107032000b48254022541d0543e542c85c0c0041c071507001400102d0302090074003c0000c80c4d620270115 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 734186411 1250 734185161 734185169
    0x80a05011406041a04030c0b0306010914031b0307050d0501020c1212010e060f090112020315070f2d0c11060a050405190e01092408030714010f0911040b0a 68
    0x2da2440c15042580c111000e2100c0c0400e4507401d0f008200110006400c0742414006050980780181c59040800001d0010100f0360070007420400d4031000b0800380e56000034840700040c0681101000c60642c280440d00b400f105401c0550001e203252068020400b056004000c1608a48252000360800100c100e2152080340700710030484440c413005100c40349405144642149c00289100180c002c018041424054260f206005000c0e2a0b10500e055040034058000389054034002c2100502e403c5c0e0000e4800b845120441007040b101c08a600c00741101c50b21500d840341100c0c100d094010440010040070100c070720303108a81c1950078900400c810f04000c002c5e10107202003a290541000d00700303c10301a6241c05e02038584d003480c6101c0381c00586000640d50050107407100202c08901c44290b00070284801c8500c01a800030411078a00400c8105d20101c295402a80c0c45145144c1c4110f00c03800c0b0380e01524070040c1c8524202c0c80d00558a0411a207500c00141e001c00554040c04168a02010000550280c2c42 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 734187661 1250 734186411 734186419
    0x203045003040e07020a02040c0e030d0804080d0906022817010807090c05091201050109060b040f031103071509030c0e060306070e060418091a1b0a0e10080a050114 72
    0x18001041c0035003d203a4855803520456240c81035039000281641c00e9584044041855802d1100300c03410180801c4a2202c0d26040501040c201aa00c40103980304a07180f002c4038a0340d4030a034004200301c58045822042e542510903114840f0603031581505004441c81c4404554010702e12000d0b101c1c0034480504031080c010103042c0c0186000302c02d00107001d030a02c5100420408000440050756842d4a0082070a601d4000003115810031440c0402c482d0181c010300007030001800100300200382d810021060b0380d481a0106008110b10327020901d00000d6400107900500c8642640c00126480464041141d015040040343c8940ea180b20741d080d000d0a0764540d130141c20107400074142030300403510500c200201030842c903e0309a6030139980c60601f980c82c0c0d1345880366444c0c1d504001403120001310161300d0307551480e0010803410b00803c03d44202c403c14541c1c0d40d5070000480c641011500801c3d0300e40303980708080c01c070280c2315a0080b0f0041950360100c0d028807000746064004071300c40c03041c20150500d45501030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 734188911 1250 734187661 734187667
    0x1080708190902180a0b0a05030c030c0411040b0a03050702060601032c0709020c01050a0b010504060518040b090124080c040b0c01111c05060306190203045003 70
    0x40030301010345891041681c000c843e0f00c0300001075034510704d9075900c21116540300155840880d000c200c2407d034a50b12403846039200040000241e540403407010031189003201c000512003042501c036060760043da4040d032000e0030b000c2801104280c141c0c0000740700780380d0b82d4255013295070307888015801c4501d1441c1c45030005030310300606401126103d5002c0e01d1080d442003142c9031940d0303d412400a0364001c20025070f650351075500307120104030380c6d0040803281c032000d082050406080100040c101d0154090040d0100701c1445145016161a07000750203800c000b40200b09150b0310b0383c1c5d8003804542e50926180d002410320f00030313583c07540c03081c21b891303010324404158149807d00e050001d0143c0d402040c0001059540e80840001e20700c0d500004058540050f01d56001300300d00d0f008581c2c21034000901d014000c0d0898010481007010b001c1d981914260340e240010313200c0e101c0d4140101d03600301075080107004140101001d40d003002c2c00a001e0551884444d02c0240507a102180100c8202c030132180035485a0044c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 734190161 1250 734188911 734188951
    0x411160611040e15030109081305090c0f0f0f0d050109050717010609090f0f051812180105070809041104170309090a0c0c05070f0e01120f03030c02030403170901080708 74
    0x3528114811356000f8000710b07000c5615240c105055100350341c480c00e000ca0000003005581807454038980c0c080b00401905082c05442004034086114051081b240c004000400c20032062589040e06c4e000342d441c800070411517850340703464402060151213907404122902170001d0311107481c00e0b40c5410b82d00d855480046a0b0b2900d1007a101918414005016264441105800000d01c42c495940310700c0780b001015010401485140d810b2804c510070040500d8810046410841e00c1040007120340321082c41c0080c4e0381c0c100d41c01d101c070f00f40c0214441d8a03806400c0007422040c214070080a0429640b17501c0d02405032940d003e0080c0da4034880c40035948d070000e641d400008c12000301940590074001d014100700c41150f001356074032800c10403581c1247e000510055418419400c003955001d02410382440100107281d000c0d00d5280501105200060405448006040e0358500c02e100fa0340c01160f0051a544640380345002c1743d5019007108901c140000c1401000803c040d00c29101c05024a103041306030348180d010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 734191411 1250 734190161 734190181
    0x8180c09060d05011a0f03060405150c07050f0705010306050f1804020402070506041a0109060e040f14030a1101230112240b0102010c2c0411160611040e 67
    0x401010a94003141030710100022800038010300385050076582e038400035201711300c0c10801d141d6041c1c05624040d42c021804c000c0003880c0054507942d05c0c0014141c81d51143d564461342e40161080b03100041950090380c0030408000d0001171940103450090700c081c000640c0760300622118400138450154011681c952842c0d000e28400f0501c1e400070b0010708098504512a100d0038070f444415101182c000009c04240b42c48408690030450140130740c548140b01c280c1c41c00c0050049824050005404c000400780e45400f003210f403005110054000c4002d4a8403044042c902401c44c054043d081c502035400d0607503400c000c6003a4406030503030ba41e0795003110843c0e07401d01138003200c841d050f91400c81e20100800200c603140400b480f0701482c0c00080c1c0301c000c0392061520000900303640c501c80b000e078180202003010b00160389c0c840480c01a8507c00c500b1562850401e480003401521254a084848950000341201e040d0f520074800c4202c43d00940003440200c6505c580c0f5003d5101d18404e168805400d0380c003140b08228 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 734192661 1250 734191411 734191429
    0x60a030b0108090f1b060412030c03121103040201050d09020a081e19120c06021b0f0106050306060103090c0e0c070c0b03010602070308300604060e090a140f0f03030708180c 76
    0x98090074036814a40c403a110500c2c0c1032a2310005030003160943c41401c0406900800d0b580c00324180b1001808902c01c580300402c254000500b00030b05000010031060301005450f40441c2090360010404a296030762280015112a0210748852140078020b20049019500041c006c4d40c1c0c0301d2a40b1482500a843d840300c1a540360003250349020004110702074408550203001038a81044616030003a03001014081043c03a00846080e101120f90415600b00680c1d640452095800803081c2408110840d06152855030f6070304503002401000c400d4401c0c04041040c26014200b03140c46442244840b80e112054008140030134416000164020700c01400041c003528054400307039a58407122140c58040700f01d0171162800749585040c5605421080051900d868010f100c002c00480106c428079080181d95903481d142c82ca0409008000000e10003484003808010140c0e201c803c11003504ca5000c0500c0c01e082d01c130751050311420000307403128002c1841e002c006004003040c1003a4000a060300081d890503c0724600c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 734193911 1250 734192661 734192713
    0x1050909031c0b0f0108072016150207120803070302071104091223040e040311060c032d07080a0e190203211c0b060a030b0108090f 58
    0x200060010042c0540003044201c4100541c07107010a41118810070f01c42140c03104d44240e8108206e08052080c10390304448124a44000b19014446400e2010300d02c0e468200c0000c18048201c10592001a201e0154550301d19110415402d82e40026546e41b1012403401c01c142015100642c100003080d03d03107010703030300070702c4054420202c0082e43e1556100203001c40721043e00540303000301d4804034100c18030750140d40c1200000950084405558200d01d40341094016800341c99900f040d01400f02d4241400340c207280e0b8401c01000c0840382e4901e4960109500c6030001d03a01d4284007820254844902c03d01010401e004d9810201ca40c3e03856070791608100d0b048040540f100e803034a5503900c602c0c07402c0350040c0b000402d0150316a00c8074001c882d291050600d06000c01d00e03802018000b00003031954001002040b2980d100c010b6594a200d8005107000400500b10034031100c0e4461000140a52500e030160428400c041c0242c81d54040340e51007008158036045144190344c010703000007208000802540250803c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 734195161 1250 734193911 734193913
    0x301032d020a03110306071b02060702040e010222060e130c090807060215060901030f02010f0e0915040b090c091c020411130b0711010305060103090204050a0b03160e01050909 77
    0x85a0941c022901c1101c058009a4410a048041d4440d9007020007480b03800500e00c0c54500740205107005001c8442c920054002d100b100300240308410340d52550442c1c1c0290100c90001c41d0358fd9641100c0707550100e05508800301000c4082000100c640c01414103c00381c0a020704500111062004100000c02750b03040d00701d00380403201d1004114503c0420090000e0036243d0000d20702c800346030b094030441c0714004000760f00c01c401c000014070028001200e070010603582070070b103a284c071288408240c4040030b0768404c0541001400f8100075541f030000c2000706141c1d109a8040040300da003c000c0c0300240d03504581c0080400c4080041d401c4074146a100300c1d003010341e1960301e405260082e0740007405840300c54205204844001c2924004140f04c0c8d81e00c030303000380300b00c00d90030b45010a2581c1e130100808a481c01e4506055071900002c41990003500481c80c40d0381e00070001c01240c80c0045240c0b0040103185007641c0a8801c410342070f00c204c120500d05006566070192410701136840c0c02c00300010080010301901c55 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 734196411 1250 734195161 734195243
    0x908030a0804141009230601032307090e0c040f0b01170a09020d05031b0a0506150127080c010e0603401104050c03070f0311040605090a0803030103 65
    0x800980c501c5043c0c8117a1003002c0401c94505002882003411141040b0b0130000d0300000010000541190001102410390703c1c4030804242204030300d03600304103c551000b401c582c204202c403d5001d001141d00e459100003202c04111005102416908030f94400d80ba031070108131105050703548020700d6081d26900407803410300031132880c807282e0100e111103800342c2080382d43e60702c00304070283c03906000c41d4460700d001007203c0204900e010a850b0b16940d05c03405880f0790400a000b02c0e41c0200c0da44035407030b2003080502c80042800440026010300344a41d44a10038030701280200106c82d1850b41c8101200001101e00a00c170504680703071078800380d04503080710b40c0e4404008080656016080c0d4415444282c900c2501500302d040e00690800d0f21100c913000080500c500d1411040003c880c030098141c0350820550b10781340c00d100545010a070018132500c0b955210903031000c9400a02c1552001c01415503030b4054030381c002503981e1000d800c0c0c0d80340000c2c003004244c440c50a0b50754801c801c00c505250101864035446401d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 734197661 1250 734196411 734196433
    0xd0501020d020a0c12051903020c15190b03011803030b04020909132a0603090c0509150a08010603020a0315140703050a14150616060203090606010908030a080414 71
    0x4101d0740f00995100201d1120244001031140c07860032a600c1c070050742041440d01c5400409400d06481083c020700a055001c551040d800c1c0d02000040045040c01e5440800e03030801d190300e6400034202810101460f030500401c01401c1c14180649214142c2190007820940c3c1070b59026006400e542010541090b824084451190350f0421090300550080031502440c07071580c14441103103860300c42100b0b4104a01c07040c56a4203110300c0540300444c0e01900d8006402101890100c5592400d40d00440d0300c001c410080c0803500304001203214003c1400c4600e681210341e12070210f802d0b190715100c040d5001c100d8a8042002c82c900b000307d600d041c11400340014160100c42030003400b881060b00d100000983d19030800810360681d02ca03607401508800b02c801158500041941600000001458007031100801d0122000003000000030701075910040c155100d00d08a01e08903aa00340c11104c0328000360b08540d002511002c08012100607400c2070392a480075a580703460380755203600c0f20030030007003184528813840c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 734198911 1250 734197661 734197687
    0x6030c030f05070905030d020106051c050c0907030213140d06110f040906061715042c0a020108012405070c030807051006050406050609120a020312070605011d04020d050102 76
    0x3600c900c0705911400d0003107003400181840c0941d00309248007236a00d000420b100e6607585101c8404a0012440180880251450040d061200590034150480d41080178041110b8243e0042c00d28000c0c640100788416076601c079031840d00e030083e0702d4103500480d1240300003002c03c45d1a0031042d9000e101071045440c1c084035590f403c0c4c0d06e500c01e501418840390349100901c6040c1e442074022141c120350b0308041080342042900d4801101d1003c442601c180e42c1e521402d413a8240d0f01c0210002c202c00009102d130442040125540c072a461200304a000400c0c49001240b1110080010f1840940d00c0c42c40402030320111400b078030160300006007640c003d003001c0400000100312000030714409221310007074075040f801c02042c8019034426410243c41982045024070041d2200e4084c0c81a5080460f00d428008500101580c1403030007a4001035050300415030075401c89010b600041521034440c440403c03a60303a03101310070b6404030703400130085100410304000b040261601c50003003058103014400049c50034401000d01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 734200161 1250 734198911 734198921
    0x209010c080c0109110f010509090415020408011a03060f0a0504020307090603060209031605010507200405070207031118040b090f0f0705010215010608181009080c0c0d020a06030c030f 81
    0x24100b1a034494501504005d034030180102e01c50002c0d94440da1941e03481d80040c1990040c03c803a64001c04040f0b0000c0c0a01c401c032a2800a03800c032000c8115603e549904405000e8600008021307540050204071941500300010b05520aa42468140b0a81d89402c1c18481c0600380140050360b16215188012030103e50500c00c003c02188901001030392222480145800c00004032030f44807420040920400c22a40c014048444440c0d00801041c0c03820031820f240d09910030203c0d80190080d02c2c00c020032012a800003008010781340a024202e0400340400300b00250b4591300c0e40050301c001c2c00c880128000405071401d884e00840d040007516501d4050051080c40c1000440e84541550300541c0208903558060000001040013145030b0362407581003040c0502003a02c00b400ca4402c09000201c104400032040c40403000700540700c0c02c21700c40c0c0c1a0741d040c400010780101800c481b0f103002c7c18001007028a400406401c0f03480d0b014010382c440c10b00c1c103d0103400601e4105004070506841355100005081c2134424 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 734201411 1250 734200161 734200177
    0x32c03011508060601021f1e090c0e0c04080a031d03061609080f120f0403120315050d050d32030711030f2b020310031b06120209010c08 60
    0x240c001898103034034900c3c100703000d042603055400c403e51110404e08094590310b04907003082004601c10180215100181c441158a1780009160644403403c01c0300c0c2814030800c507020001083d180751558000070285106911a40310103a020303500343c6002038050501c01400b01c0c0c0541e0441d1200503900702203410848110b840003100d07800711000348003140c0c101088201400114000300501c3c8421419a99240385560071020840b2000c5100c1c01d1004595003213401955101740030f0004e0340c12160000d00900194a80c0749800fa1090001007900d003420f020742c4603000c1c0c02c900240107041c1d80200698050191184003181c1d5080e03512200c0d0a0422420000b8402000818407a0b8919103200000c0c81c081003038079440c80607081080110070541c900d030192200102c1c80c08415040960703541d02114118000317034070004441d0000c820408041c01005c16a0200c9005103410310007030714170810f0002604400d001703040c0400d5140c030074810441b01035409008445018181445e9205494507804020303008818 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 734202661 1250 734201411 734201441
    0x4032007030c0b07050c0d050309100905090c0a020619060518091207020a0b0f0d051f0605130612020c0a050f0c03010b15030a06051c0308060d032c0301 67
    0xc000c10800aa00300031400900714001d0560410125641e520b448440da132405034840e03010700035403000f032100600488003002c200600d15050003001390009440641c00c0c0c410b092048800c031002404d0790810000b228856032055001d402240d44640d01c41c40d480c500b40307580d00f2209580e16000300f599290302208030071141c0d8000e041d20291800c040c481e0f25010a03c20741c00c208180503c80600180c48a0401c030040c0d1b0002071005440d4513240ca10815603006003401c0494080c14181803006030a09442020719810b1911101c0c10740388e4441c0015141c6206584000a007480d05942c10002c640c030529943c0141041404054070303100102041c18608545080241e4654004620280c0d523007404000c1640c0d0702c04190024088504202d001a1840011042c0d50413050b00c0040000c00c2000c190f4480c2014110007009804601011a0036022800e14110120007007400480401c01c9413402c00d04000500d60306958021090020340c40c0c14460900703c03c11b02442211400e40355003603a40c28060304a85041d124 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 734203911 1250 734202661 734202673
    0x50912041811160f0812040b0403020c09010b04060f030b060f040e1f09020906070f141005010b09151309141501020c0405100e0f01060f09080d0305040320 68
    0xa10030120b070507a440c1246482c204004001d009140e85400344003440c0c008560101c0f1002c282803014441c82042d500180c0790b0403260803c0204121010228081c0307010303600f00d0b2a1400e21400b80458590280280d090342c034070520007002510b1048150440303056030b40ca130114004086402168654105020b2200c04410215081c02809000c05607a07602421041110750b038823030f2010b5040412240c034007d241da006e400003207804a45d102d4a0450f000242c0c0480d40d401d183c0c00504000c1003640031a001c034020b60051001505049a1900030503060b140c503030804600d02223003141080202da0001c10b8003000e81206020000d00481c0d0440d5800040c900100b0108182a42c480c0044200400410b40820b100c00b80500c403100c0e0341c0c001030715400044251000241a104c21a00d10200401039024001110b02c2200300080b001d84e40c1113140c100e034033039210100048610350094400c01c41f98090300c07016500032205202d078103100750401c50300710b40282440c4080c5080304a4078904901821000c4070294004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 734205161 1250 734203911 734203949
    0x611160602031522020f040b0c01050a0c020a0c181b080910110a080405211c05090d0c03051201030f020a0b210c0408031204060b06041805091204 64
    0x4544884400c0004a5410000008804c1030303201c0040100d001075256a03000c80d1a0403580162001c580190039021519a1160800d10b0940d0280c50704a540a0980d41405420030185000060422500f544901800e04460404002c02d900d011004481140c041d1a10740c00020301200c1150720000c001e16a03180076407403400c4403410b881e002140481c1020289054404006106500300b07031b0315010303a503240c582001d4855041c1540380810f5a20058505030141070414110011040106003d144600180071071142c1441c0030021103004480f104031540080d421108100e11940c0300c0c4280510a003092424101c2c8141d8425060f8001d0b00103d83c40b01d0b17000c044009600d00003459800400340c0710a900c0c0b4002140314841c07145070a008928400034840d4000c1029a50084180c0d005010f448040b82e88900c2440d40284155001356010359056103044607641513410600c0440f0181c40036504440708031703044100c0f580c0c01080c004080b6501406902030400b940c1021100400040100c41090b424809038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 734206411 1250 734205161 734205181
    0x60f0f09150a3204051c050d0e04060906050907050304050115031202250605070203010f090b1b070b040b040318090c1202090a0b0309120304210f0c061116060203 71
    0xc4024501c40c04103e580d100c403e400442124203880c4213440c2c08541d90410b540240200740e141400420381c7c0564000c5412172644509101480c00c0d0440e0180000c99503070107078034110395403030003000e0300190040000b8045500440096801c244104000a0804990801801c085803075402c100e03150000c00400e4401e00d541000842c440c0e0306031100c440700c01030031000306420841c510f118603414400c01003001002d558003940007000042440314103214111180c60704441558045502d42e03010b41e0800840200705031158103551113507070301c25a10041525507403611007030854010422000c10880611510182d801e031140b820062071050804501c00010510280c01c1d8015140c0b9070041d24410300c02c080503650780300c4000c8201c0342071088260f0350362103e0140500f08482501c080c50f44180010500c82001507006803514100b07a401d6980d4000380703014000722201c000083e88580010800300408002c11840e500c01c61050408014052500282c01c4001074000c2404c4c005444040c0c0c040100300c142c0c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 734207661 1250 734206411 734206457
    0x204031101180302010f030608031201050114040617040227090127080703050408030406120b0109030f17090418020906060f1b0c0616060605060f0f09150a 68
    0x42401e050341810359041490742200c2c00e911000e410040f01194a1540d42d0007a40440d000d000751601b0f90340d880c3c801c420390301c408040a00c00d140c0000c554030364013404201504261802c0e100c440d500d42c401c2503984000400300141c050001d9921010011307000f8446e0b82c41180f42d1032508410444010145009071925003184d40c0440d11501e00342000080070500780e0103040141c9000c3d072000c170098550000e401d0423207850145030402e25651000160100720b150f00400700030400a00c1810500c56844208011a11006907100003002031240303c20240010340425584030f41d9003d0390702d0345400c003809400041c0540703038001d4009403180c40642094095003000120319600050030740d0036034a031604001c4008150b10039140f0700b40d29a100d07030903205e10541c1d061100c0c10070518024440d0b43c46494503a04802010796482080303843e00c4c1303000b00008450400700d0550721942116801142002140703c080012640030001d281d900c0300c86a1251684041d11401604c030303c50303003a500c00300654603d07202901000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 734208911 1250 734207661 734207693
    0x60403031d03011109130f140a06063b19030b010b031510020c192117130306051303111911010c050a0302012c0c040b0117010306020403 60
    0xb134140100080300b01565011640600c2c0d09661201a82c14500d5811000300044541190784c030741840b145c84440da903a900c0c2e09029150350711040120301e0741d032002903c02031080e882400380700d150085034004115400d0f0300080703404801740d1002880004000020104410501d404a501040c82428810b01035030080c0c60340901b290403011071460400b05c400400c01440716030198410401d880c5076401c96031081c0921014950f0280243e450743c0c030b03c4400c40f40c0ca44200e0081c4c0c021060f0b007090b415000e084200f805080b46401005103c140f8071a4800003400d41d01041210f070300148100000000201d0900c6030a214140b80825074102d85650310b0f008005022aa02c0800b072540004408180e038000c0780e0703c4005003507120000e0211158141c0040e03402d580b84090103000d0b402046114828180c041d00041d050004403409840241e010704145c64031501c1c60301c0b40c08469031044420007498141548480c802810504100702c8000000f1281d03540c0c803000360401c848858001c24200100081004000514 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 734210161 1250 734208911 734208913
    0x61e030a0606050c0606040b0a031703190c2114090102090a060f0905091306091208070c08040e060a0503070311040605010c1a1b07030801031104140a0f0b060403031d03 74
    0x1c404082c125a58811000d040340c7d110741c0c1d81d182001540e5555099180c029030380441442d4807559126115a0316410484d500380c04032518907007500c11004c0381e06c1074014504207511030404c80081808011a02102d25000090035030f81ca02898210901c50b800b1507108a0f86140050f035903030000c00c140b050880459000c40d09019a01c0d03a040d5000b0f0300b00001e0000d0f51000e60720001240d4800c1c10000f070615030480090005850840c0000c14451407600304140503000c2d0710780c004143c031360807230458210781010030103050781509100c2448450380d20340c1125000100201052501501c60001900b0b2074401e0b40121158010003403818400d0078103014200080009091050301384080d91035040d09185030a6800050500ba040020310310110703041c0000031300066000c9161503502c14500540382c103034207002c107544d4808000019119454540108111080c8161131044d107515010380d07079000303460943d2550054503100c040c840184e40f505806840214001c2e6603034648110b400212114250450380f0850003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 734211411 1250 734210161 734210167
    0x90705030a11180c040b0c03070b070c05011422050705030f0609060c03041106031902030109060501030e1c08070c02030a060609051806161701090e0d1e050306061e030a060605 77
    0x250404c0841030342d00319881031400c01d07550303410180024114481d8241c000c0078000011300b403109059000b40c1d400c1c41248248000c0081c4102c52000c1d41d1950b00454800400e80c00c513542016041c0740040051816510980c11905080e440c4c000190811a808109004030b034031000401100001c20000355400090918119256040648401641129501403280150000004a5104095040071008404040c40c0c21034072941c40702882c070f005d8080791040a0000303091620314882a2404203000840496146c1420210220100d0641e5004001414070080c0f02880c046400035032401e009003010144100c1000907100d00b03020038002100d4000d082c0f5200c0000b0f1409003500b82200180907a007080700c0303a10707141c2038840c46001198502030090b6000140700c2058000101ca2107a40c0100509280346c000303035201c00c4801030b030071107040c6103200b0131300d080c00da0440d010000b450044d8019a00014050045854400c4003525003030b2a0500c0b180584c80840e0010801008142600c2524050959442c0040c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 734212661 1250 734211411 734211421
    0x220302060604050705120c0c0114010b090d0305070503030f04020414070f1d0a081c110d0305180d1e020a05120a0905031222060206040b090705030a1118 67
    0x240da504001c000701e004030703900c101013009507010b82d095942c0c0c0842030703104040e5450301040603050380c0c2146402800c190f007801410040d204500d0b020fa416601c400301c6c4e02c0e080203141130030030840c51400c8a060341400f40410907034010032002d02c02940b09050b5041c0268240c1001d20600003107610303040782c0480d01728800c420b00c543c8991020208209c1501ea24002e40e521411180c0001c40c0710007202802c1e4810042100020310500100c5c4000340404450ba40c40c4100d4803c41082d00c02ca00b0802c0c1c403019540142c4580f10f01070340a0791003a074010002483d103c190204043d031884c40d11111513015008601c4610164401581c0200140300780c19507880a8003000c146941c0c2c2c50b40c1c998130400315940008010854038aa079100b500100020b040090459680d060000c220000329803000f01c500c0680324510840d038614018084070302040f07a035160b0050440da603880e180c4c1003080002902440050080c0440000c5503034003002005540307806824140d00854040c4100b212050340300d01c3c20010045079a003040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 734213911 1250 734212661 734212663
    0x815090c1002031804060f03061a01050403020d030f0207090905010218040b0f011b060518011104030210080a200a180f290a030b0f010804020f24040806220302 70
    0xd0000703405a108190040d2110005806070940e43c0003000e403004d802c0000020711484e84c0ac880600d070a20b000100e121001c80004450380d00c02e038000a5044030501d04088002449001c4030501090321b8415281c00e5905c1c0d0b01c4085c00d9544440003070b1882c1c1c1d0081460b40380a203940d040d400c640c035400c40c2c0401810600740041481d00306000039040c1806142c0c010f04404100600d940407500754004020001494048400040040043c989900d99841c00c00c1084042e01c081c422981900c0e00201180c08684403600101c4488800030300603c07a15413a81190510010700d401c2d49141001e0345604d580d00e03610b01c0d180042445002c8100790300203c00c0c4039002c1003640410440841910016144116502201c003500c035440200c1244610400b803000940043c504d40c1940803070041542150b020055008110046804140940300a0360008004c09004075a18240340411948154080c0e40b140d9203100c2c0e81c40c020b45400a0344480300e6600810100000051290000c150603110510240b0950901e500c3c02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 734215161 1250 734213911 734213917
    0x220305191812060204031407080d0e01080114030307020a06080727120311061609080d0905010f031103040812011e0e180109030903030305090318060901090815090c100203 75
    0x1e800c02c4001041e41050040c0c58040b038025640001e0207124200100c00340c103586100521800351180200d41c00c40c0a400e01c0f40301040b8500905070368209659080000d200508442e03082081c1e810b120421407a0010b0f20b6800410000b000d003030711815114500f41001030101120413240802c140310b03240d0b2003164580c9107161a02500d4104040305101005440c0a440002d0b1421102225206080030040d00c0d43c89034065800001c02c6a4512204680d030b001e620303950740c1100d0f008001054042c24207000da940300b110740843c0c0f00001d01d000309201200d000702c8409548281c40542d01c40000045003215400c061074040d004045168414201d0b84242058a0b1034070414040c80ba1045e0b000e00124128613411440040c0c1410701c0c80c020040c0c1c00b0760f881c0c044d0042400344411400300e81080002003007500d01009884001080c04840c02c000b80401d02009134503442000094140060900c021030611ba0030415050783ca00c012003c6892806c046175561700d8180000041c0c0d220340400c24046008980c0401031b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 734216411 1250 734215161 734215169
    0x10807200109050120160f0807050102090a0e04230c04061805070905033c030307030b0f030c061c1d0c0f0a12021210140a090215032203051918 63
    0x307106406e604c2c41c50017540016152501608501000c902101440010741c020400c0d25000c65003001c1d5240c0d540f140a85a0304101c83c05042c50700b138000443c18064084981080c03415180003950750801010f4001021118950851821241c0980c04100b6400766482480c1c0c100d8000e003407038035a4500d0030000903621b461040154004000310641082414900c105455441c0041340611aa01400030350880d900d420480b241000641400c2d40f480450802c182642c184800140c090300c26811030500744040b036840503624940c640c00d40b4000503026603131446a02d1f807003446212481141804404100d2500442e045214440c03402c4000ca200c803a030300c041c16042256040001401c500205000040e50700c0f0b80d6200c010f44074018010106100d42240d4411301c1c080e8200003258017203488101a000c215040028025000f132009071900b1200329640d40655406041c8480504004030200ca0303042e0400b43c188403c401040002c02c1c5903204103e4440124810401e41c0f526040c860304401058440305860702c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 734217661 1250 734216411 734216437
    0x806041e18021c05192609211006080601050105070f060203091609110901110a050a050c0a080604020906010c1e0308101413181b05032a010807200109050120 69
    0x540801001b07810003504c4844000604001d0280c815805c4e0320710001503040c11a00500030040c94240aa010748030380b100b620500002000b0356800e081c01505c0e5076000b0303107064450040c100c0080002510301e000440c8500706000180940c2140c03803111007a070040c1608020002130070f08401c0c2042c0c04990080d00e404000910b45500301e1034000400c2030414200040203091401500c0b140b0040c000300040180c41d06100f81e178145100d0396203100c0d42ea181c0b0700688000f9405085403001c0342281d0310401ca0240590b01070a40c8a004203a84400148103180000d4220040703030510081000c4c44410013160310040030700403900e0b00d001c1e0348c020014082400a5240030a01980c4461000719503040c108400c44590b4801c06507804101080560301c500d8000748100c503c02d1142140d65a034484c9500e00444808a00000c80c50b07002e5010401900d00c0500240703850100126640f661032009610400700b0600c3c4641c01c000106d000641c20300c9400d4800079441044d440c40c000004001000c0b011088607600c900c0302d6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 734218911 1250 734217661 734217713
    0xc0a0b06010c050d030606020c030304120f030509060304050c031002180d141b10020f0304060509130203070519021903080a0b03010608030a0806041e18021c0519 71
    0x200c010707242081c6400c400740c094031500b560b64045030b4041d400442030f00c6180d000c03604c0b014800c00c20580e0301d00c03440c0903003414a0489030680d00011000e003281e20501d442404c10505220000d804030307502d5042140c0a9400380e00402c0c600c541c03410288400e400c030f85400c1c0030551070200040c510b009105d28039400366000d0300c1c031440213106200c036002d0f071405441008030568809080111959801e45c0c500708410b07204054042180c03411303600000c1c0c0c24031400f07140c0020303500300b81c40c0c002e095030241c00402c0e107139030844043e24501d9170403415032005500c14130a41d240c05448401e0803005401760182d466410080d54000704c0d481d2400b44c080703030b598012039a152902d030415980f0856004040c110102d60300741c25601340280070601c800c000c0003406003080940d41d4a406696a0410001501e080324442c001ca00481400101d010b1202c1d004240142e242458103840e03040c5640c0811401e003805100300180614501002c005c00c0818440c06079045260580c00d400c0d0b20030360b201c0070020390040c1241c41200c0301c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 734220161 1250 734218911 734218921
    0xb040f0512011413020306092b0306090f022101031e0f020a0303090611070b07081b06040b010f0e04020f040914070e15040515150f0f040501140c0a0b 66
    0x3500055407040483e51890168100030300c0701000c0f813040e01400c034032a008000c001180e10200080ba415407030610034030141291159000720352182d01c06482c070401c16444d10030206920a160050301c420300184140103a4900760313502d10782110000640d540c00c554040c10010008144d20f40c20350340000c00d8699007440074103c2480d00714580344207088000c0d0000380c80080041810b03000303010b6030708540c035580369003c0c1007201c10391044e115070a90054a034614001e20150020801090140201403d04103100768541010306500c1e240500c211401c03112101c4581c0140300208000d03d00400424074079030b8042080c1080d90000390045d4501c550240a656902d0f5003d01b4000a801641c14000c222030075030350240c2e21420102d00310901155501400084182903829504107440340c20720404060290010041d001030801603803440d010141c15143c90705010480300042a40010034421012340d04003582c8514000000d800100c1c2d41030000c2c1c03110010310500c044141d002c42d2800310f040c1c0c01581d1b00c40c990f40d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 734221411 1250 734220161 734220163
    0x91f02160b120108011a0613241404030302152d16020a020306060603040f0804090902010206011208030a0c1202040602150907030b0f0a062601061703070816121205010b040f0512 78
    0x189c1c0c00540c034004486940d00fa00d28006010080d04046951207405009100f12022450b2107907120040042e8401042200020f8002c03000a4000d0803c82454400181b8032074958a400440c076000700c5009100c00c28480111b00c10f00e02048640b41c035001501d444242c6170000303512840010065406000000001400c11080da0900500c41d0f0788504250303102d0b5102d01e4200c00030030301800102e02521a480c000f1481d0401680a45103040c1e00040da90729550b14140c80c0b0001d40031500c01e19051104040c0e440d0384800b520b001a10181080b680204040310001420428400024000c0c0300103802200080c0003140300d00704415405180040100503d8503a10110300040c60030390b00c5407002c00340361401c810302c0012002c100880140300748001c0c40981e4581c500e81c0303011038204000c072070b165108000c0100064403005c0034042c001010403c48111900301d032208c10303448045400b6600001c00100502e0b241c20080d100d42409000c0c03a0f00140c2c1800d04085007107548040794002c01c5d00c6407007082d81940c56500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 734222661 1250 734221411 734221447
    0x907082d10050408031b0717070201020106080d050a090e2a0702090a090b0f24030106080727110d091b1502010b0303091f02160b120108011a06 63
    0x40c007071104000c42e10b000d06100c0d65640090700c1400680f01a40303140b12016102d00299801107400201d100e01c81c5903445c1c6405801da0000000300d040d03540318000042c0401d41400080b0003000300c1e84660b81d0300c44190400801d10a0030b90800d084201a20003444000207680e59250081e68600030080c1c000400d500810b5403c3c0503d920003903000040e5010002c119007d501318003049480390042400540301c0800040140384111200404100c0d40200c0e00c1c0450001c00c001d00c0710000203400092143c2d02c40c003089091900503041010030110a496403220201801401140d50220120411131404149051213080c0702d0f2050341c85006031642039600610114404503a82074414001c0800311603a07480780344035801444200c02c0c001d94a00310340340c0780340d06010040b6140004004c0c0260072000d255003203006148080d0002c4c10071842148a4021070b90113480d411000b030030310070580035101c0c080c01d940f104a200c0140c000c200c040e4101150b150801400390072071280c0f81000c6030700940b0344040c800d80b4105c1407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 734223911 1250 734222661 734222683
    0x50f04030e0a08010501092703020607080604111206030d0908030304020603040c080105041b140a090f02041e080111040531020d05010e060108010510031119080907082d 74
    0x54603010000451640c2e550148450408c41050407030194811806415008003481020340580c0141d0f0008144502c10501e0340c1d0700900090002464440c14010350b182034000001e000c04c0d070550344061080c6440c0800c824111007c1c43d10740a0703811390500c0b00183c0c50f408040e200034081c160100c04102082000a103400240c00c801d0001c02451400341800c049844a08108900c8550105004204d10017030064069050030081d0101001515095410b40140841c51070384981c0d55080c00041128408a59101212500328200c2c0c0c45071418502040d0844204803460301c88007400700010421519103c0c41d0205402404c603540d05400e50280e031105011840b0001c1703105d00e038800140300d5070220007948600e0581e031440507010383c030f0b65840e001900e820400b802001e510400c5000314031030302c0e4481c0c1c220348407503840341004034100300361107066040242260a000002c10b903d00c080215004082003214002d050240c004c00340d2106200081260341c0d80081a48140f40c0c1b80106001c6402d000c11040d0418 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 734225161 1250 734223911 734223913
    0x160f0c050c100203072a0302061312210203040e0403050903070503100204080c0a06210f14040204200a0e0607050a0606210206270d060506030d03050f04030e0a08 71
    0x14040b4050003512a402000110399014511035625240c801e103841c0a1600041d211320192801d046408000440d000044c004d0300d01c11801802190040e242c4003440000c6115801d040200c090441c05078884040307080e0000c003150300911041050800c5000c0e026001038050074025a00c0c00c00c038010a007002d5a903000141c052240390402e030240b0120754001c0c81214542c0b07068480301e807020800c0282d0304080e8440d9100081d000307030949041c5a010240b100c001c4d01210400202103020410300e80965680c0020381070010391140800066040a000d003005410724001c0140d17403100c4070741c81601c8030700600040104100070300100807140d40380c0700b04640d111a000300444041300c01529054000d0300712405031454080001107004281008081c04a814607801004a800c00044d440c0720305a500540500f2018087e09070103405554407002c440d54040d030300808000c5594504075060601d441c0c07c600c500da08040c5490104485020081e490b2500035074540f030515103c00140001070b481f80c03200c0d0040221 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 734226411 1250 734225161 734225179
    0x607080d110307020f0111040618080604030c021003050f0c250c1401110304060f0306050d122c0603040201030b181b030c120406020d061d160f0c050c 66
    0x1c0300820300607502c2808203038201c1e12050a00131241e4282d0b100c00c54400d01921040c08280076107400398000040400940c21301c0300f031850343c1c0c41000707142136000d58041c1c0100303c0c2004948190700b412840e5239000c1155060a0100d4142403200121903003008102401301c1c2c80105601c01e1105450788a92103c4030b10b14000c0d941e0701c0d46400e10480c0d2061760300c01c50100701c104103040e90040d4015000c10010b030105101039401d06240c903e040c0d0b0700c0302c12034996108042c0e40d0030001c07407150307106408080d03480d0040c10345c1e030f40c4000d03211400b41c841c44c0804030400c00384d208070003082201400c00315070000b0b9202c107943d01038698841e403005038003400400000d607520600b604504501803600c0100c25200f00550812030440d0100c429844005200a80740d82000201c104805c4c40441040018203800c148103210051402080c66020b40c222050758000712803451040026010340140d944140b030f000039200d04050855207005070042c1074501d03117001c441c090010098050302440014490450300b21009060280 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 734227661 1250 734226411 734226431
    0xc021003020c1e0c04060803070303051506070b0f0c13060507020a0909050312060402070b06040b0a0503160512151b090a150201050a090b0c091203040b03071403060a050607080d 78
    0x800c00c4a1010b401994402c0025501343c42c40d040c01158200c51400c0040c1d8980511a14201d020308802090703d010030781544c4049609490b120700520400c1d0150440c0409801c041008002c01c00c00607184034448070307092101d070001800100501013152002d040c0b5070741d1034445101080692645a010101381850500c49400b4814084028034034811410316800581c2d4444003000201d0040141c00303030aa90240c0c00081d40c3d800e0580c0469503000c4020160903155542c0d5001916040b1400001085071440c08002c01143c10700044504210760301001038803450046000020450f071000702000b641403080c140c50002c094882049500ca0000034090800c0191201e0f801001040c00903600c00042d0300e80303400a04040c05a00c41c0d07610680e4441304000103600c641040045a0b00200b04090380031105401a540d03480e000c000800003400101d030559121b180c0810054920040d5500c86c6480ca43e040007000202c0d40c91019030030540300b08440301764903502142001e142134050f00b0410b492091030034013030079 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 734228911 1250 734227661 734227693
    0xc1908060a02071b03170d1d280b040b071211091c05060105010503071829030403020c04022b0603140d0c08161a010e160c021003020c 59
    0x110f4003600844039006200103505803400411800c2c400a040c08a0352210722200d842e80200401340c0981948010905181420b0011801038518040c007a203a406140c40300c190101480070706ca40c2e03d041350040701c0a034130b10761611180079100400080c02c210809000a9680380038101464061008000c100080b10024a44440a612002d49648208010702e41b00c480a81d81c119051215644007020b80079903482d100055903160000380c58041407082c110b1040013042d09018030040101205005021152901c0010107211106c01c2140d46003401d0800c10400401c0d000107100170402001ea40060340c0314403000da92078070180260030160501c01c210040d0340780828580c0020094901458074100034160115504c1c1d900d0840f04800400700f40c211980300d021454503c082c18003040d40350107080000c80c0643e9900d10f8808000014250380048c400103101c4c1c1e103010084240c1c01440c401c030b040c0c0d10044000d400707000301074212802031041503480700341800303a88a1380603125401410341c00c960b143c0601011603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 734230161 1250 734228911 734228917
    0x406020306280303170c0703140f0d02041406090315101a0d05010506090a050904080c01091202160f0b03041407180e03090d2603040308041506080c1908060a02 70
    0x340c1c00034002d038011210140b04c5d0300100d0700481c00d0a00b428500741d0190740c00c0c1e9000b14503003408000c8034000c2c0319000d042c2c2000e40040c032030b805550382c00583d00d5083c1a010066181c0601c2ca41c0d000f440d0501c04007080f910300181881003104070544500d07580c2c4c4e40e0080840c0c00702c0d10350010b40400d103024081404103a10100034112400b1500028000c50783c0301c1c03084c02028000d40c55500d0740002c41500c2000075040001c02990402d0280440e1803504442c03d84590039220118411206d504050130f158080ca58144804100303604184020020103151030f0004800c08618095a00540780001c0810200a00d02c50400500d0030000709407410596034075141c0a040c0500c440c5260702c1400d1180f03d1a500e54044100d81c1d40803801000c8200d0f01e2040e89440810003a0040c80300604804500301248041c401707000b440c03045119558103002807030103280c030446007104002185e848e01d040940a1245120104204200c07107425620031321024144403140c11905016480301015001c1d201c14441c80c1c900c03035001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 734231411 1250 734230161 734230163
    0x6090903080103030e1005041511030a0c0b010f08030702120f160f08072621071109090a0b060d0204060b03011d100b070303111305040e0a02060304060203062803 71
    0xc81a0401000f401c1c8018001500b0b4010f000503400c0000380300d600c9030302c1d106404104c09d0303140095100d81c03410481842e55204156400c08540100c5004d820031003040f00c2a03000d0550303a80e0018070946400c2c03000c0c0c1e990007102d0000780320b4a103d05c2060f00c81c040403c10141503d0780c0742c2c2140c0200c1c070f184050101004c528043e11110140083d0086400a00000c0c03210481d1a580358a211015895200ca1070361454040040014006c0c02000d5001e605500460826034001c1011103a8403a010701d05200e500200d02c81c2240201820001c0224503180401c803041d15030f4100800003141d50381d02000841122842d040258000d01d00303480030446c0d11075040518141d48440c0d200040480300c1c120190140841111403105643c90035005210010b01c12016059071446414046480160940c011145410441d51b800000ca941c0f42d00300042e1410740203249503a040500a451101442d03004620588801003014011a400001140040e280d108a204600c186100900c070721902040c40d4615040e132a01c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 734232661 1250 734231411 734231417
    0x100501030605010e21150403270303080609280509011401240311040e1603020310031709030706020f2506030905150108010204030215090d150609090308010303 70
    0x714807540202a1006010030040001c0c41c40d040f0090310901c02c4c10400d143c41002c2c01b5110039030100022010100c6d0041d84662240d000a030090100c205c4c41000341c80d04103440700d20311001040465041508141c200030252006c84c1749588044081c140790195400841340e85110f1074012004440c0c0d540200e009440910081c0591319804031f084020110078000d40c84c07124008602e400d911031094000110151031410041840f61004500640b80e4129a1100c3c0d2600070240c1004174210100400c403001c244139080460071401c052200034100c40c0c2034007004040014035014a04c806602100344d40411100908540b070180d1120710094a400081141e070070a4480e241102c2d8001c240c503030380390000960140c8007041c07451929400f28090480c400041c2d48074090500c005030000c00c0124864040d044100c0003680e900d145206109113400340307450008210b41c05020030b021543d642e0b02c51703010741500181101026400d0640505c01044207034012130090746007140e010205a04450503034101c900a407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 734233911 1250 734232661 734232671
    0xf0a06081605150c0c0108040302010b0d21030908160501061a070c14010503070804020402070b100515090f0409031403011202120f0d0f03060305030310032d120c080310050103 77
    0x1203d001418024190300802c2600110f044045a51003852070355030250180c4004a0898107580c0458071001003090156100306034030400070480307804c0100d50184c1040524007045003540c0d40c0c903440700e90701503200079103c200c044034031040c140403094110070040c204805890008100414448480c2d40c044281280c15400000c0e00181f401c50041048901d1181130712414615502d918080322510320040c0203d83c030560030302c15200840c8414440620a001c144007100100782080c01700000200c0f0f00384d205400c250704014020f01074640c800e10f02c44140080e94080b43c8a41d4901e4182d80e40c9a8244c800d1043c03803008800010701000802d00b000280c0d0080e4bd05a0504200440302622508140030b821001e9100039105910284910600c10002d07000d441c0014400382c4951b03490307080d0f0f801036884020706d004130a8244207105c54001485c1c985002601c5101c00352041d80c2c01c003400202c0c4248013404142d19403158417040c82c01800341000082d4842c450950302e24106084810340442d9004540c0001d1a00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 734235161 1250 734233911 734233939
    0x5030c03120405060d0609020c0f1612080a030e030f1c06060807110c040f0506040f0c0c03050a0216031202150613091509030f02160605030f0a06081605 67
    0x401c80c044081c480d465070901d0b00307042c88140100ca60002143c04081356850701c000580f903080e0710141c950150010040c0800703c00c240e4115203020b001242c542032100d40c40d00e04000c00522039148a490a920001c0c040e101d01e40d960041d001000b10581114850200080550440e56203200130130308500c2562120310308191a040c403600b11480b034001c12011402440110b40103501810800c424020300f041102e0001c9482d80c00b107410f40f00305035040100c05855000f03001062509000d08840d6240302c03082041a031b0004000101941041d20002c0e041c040006082e03c0e4081c4240160800c0000d0000ca050126540703190031110341180c20004801402502d45a0110030b480000c075901034000103003c001c0c802e036414444001022101d100b111341c1d0421002051642260b400745643c13107402502c6451102180b09006410486250b141240c0f080541c18107001c01c07074111302526002042e40c001e500007a60342841c104000c246540048490744140035031f5403820002d40040d0400e0740d5094681c417180e0b00503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 734236411 1250 734235161 734235163
    0x110114011205071d01270c1701050603040321060e130318081c030b0a0b120c0f0f0c340608150402160b04050705011d09040308090a061505030c03 64
    0x5420a58481c40c10352200400510118800e0030070108108403044020713040300c40d4100100c1f00392020100c0490b0146400d09014298125103030700410b400d4858a10318605550010300c240c0c440004c500304640a000243c10210107540600054032080c28245282d00b0402318541c0c05900e100c404500003503207601c070181046c441548150880c0e0400d002000f5112801e92408420a05407400301c2c10582d54098884283d503440b8202c2c0300500100104c00c1d03441d8640818800e03581801407102c801441d04100c0c2403a610440c0c03088541070700c0e03195005600e03201d91401c030700c2c1410449040000590360350142040f1108080c0700903400c079004501c201400c9991000e00b580c03445011901074100b003141034852801405c154006207140d0204051240310581286c3d80c01040403405d88040d2142c1e8032810080c0320f40c0d40c000e8501c0a02d6000c132507410034090b101000003081004018401070410a07200c0200b070247e2001c00c1158487e0368400014001c540140c56050309407a46842142c0c4a031080f01111100303820 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 734237661 1250 734236411 734236439
    0x181b02010212070818060f070905060403050a0303050a0603050a05100b01030b0a1206110406020703030801140d140c0d050a0209061c110f060d0903020705010e1011011401120507 78
    0x102d601c00d20442961102c42c1501ca00c44001e0100c54401e800701d04031002c1c4a000d2080754803410242d041d51001f030a105800800c0030389260416030146c40304000c140007066000481e900025072502d40400d00365141c2c0c0744100a070400340d200500b2482504140b0082010206900d040740560050800880141340d0044003a103014041e625004035101c40144031200c907044c1e0f030701107080c09960045218682c056030324407035500c103522040042e006018203100f010741c0300300c55600528141301001c0806131544000b0b080188080002081100142030319142401d0500c8035100ca6000201003010b85206400c1c40b0381c03100d443c141d08a1242110200080d2645071031404601c2d18200c0030b00e0039015100036610b0100413540311292540c401543d9a1103411959030034018951130315182d030003040140301498003030720780055900300d2030521200c449162000c1e268800903000035440b902d040c14a00706508862030041950555070f000c0920198004907442c00320005c5008000e01c1081110002a50b500a40c40034013 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 734238911 1250 734237661 734237677
    0xc0f09061815100503010f090b090a0b030708030a051803070e04120905090705040815090c010c0228060801080606010e0d030e130e190b011e181b020102 67
    0x1e400034501d48078400707492404541c030221162a189800002e0000500300c15004100740d000260000010700610414000e107200510f64060140404640c00b800100c40000041c08444010780e02c040c203c44c1541d040141e00b00408040083d41d41d64009590001c2007036004144115000300800d8119000707007000900b000c01c460f40308903015010b480b180e54803202d6031440e01a18003080303103074000820181c1e80d0b00c03682801514103444080e0b40c0c918041a072400e2400f452504200c0a21100400445840205929441c440c0901e0100c4110400e440016140c0303400c200440694945920107450104a0803140400c4c1c0d20140c131504e03000d03a03070f401d82580d941c2d004442075400200240c2e0b81140038100030045581c03031403107030030a000544410720110b410240c10746807101844ea240c40074100c41240c1449554a034951540450740c0e884020349640c4081c0c0ca040c402e404a02004856410440c05080000c40c0900808071150350b0030b468402200001d000701209048104804042400025005100b2a1564 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 734240161 1250 734238911 734238919
    0xa02041e0b04031103150a09021f0e011101062d0503120409151203020c010e030309030a1112030c0a060f0b1e03010f140f01050d1509020d0204060303020c0f0906 71
    0x403d0640c3d542c0c05040c04903011181d014801e006840803160343e05041644280245040013841c9500c80c010400790380100009409100103114041160300d9004419007aa54000c3c200200310004914510f4014107155019005405803108401d45070000300d9a035051300100900c0741d10450b80c80d0b8007010749444408405174a0040200010811280190014810800c0f1a60204c944517684c906071040301c1801c140c01c40050b0000c503689042c0d50380110b01d041c40c0060680095003403100c4900070075960a041d00011300100c045112107030710381d80c4814102031210304500c01c1d00d8a070700d04443c0301c60391440c02c03100c00c4400f94105005801519218841c2c250b070200000d00811000c3c03402d041d01001c54241102031a0155295113121441703ca4a003e07840c17035107403181c04000749445c02c1d25050803d4041a0041031042c82e4221081002c034034030244806801010306800101d500351031001500c40d11a4a4001b50803030b003415400802d2540203d04590441750030344e0103100005080040090440e03040b0754450340 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 734241411 1250 734240161 734240167
    0x5010203041e05040614130621050c061204060b0409020d0b13022809092d0b0a0e010e0109030206151c0b0412030603110d0f0b0a02041e0b 61
    0x71484000307418640b0502114121030b0306a4035100810103031086604040300d41c80981002101500b41101c03500042c0b025084200f00050420100b00c441100c0e850344d0300c10424143c503000007031000502c1005503000b4001c040c0c0d681e480e40c00c1211040f01d00304440680f620b91402c03500c058070781406d00402403040d034004d013458804c0c6116910715029003809410141d00250501024005848081d20020800b40c0b854080c05195900b122800c4221010341280d1071940c2401d0640c000500321901c808044104201c400c9601d00303a02c40403600103020118058000318801061201035507050b8040360704120f1000090014100e403c114509a5040c0390000300161300c0140000d0714404944045a8083c00040c8090070090ba036004c0c0d01038403141e00c0c909443c0ba81d105024001001090030982ca003144560505101c96403a40e160808132005540c02c1a00640c40e118400081041040760140c0240d4803180c100464100000401d0003500280a030315038144040c6000755251203642410801c4444038014145 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 734242661 1250 734241411 734241419
    0x30207090e1501060306170c0604090e031c02030604180f1104020412080c0622120309020402280504030803150303121612020906030411011b03110f0102040501020304 73
    0x801400c0c0001c44040300e0103500140c00c1c8420000c298076008000942d008280b090034161408214115940c0e01300710340d40085113890081d12085c0c241d030122045420700051090a605445046108140942d10702d8403104101e59115203a1350b000c0d600035001503904003c0764030408040f0000d45158040604030b504281c00340340016510054511003020064005402e15a40b44002507544a0083c1e04440d40d40010032110b0320b040041001c02e900480b40782c09014001603813072205850041500c80546001410100c0120f542c1c02030300400078103030f40070704115558030040c0040c405c49615080914544030040d0003010019124005032805d59801c401118030710307110580d0031021600141500c40e014081400524000100004014810095004405801c6800d07840042000004000d03a00b0800d00c180b1102c0c400340c446405603548154403009200c0040101c40060b030700310b40140d194000c0c854000d001c080c2096400002860440f0070a4100e98040c0d4651202501b43d0107203025146c0140e106100402c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 734243911 1250 734242661 734242679
    0x140405040204110d020c01110405010f050310230102010c05032403210c0606010f0507080912070b070203011a0d0f06150b0c15040c06030b04060b041d0106020a030207 73
    0x103401034401840002c01600100c0031003059009202e111001a5000c00c1c00d0818100a00614400c01c0c401002c0c0f84c40d0504040011300046000810302e0100b00d0301000107680301c102007880502a002d492182ca9040601011031001a000080b02500550800d004580c189001e0404d070b03030051000c60a80e41c8600554582c0250340c054400d401541b5206200062034003a01c7c0d500040d200303208800c8901c0d034807000344d140d407890701130003526103410480b018403c6103070240d0240a80325841e5000058a03070725980440020540035000311941c8060041c490300248584410004105040c030a0b0024031a18022841e40ca640e40c40403112070b40c20400b1440124002440b00d0160303004c4601c9041d0016020100d4085d00b1442c1e40c1d0303600300d680e268030000343e4120040b80c10451302442d054034505030b05081c42e150f9144101d84819209a0301803546900281e607140d07541750000d40282c28100c0c1c401e51910740d0b403e00303d03228030400402580340c146800c001144643c400310714080510b815400519005150049803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 734245161 1250 734243911 734243921
    0xc01050103080406020f0a030e1c0b3412020a03090210081b1e071b0e04030e040c0e090a091b030303110f03040f140609150108030c0703120203090306040606081203011404 75
    0x191442b080103010b51303c0042d1410607014081c1d120700a040441ca07900c09140c4d804c5128030241940503040350081c2e5040701d0751081801c000361010681c0941c42c2c1c100f40e10140c0141203d00d0300213500240355400700041580c0807102c42e02c00d408041000c490800380c3d01003a150340c45501107500c01010218100c0e580e03214880014050b4500c03c26800c0128103840300c821071440c40682003a030400c0c0c500030a01090540c0104000c41c94201241c040240c92003c03400070b000c1c1c03138a0b400d005008190000c00101c20316055480000c54a03000015071001d024842614801800b00b80400c4001c41c0c035205001c0c20701e081840540d226100c4200c2c80f50303d19200d42c5c0b58030059801c6841c04840441ca42201c262401d5000c0c804540604030001c0200860341114405500c00c09050f00005050b80c42071156501d010000100c000032607800c10200024500c10100c22070451050341400c903014401c107014001042640c5d41701d00111207040c8182d8811551007408147d044c48284920343e00d41d40c0844000079a8501039000b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 734246411 1250 734245161 734245189
    0x11090a0509011b09122303030405010b09090607030504080405040606030b100207061710050a08030304060b03210906070c1e120b04110307030203010612020307050901080706050d020c01050103080406020f0a030e 92
    0x41d06001c4904e09507046e8260b50a000c41c80d056801c04014042007110074014422601011524103403a403502040407a40d0304802442d0400b016100c0002c182482440b000703ca002d09006881072104940794940500030b0b00d14842400e00406400030424045031000c02c480c0184c81c41650796040840125031145078490f400ba0407515040905a00044c1965660f4070b014000d0061001454491902e814401d085905c0040e04900a811031000c5c0c021603074051380706000502001c02c1d415114024500407441b1070240d098000c0c05140d0b9408007042c0c0e000c0f0550205401a0a1f41d102c120b50798403580d0754580d40e1a0380e0703001400c07400e1120200e4009040703a034841000c40c0014040340c075807959a40000e0700792581035010b9035040c45000300c550250700302480401d02a0000f50703030039021540b4081c1d003aaa2961a03103d03610421002040c0d0405150b00c507011141070310f01c01c0b00207004d25612400c0c0b0030b07020b51107440740038003521420030445010800801c018800a40540b10a5040c4d041c500070311211400100d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 734247661 1250 734246411 734246423
    0x5041707050301140403030b120303070c061b0e090c041514070b01060f2a0b0601120c051207020c01020d030b0105090d060509011401150c11090a0509011b0912 70
    0x503021601d91402d200703080c0c02804e05030554401d8201418094200c40e00001c200340503a0140c1c1c0d92001f032107000000c0301e80110316451300000118003030a0580c001c14880d03100350325081180c0700301601c89501c080d00d007080c0300d401c0f9019030741e54407016070260312440303071b03200b40700c242c00d400007288944034000d81a44140703100380c05045142950590380c201c05500c1c26004040401c41008100009030740c08044c002e1011f01490b10440d80e0b003d0b009420070f401e000c54000804513003030000003551036445044030000c0c4404015051140004c2c602c000740c480d422800c003550304541e041c2d0000d48018400241c40c8030407101a0040c02c08840003090443c09003500c002524144907003040486581c1e1118030b201411180144000034807424000051400e40f21030880c0c0d00105032140005201c4262030200d031102d10186414928140e60680c6070030f03400d040c0392108041d40b1643d030f24104105003245400c400e204030343c000000c115507000d91003104078049d043c82c017103800510b92900500469104030903c84520f80528 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 734248911 1250 734247661 734247673
    0x5060a0f0c080c1c09060306080303010e06010c0c0b09040f0b0f1917031b0a0314031902070317060405161119150c020606010503042003010c0513050a06050417 70
    0x20381d480c070b800c1c401003419092001301d01c081c1041c2a80f14014070040d0656140c1401151700d46489581e40303000601490700e0005884000c5911603015030310b035814081d0710811034150035a80e030071407250b1030300261b0080b401503041c0440a22107000ca88540241c69070010031420b4041e1101c002d0141d82c0c40300c0c03402c1980c404000000400c0704e18103040d5000c4081210307401190b0b00c5241e0320001001060201c8031b07070026800b00e40c2d070100090b00100d0400741c2034020501d0b15201e40d52003100c0c01d06001c41d8a110b4001e94800a105000d0650180302c403030581036400e078054447e4440300107000455500301c4072002004c506482002c10980310704440c9045000d94821100012164041c15444900c2c0c0c000403500c0c07200c11207002001c006a4040e1082c0080c0a00241441d40707031100020b04180f00081006000c0e0070140c50352901a048902c44c46e01d02240500200881281004007408e03d40c80540044060510003000203801e14001c4110007e071100c6559650900f4504040350074503492040e00612035000d86 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 734250161 1250 734248911 734248927
    0x80c09100c0204090b280515130b060d0212130c06050708041a030f0705031303110a0c0608090714060909060a080307050318010804200f06030901050103060605060a0f0c08 75
    0x503d0039203024107010b890340b10300704c07500d52540c540e110442812004030747c0c202020080c0301c64840055118200c0161503203141d440318106402c00400e008108580d10200102e10304800440c20b42c09000740540008980d1000d840e54000300c00c111044950080007405440c1060100c80d100b840a00082c0e80305e001200c0c00d194480b220fa21250192600c40c843c51031006c01004032940c400116030750007500a040c040d04e107003441c0d00382862102c0c80c458054140071400007160340803802004107a90701500050b08000c40b039200c40780184459815074a1090500c82d0810115075811030303000141c4580f800810079450400810709100c1500c03401044d0381d521001da9900003582000c280300a1186074442d6000d542d642120078100c0300c103004800003150400000004010000c0c2e6180400e1785030408100300010355040c98270000752103140724408182c01a9021040c8072000d02c0541001d41030760310034001800b409403035905004450080440b143c00203004880b13816170050203241c4c2d032030701680500400381c68a441 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 734251411 1250 734250161 734250173
    0xf11030d02030403080f07020606190308120603070609050a031119150f0f02100e1f0f05010603180b1b071a0f0106020a060b0402090d0302060106080c09100c020409 72
    0x6650320110350008204800c043c0c1c007140d00340e0702040c821030165060415900095446c0001850329000e0ba80420100d01000d40740d926400c0250352000c0c40941c0d520501c10500043c003019a0032134002d1042c10008524070340034014010950304090002210149152144007442c0c141d00b4205400c950914404c40d02d0048031080c20000e480100891406243c0b00d0700002c00e410700042c103202c01c012103004071401d0307280d0220b009803900310602008507107481441c411500301000d50b8a10301c052083c0f0003054a025209400c00da0000040031810030550b0781c0c0b00c900340c0580306040c9050410300c821000c00000070311103c1c11503810410b5003401c0f950102180207581903541c000681941c0c40c2c0301c01c544445a43c0c000c002d840d54040324080940400e07500d000ca0103541e4080b8030b0380040c000b548883d190f00c86511190f06a68404200820020440311281006501c0744030a0223203200180030200081e40107403c020840d00e001c1006841140c950244490484400e070070f02c40200d0b4040d40380ca1508000c110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 734252661 1250 734251411 734251417
    0xf030c09031915090206030f0601270e01090c021218060703110f010603110423040b040515041a040f0b041b05030f0d0818030705010501051005120105010f1103 70
    0x2c0300241d10312010b000c1d400c0001070203010410000e0b02a04040c60440107854590940c1d0304088a2401c040c86a1a1440117035040d4070440f04036450040b000d4400d0031000c16620300039048a0242c21000c1090b62190104410798082c00c45400c0540e003d54000750310340c000200240700c1400942a070b8950b8072011400a1016403192100f540000da210280000c927a405102d0b0001503c0c0c0d000c001c02000d0310b1643c90300410009907180e2840307150740e440d0010b00f02004510700504d94a001c01448814030f4685009500c0e02c02c10346040d100d81c4203034402034403405130300f16205002c1c0d41c1200e101114511004e258070b040d01ca000380b00315031505a08a00303500103500c14030628000d9200b01041035046c6030b00d40e80c09035881030a50001e842540980c10440b100c07040860012481030076483e101c0080c0c1e54180001d01130f5007001c2800c490794440001d0500c24043c043d800310b41600c4c81106c1d1134185001d00c10b001c8806002e2460580680640d14004204940c09021520880d00c21350070044d030f1060100d02d01c0c2d41160 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 734253911 1250 734252661 734252683
    0x414060a0501031106070b06040b0316030501050f1003030e060a120207031d180a09051c02030403030f090e0f0613060306150f0e0c0f070b01150f02120f030c0903 71
    0x20341c07100014810403d80314180b00000380305403051400c01e58280c881320310044020f08020300680d40c40d05403c05a4800f80201d0101c07410083d0240c422039580d01d022402070030f080ba40a0003081070100410b080260803140b842c11241c0660307c0300560040041003001c2907226107814820701c089004020f400d82e126001402e0018060b07122903d01d1110958002114207904901c203100341200e00c4445284411805401e400500b4400005510496032500614144070130ba0301202544444450789646079000008001396031190b40c40c03010181800703000b030790340d40024091030f10100800400038604010565009600c1480101035281e1050310900001c1120015001943c805031a200700c1284602d1690040d0f00134041400e05103542840d10356400521003000c3c00300c40c00100006903c03c40d540d0200265500c0c0358100c0c400800e1560b46120b010302c0801c0b540303a60b01c085101300d44450082800411070f210582c20340d0302030034030b44200c003554500707545d0000780708101e20802445a40072039201000100308803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 734255161 1250 734253911 734253931
    0x50609090a38040e010204120f08090a1e050402040302130c1707120b06040302101b02040623040c020712170c070f0b07080a0f050d05150414040c0608041406 69
    0x250b03503101444180d40307640458001580c0104010420031038003070440902d0941080403030700f00031070728034182256114140615503c580e581d400400d8258409007445001207420021074403503070780d4600f031206901651101951003055255480703276070307441030b00191401c0800e880d2081405041748150000c5800603989500010010400510011450b208580480008581050800c0d1071175000401e43d202c14910f07401005006200240d54141a01000c8005a0300500910801c1e480d241012160500240035155001000160440c1410706110b0100e18103116800340011a003000d003050880018110101c54680010b810781e40300098240260001e030394450007420741c05d4602201c13400c048601d6004400c01c408200000c500090304c070801c40b90070341c015040c1b0072000c40d4142c805403014009d0780305050460b4101410000c41101c00c41d00322210100c06c4508000e5001540010001e000c0b0490380100130101084d01400410301440d001c59001d4400e00d5900341c0b840c00215064102801135549400c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 734256411 1250 734255161 734255261
    0x20d020c130b04021303030327080a140c030d02270d060b060403080c0705090c0a0f2a050d0212070c1230020c090c0a030e010b041505040501050609090a 67
    0x402d0005140c1005860200c200180010103603e80d000207119a202203c14841070300c030310f80002c109100078dc03416255440156070712000105c0b0094040d622680c8003121040015030307228040b51545092214a040c003810303402a2030441c1c3c1e1762a008180d050b02c1d103944604107100000000720111700401c504601803001d465050324007001e0000d04034015000d0f0910f510705002c5503c285a11030041200c0354114500300c030a0158501455146035442c100102009424008240134400700294040c0030f0758065080b00c101c401d254450b51040d002e00e0740024401c0401410030000500003454540703825016000d404c004031031144d202e0140352901c2c084010f00b003c1e04010740d0585e0390140301542600c0c40031399841c1e031103243c1240000c1d0244644480d0701d05040d610301d08030328009425840907441d1200644204007610000240351151501072090302d20460034a000480e5904003101038400d0004050b014041507110081084084c00080106925a007c844d490403662080b420305800650030714413503404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 734257661 1250 734256411 734256431
    0x406030602090901050a050105271f0e09060d02060d0b1c0507080d0f110c040c0504050a0512060f130b10031a0411011b080d02030106020d020c130b040213030303 71
    0x181090050780894842d042900c020411f40e40c1290840c0c03032002d00c0c040304040d402500740e03240006c1480e00241c2c503000030885425452400c4003610002c4804200d0711908451342c1d82d4010490408800c54625810a0321400504010b05003880601031151560b2000b0071403094000c0410070035420342c601e840c5040340e050082c90900c1801d00c5200064010000680742d0012074240151851800c00e00403c1000581007513003030054002d1264505d4454010310030b0010050001c0000c1403500103001c1d4038030440c20501c1c00240c900c4c0c80d1041c11000d039001806081c02d44d0750804504110344000f80780852080e44071400c10300017140000003c1c4a180301c1d442c008403260031800c09800e1a280120140e0307020591a00b440081500b0400c0601d030800300b4030707001d0078044c41003400d05800016564003c3c000c03100450444410006a009581a42da0a03821a1003101c080340007203a95140c030004858024180d03520040c9458050b030030075001c1c0c80b400f42c005447e24580c180c1019808400e80d0081e00045c1d03680104035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 734258911 1250 734257661 734257669
    0x13020d02130f1508040f0201020c031006051503042a080709050f0a050f16020c0306090d0e1f050d11074209030c0f050a031e1b020609040603060209 65
    0x807024161600340d056005614103c060b00d9850003038030250110303000300c0040045a00c00c1001800482001d8242c0f015103964000000280203c1e01690307210b050043d280010408012061724492908140040500c1c10000c0034407901e00b1034455552107405074040045050380c7c04100d044003e04106600107080e281c04000c03001d00c4ca002404009805050209224200304040a9640c101c00c941040f4034000001c0c0000381e1074840300069154142c001e8104000000e040411a000c402146898003810700700903504104d6041b9a240045100318010030007200042d10400c05000c0031035241e880060b501c0c00e101e20020464100307100890f1a400582409800203c0c0b182d800405a06400d0241e41d20185020100601004481641d1060741d0b543c00c40c0d0047c1031058091441594005021600d000040c0c200942c603035440107402d8000c15072a803e405602c000402c188011003810359100d282a40505030444401c0e00801c0c0180c0c2d110000b88a486603a5607544540310056204510040c0c1d96011b00c010700c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 734260161 1250 734258911 734258939
    0x90f0c090507030b1f1209051b040c17090709020c0f1204080a03142107020d08130305030a1b020d02010609050c040b030c070b040f03030b0d0302070513020d0213 71
    0xc102058240340e11501652140c0c00b90b17500d506003528004164001076042102e00704100801107414605100110090020114a110000c95840745860300ea402213001c1c00140d456400c923441c00100303031102a801c030150a00c1d00c81d820046407021364410b15640e00c4860140e80000803004083d4102e01201c000280f4100000d034160003c01045609080c038090a907601d400000102405100c80c03915462080b00800f0201c41c200501c02c0e5840c038020131048120001100121451000b62041d5800550164022581c5c5481404242c0d40030035a50b5031503034125031a070000751217254501d0729040b080254280890010b0425034a0f68010010080c0e42d04c1c0c0203081d0345a0354003450a4078988414040d40c120010101c2d000da550340d5982998a84504030f4540051141035030107031640040300180000c000300381c0d12440f1000d0107564148000b4a48504118400101807001230142e80420b10030041400c0400c98090f002170844001814494110021416a480190404150b049001081c0030030340c244030700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 734261411 1250 734260161 734260171
    0x3040c0816061b05030307050c01060801020a0e031921020c0a06021b0603090c060a14040f1a1201050909010e01140a15080606040b0f100c050f0a030c0b0a090f0c0905 73
    0x40c02c0b00004982c461684901c1b01816070000c2100000f040c002010302504240c00810b0b00100841d90790b071607540010050407900003003a2083c0903001c50603800d184d80310481e00a064000003d07403405e00d0034841094850340010f03620030960003001010030706071b9188900500140f03040d070068030303920700c064520742210351149440503c107010078001e10000103000145081e09040603035103540c2d202040902074444102d003003c504d5480100040c041240c13243d6440d201c04546202810720701c0c1021101e8a89054002c9690701154000c40800411061505481e183d07088070401c000040c0b003a1074a02d84500355030344400100000c026100038440c003100e10740f00344640518040300c2040100d0a190f0f13015102c1c14003034981c2d0b1285880310340301c02080c0d03904102d01600003c010590881000e56200c0500040905601519540503202100d1114030f07010500d0f201c0d480d81940c5141e001259a921a058403074042c1c4040c1c40e0a56442c4071030009801e00d0403a0a925020b1051415210300d80320004044da900144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 734262661 1250 734261411 734261447
    0x30302100c021518030a02210703080624041418040201080103030c021909091209050d140f0312090f1203010504020a23070302071508040803040c081606 67
    0x108020a0300e0380030422484801d0f035407000070030300d4440b005007008070b6000c082204503034040043c40d4030b02a600040c00a140c0e000380300325103164603000d42030080ba034010000080c010500000000c0c6903441e140d41c4034140d00102d00c2d0b19000c4480a0310078103285401581186865402032040c450705403030000c1d40401030550698a111f02d41c681030707000900c0c0ca401032000400b84800d508154003190342d1041e0004140307503030604d1307010703050342d20304420f809010904800d46500116500594070303d403007810003405a9802420145199559944030301109041b00b9074010079010305001a03048480900042c00c1c800350085680203d4208540603604100345010031102c1032780134640403c280c801107020707070f811030303108960050320395144000130f581004080ca00804a01071440c440004070000380040c210b424065800c40e0a520780700e8051012a4110100a0010400780c0d4006000074005400455102c0e214840f4041c04507904c6d44114640444a040e400c07110001c140c041c420b840d8460844c90000c00c0d00c00c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 734263911 1250 734262661 734262671
    0x60c0216141c080406110a020405160813030e01140d02030907030c08010c0c081b010e21032203020a0501020301030809040c0f17100b0705160605070c18060e1003030210 74
    0x1e82c3d618858072680c401c2c001805440c00174441c03440d40c02c0c030425100c1600600b0600113031a100c412840f1105800c130320038011071400c00100c0c0d4460b009004040708258952550305486441000654022030040c21a1900b0101001100d10f144903500180d4041c90fa148002d0101c84d00314035044001070860340018601d40e1610382030490319070f03100c0c00d2040c0081d00303c1a4175590b004101c0000c1071052100c0d0039000ca6609108140d03140b2007000401d0080307108964a9010600041c0741005070511042d958001c91401060399810080008403030380428601c01d0040300d40f0700e60b40d55111806da8000343c0c0180c44000000c00c0c0c0280508150180c0350140c85645401070348407101510243c4980c0764400c032a40c0234420080002d042c400500280c0c0040c0043c0465951651401d24026540f00300002d9803000301000030342c000840394001d0060b02e8080d41d11100c010b45032409d020b444c1d4111180602c841850360303218100020420100010345028180041600e207941d401c500700030740f51400840b0780b109468944 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 734265161 1250 734263911 734263913
    0xc030d020c01051e011505092d010f0c080a0203071b0602010b0402030108030706051914061e1309080f0c01020702010e03030a0e0609060405100c12020a030c060c0216141c 75
    0x3603815980c0d0001c803a022204011b400315400d00400c01d0f11074111556100d083c0c0a01009620040090600608414241001001113072255043c06051000c140c0b82e1041c2c03000541c15401400f074060407441240d0a0840b40e8547d0801005040a50390346c640e440361043c403500d079083c011216440000c0e0b0b03040d459949020040c60ba07030f104204014000940d500046404001c80800d10740550500c1541030250410702e04844042c10340c217444080c4074156880781140382c107801c002c0e071400c104402081d00c040007200d0303c1080301401e080704045030310107010044407500948840152104102500006881d03520501c0050030705d80c07842421078800d6006218072005580d1100746980c0d4941d040c0c403426214103419000c6010760242e074000c217070b00102c100004a200c541c00309100031003500492100900062194040ea12100810b10280c009072a000700d0300c000c90303155000007500d8400fa104079a901512485001001c0010380c00503014415090213944883c50000313515024050040c504003510201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 734266411 1250 734265161 734265211
    0x1801030f05070f270609050702010c0306090e06160e031c020d1119020102010603021816030204050603181c03020a030c0e06041a04031a07171e09030c030d020c0105 72
    0x511500c492414455135845524842c942d0001d00c014400f0300d60622850816520107030180000000160001e49411000164a415400ba6000c1d00c00060090951038440a40103000003001c00101020300c0402c00345a00c05450070808685403000046101a9540704200c0c000e041000d0361010404101401c40403020b0744202140074080040da20340b81780d00c3c9940510050740034040d03c0d4030207503000c00081c2c4a5043d078450700b40c100c3d10400380034030715041185203910150101c0c01603020319a00b00700d0034000200401c412141c489409103c4004075104460302480b008000204248d07184c000035004070b03840d04807a800d8010b2507501d009a0528400c0580e001d004a400780c001c43c4910200759034051690070030f030303160307041110065a000580c07110000c00f00340c0e00000c0704c0419241c402c0002c83c600c8800d442e80700000c9220b801008c8125044c0c03001d440042c500c542d98500501681814001001302c001404810001840c1c820025000540c0b00d01c1c03015011421100c004100040c1d80c4004801a4201c1e58 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 734267661 1250 734266411 734266439
    0x31b03170603101b030b03122502060d0b0405061002060604020a030608030c1614010509210d0216050907120c121e05150607111801030f05070f 63
    0x21a2080c0c03100c040d5181400246031541020056940d14070b41543c1c201c1080902441c0003581c078880d1401c1c40a034a030721003895607030007088074040d003200d00a0003000e6200ba141408011144072803140d00b44200300c0c0ea00021034a6100c81d202484140e80c9002079140b41c01e00340526540080c04a40c0c02d03114184000010392240c0001700140c2c0724660028648180b00e0081e801100030f4290101200e40b50b100c4a0074842e40c0703c208860407440307a05940800138580c4102841000c1d602c0c01a942c0364203228180d01030100a0396a1003042d0400c88098004c95900101005050810760260780205050381d45078094940b80d10b92a042103014041103410480c0481e04403140c100304070b0ba004400542001c8203941281c1c030ba5105151415111300300f2103c080c1c0400c10742540102c418001c8000c00c16602c07503004022204d0744803080c458000314280320801c0440d42c0c4091810a848014210707071044001c40c0c0520340340c500260421142c80559500e02010f010007003103c400600300c0030000740304a0f4105480740500003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 734268911 1250 734267661 734267687
    0x606070b0a0603051e010509120a0309030908030a09180c020a02090a11030a0e0610060905010e03010605060c031306050c0703021e090906060f0a030b04030c020105070f0f031b03 78
    0x504001107a0030014940c04030b0020f540080036160707174890380c0401c1c003021035003280d41e04007640c01c2402040352001d020070041001d01c69620007034a020040d42080d0082c05c0c0510050f0144001204009400d550601c0100074400380790b505c2450305420001c6048002c2c41040b50843c0c00d91405214030240ca030005002409950101c0c1c5907405591001da00c54040d00500c1e01e002e0700b0399004001c0c001021280d8000030310022580c0190303401981c4643c1d425910011604c5440c001a0900400b0010b5500076601115203c0b405000461070907203c1c0d01090003940550480071741a88000b80680408003101c62400282080345812894403c252405940d142018080a803181150000040320006022100e401c132000213003801d50146072000407e0f4170381100b00c0314540650901e1908ca42c507803410100c41c1054a40c0454040748648503910111292600c1280490600c03004100c114007042040700000010340c8101c0c00c076810500036240050054084a1482e20100c27040c3c04200d0000341c100e144a1024 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 734270161 1250 734268911 734268923
    0x1302010509120706080703061e09021b0f0a17070803010b1605060f04020306070507030507110a0503161d090a064205010819090203150a050a0506030105060607 70
    0xa101e5440024102000c142d02c0c6012900c80d00c0c6000400c030743c008202c14421005a181008501e555640704600209444500560408941c41c180240c003001d602801c1e010b42401d15a40f0081e0300000042d00d0701030041108a00c0f54440c410100800820400b060100640030f90340302d041001c550307241001e6000601035400c0c02a40030444041412102c40760414098225040306d81c9800c02c0e031302d0300001c107400b5141603000b4060320000a851074002c00484d00c4051b03140c2d031094600030300d603100d810000d50015440e550141d58a600000c05a40801c180c40d45d601c44c060b1380307644640c5041c2e442c00991070200300c80400300c42120704100381c40c00d01007040352060341c0041001c6500e44814150046c0303e43c8508164811855113401000e08428604000d82c0542d03040c502c1108881d06c1708015190540219402410810b00780000039408084e9040070001510140071030348180c1c0e000c0f0f00d10708279500885804d10300541d0381c0100000c0391081e01482e80c103c00c042c2c00030801030a1500104100b4410310318041c01c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 734271411 1250 734270161 734270167
    0x9040807020d02060a0305060a06030c0507020108090f060c1b0106140618150903070909050601031407090c17070e090106030c12140f0a020412030c03050c1f0e0613020105 75
    0x540d114030950500c0e00b42e0060004d40d50740520040a030090009880160103821600c00101d5268002c0c403e480440103191140f60a022150f03004440300c1c0340041820b8418040c2099000c06003400700400d034014404049442d4880700049602000049110401d200a0381444c00420400301700d52080c284042c0250342c1c0c29590741c2401c0c2071040c00c66034024201d4000c2410b808030700700110340d003015107071894044083e107200a43c0e0708440030650b81081c0e0068103e412200040001800404005200c880d240301502e101940d101000000c403a0408810400f16074111400e000d80740c104d10029500620a0030804041c3d200f000200c0d0740030105006500c24555a1301e642194180140194690408400e209110340b88c0e4000920b101d0042c150b800c0040340c0c6241c00440d00c600c200d40291001c0c0c03130200c800001300041640b42124150302429080d4184881080183c51440040c08220342d0b810042c0c00c1d0302c1174400d5240c42c030f0b000c0b02c001031560b41083d00054180602032505044800c4c4007902482e00a803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 734272661 1250 734271411 734271413
    0x60f030f03030e0d050a09080c090a0e07090c03060906061b080a020a0203031b0c09040f200301020d060302030d0c05070e0a021b060703150e06040e0c190503011a09040807 75
    0x140200701c0030541c84e2080b40c42c40c00e001d56020000340b08940c0e1590301d1040295460740e95641e228480f0031031513401607090300081c5a1a41d6a800800c03200c0b840021217201c00e81e00c003942022140c0c03840070800000c2d224141404074403590700800c0001d00c000e103084078558115821802d20700d020000c00a100f0140015201c010501c03c010a10403107800601ba04c0e6201d005c01c20301c89020b00303244208140e6003d8038444174020f24201146c1480369030030010401e030110302c6039a0044204a0714908448404070100c0610035038409202808143c1c4da55400024694154010985081034079812081049100c040d844002040441c03030b8400c81d2100c02d0120f695442d03c90160004e8000e0000d0061011103014a51280c2c0340006403940c011541c40d2005c1010301c5114580b2071070701e0010700401c22040007400c00308040d07040691200c1c000c2c1c80500141d13420a10200005401f00e01c020b2480c02c80c00c4010301f41403085180a10801090f10044d41d18003503000c42120200700f4002000700081c04607200460098 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 734273911 1250 734272661 734272667
    0x309050106080f03041e05010203121009050115020705030d0c0b06210615040c0f050304060e01060b12060d1a0403030905030d0c180602120f0918040b0901060f030f03 73
    0x400030b07148031001d07920540304032000c141d5250090700c20403048040c8000c148003030700a01e54403a000ea0358180d001d18030707001030040448404000500084110515000300107180030481c0b05513070182440070256030410341000402450310038581c00a52181e003080c000c4c010056008091806070fa5070284003059195200c07000111440381250345c4225103681e02c0c03012411180003041841c400c403001e02e21003125058190521088401c00e00300700d0086843e0780415640c3c0c070700500213994070511a44010560412054080d82540c0f4140d01814030500f02042d011180700f404006294030820680740043c804245444040108200300c841070100499800440c092520070303041801c02541040c226a42c0c0c1c505c104141d030081092151200014013854451059a070242007840308031031300d6034018940b4455421465405034000520744030601d0082001c41c40303a40300e41c0b1031803d5074150026280050f191504002403c00e400500c1c0510f0342e40740100601c85031007444410b03001c1d00c0d00142003515482c1949401c0d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 734275161 1250 734273911 734273921
    0x90907170a09051c020a0b09060105210313060306050112020705060c1b0d0c03110a0b0a0506130f022d0a120e06090606030d14090402070813030803040215031603090501 74
    0x20038014882c030001c2c044c5950001034600b10144120a101c0440c1c0e2084607a0b42c55034402c0c041e066103c1100710b803001034809030b14074005a898415007668940214400341004c0c14086c0d078040d80c00300f81c651804101a681103c005410a01404415403600c0802e03500c050721802c0c01007aa034a040c5c0003290303861128903040c280800f64000301089481841ca4076001405200307541d502100000c2c1083d40714280300c00c0c0420002e0f01c0702d520208580064403070300f480d00064040204055080310180b031400b10810304600903284000c20400b8010780e01c046d0000c0c204480d40703403000607100400d600d140c2110903d01c0d8000f00d030240c080d00d181c203600c0440d202c2d03003250203800b0a01d4640c550b48210340c1030080c103c034085202c174014082181190b180a030145016158203006a0311081122400d0020301c48506164005248817481895040d14010301050102000941504280e40c01300c404400c000c11420300d01c1e4a103450440c410300103030a41ca00010440e103400004024038080548170051350381001000d4000f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 734276411 1250 734275161 734275183
    0x1416050c06040902033111060910031b090f060e0a05060d1a0301230603010204171b0607020d0204020c07090501091a040b0114180d08090907170a0905 66
    0x1850b03602c030f40c1c8616501c042e420903a2003c410384410804c0c1500030704501e1000c00c80380040c07880e81c100441c15441d040303401a114010103420403010004500d0998849800c135030307240700a89001500b0f4030b0003990562030b04038802949060181d1a003040c0860400041d50a0442d402c503d0100f2040702d582012920701845a4404e5400840100d4002070a8000e40c100c456a5650200350003d520006030815083c2d440e11300d103804c4c070552500c0311074074849601d841c1c19500500240001d8581960303a501e00d10346026103a5188020f401c400702d4080b00303402d00100074105c1e2800f29101401c014982e000501155000e01000784125400500c4100c05401413101e40300a00d0503000c100995a90340180c074010b001d001c203410a401515a10380381d006e1500b88514100344206a4440b824038142d4080b0004651011403488141c4107c1e03e0805441d6a44058814405100b801d502e612032215206000415001500107030034007541d036411803410313440030002c00d5112051070404200868182800c034140f01c08940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 734277661 1250 734276411 734276419
    0x516020f070323030412060207051b06030c0a020a05070602010b03060a060b0f0d09140309131a0f1c031e020619020a05040b120603060106050c030901050318030d090308071416050c 79
    0x2041005101056001e022614055404e5540c030000f1903403980c40d40cbd407556485e15480b9000b4004100311580030f0026180b200303414011112202129250740d481e01c2c10652002c40141e45684882a840c04c092001e1504001030000a010041c14500d06209500680780502c02006010440070210f0707445400003407410703802010764204540480c0c03060791a540204842409168040d101041180f924412500e414400354480003c0400c04030800584001d07403100a54000c03464a150504010b24002d40400c1504c03d4a4464000040900840c2d42c28981460703401950041c1c42040561000084001d41c2082d103540016036a182107881030b51680a51303040b1a40c0114080364821040c01052151400380000710100c801680e1f854404071651f100303220740c00d40240c0090010f81c0003940200061038000d415940c014824242c80b0200c0d6107550041e8088000359515074001a06164001d0500c5801c20410315060400002c0500349081611505805005c1c6400c2070a0b41e005204040c040341300d800c44024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 734278911 1250 734277661 734277689
    0x30f022a1c050f0d05070312050a090c0b0a1b0f11030f07060908070b04060c170d050906070320040614130807060f02071409060a03060516020f0703230304 68
    0xc10510764038624010900b055204e01a90340341007038016415141c2480d4190750741c103648420401d0550181c0000f4004243e403588401d83c50300000c944055100c081e00c4000c0340b264498141c0c42004101380c140a407004240841c0303042ca0380c04542640d000c08212600200c80d1703140362800601207840e0414080001001e030040101c08204d85500030b14400c1112003081c112000d0310b403501c1c21034030030f486140310307400100b220b0001c5c801c000740314802101d400000620200703050030701481011050303030f104031403880041d0002d030100060a42c01d0711980108641444000100c0b880100c600075483c440c0f4000c0741c1c180802211040540c5a040c01160703d466184103891040d60b6032400345940c0ea105502619010030702200700c85440c0c1d840002c0d0301080301c4010340060700c7c5000200911007a9103001d808140c1144503141d02001043c21402010301502100c04807100e00340c900c6800030f0828240c0c0c000b992240c0c01820081000c10300300212140c2c0021054004078200d040f0f48003036881d41c03103180c1c4179041900e280 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 734280161 1250 734278911 734278913
    0x8010b03040210020c2706030d050913270317010503070909050c19080f030f040b0f0d05270f1005090703152007020a090b03160f03030f022a1c 63
    0x40c2c0940141c03080d88215148881d20390340c042503192523181c042c450000d0422f0101e04e910f440d20070806468520610710000d1034407900000b038810380c22500000746416101d24441c1c420168042901c031600107510550403015418035001a03100c00706441200200c0d0741702e4410409100041c81620f4508500800c0954400c000d104103480074101c901c030340e455a009465a04400718008070489410500440b0b54a1401d424800d069801c1c0e004850302c02001d8005111008000c0720500c111070160490f200280703c825807540c3d5021800c2512183d01005401004980c00186400100c0c520020701450021540e9603030001038604c4d1100d190700162140b882c101c0c5121000b20320f940a40d031503c0880c80c4900725180c4540e44c0c03600f02d200744980250048480746042201801ea907114a2007510000d040d50040e54092903445240032094204000c5100b8040041003015000100c03c440c5811600150640c0d00929011141c130700d0482d0100844801c0101c5440c2455440c808d00c0200703000c1c410032000350340c40c1e5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 734281411 1250 734280161 734280199
    0x926160617070806091b13080d0f02030301030b0c0c1507030f0605030d081008030403110405061801031b150e032b030e1e0609070608010b03040210020c 67
    0x4a204840c04150011010412070500020542c42003460780c079044140e0300c5540c28003281d4000200484549035881c0c2d4080c5100c45000000d01c505c80c202d4184050140c180011981003030444003284083c00320b0400b07880481034021058904403a0411804001555840300d418050710481050700c810740142c50028012821001e022130041da519601004000d104040d484121000750041c250b050b40100e00148000b07105400381070340301e0f80340d150110009549060013031458200380c0040305c0e014918503801400d818940714542d84198125000000a15075101d80d039400d200c10b0102030031440b100d6014070318004481c0c0b03080c3c0c01840f0804c1240a807044000008003040501a03505120340519015030902180c4500c5050b41c40c000003222054804d620708069000740b120590740070403402141c0000c1c1c00311087c44d04140012107818003400d03481c6081070019090035a180c0149040c45500300041c0103102d03a000c02d43c0d40c02a81564083c5907003a0031003060381b034244091480c65100c07940c0380241e800110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 734282661 1250 734281411 734281453
    0x504051b03041115041403061306090201111603020102060f07080112170703030537021303050312010f0f031a0408070b0c09040b030114060d02180103030f0f020307030926 75
    0x10b141096a170400041c0020140c4231841603a109240d00d05142c0c4030380100d40e0075880007403940c3c03050410860603084000d0250400c44107041d50215007030703241800c100355601885180d911503415070304101d0074079003a80c01610090b010b0185146010a82504500f084075110513001c1031050304d03100548850302458010003401088411000f0400d94080501e140307a800e0f240a100c040b01c400c2d50744032003e00c1000e648001e41054821a29000040b04000081340c014270003056580d6075401c0d442d20079810070b86070204103a05a40400d00c1040001400c20100c2c181d66000d0034030200101ca061403a454a0503c41981c0c0a003507005440c850018090005e08010000104070082c0e09907014080720591004145c00c070762841a084031079884a0300002c040b4945640c0402c8a50720041c0201440041003860503844182600110013141c1408120040d0940ac00719044141202c0c0c4021407800d81d4075500146442458460f00f03c800c10402440f134584103034030713082c009103650038012109850280034000d505c00ea = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 734283911 1250 734282661 734282669
    0xc0f0306140417030903091f18080d051305060a11100b0f0409050114040c060801050f0d24020a0504090b2403130804080c01090504051b0304111504 65
    0x6072421121a8210010360400c500c51a04000c00441c0711504a184200503440100b01e520140010484203150307a40b6913a82d12400301b00c101f2201c5000031041c40c0586600302100c80c80c250700445440c03c10036a10002400380003100c0500d4071546800139005a04801d0140e5002036503c080041081d0b103040340d011001c040206010300482d000c00d400e22481c04101c4c0c103602c10f06034004051032000c881504082d001080b24520500c0005103040e2252402000c00b2000e81d02164142110f140800c05145d00049182c0906412242502d0310312040000682c12490841c0081400380c29480c4010100315800c444c0540c010841d206660346c6c2200700c40100300c1d07031080c091100e0051420039102a00d003001c1d85844040740030921603d0031081c804016216076080144641d422228901000000a40000c003a0008203141e0004108003100b98001501c240c1c03c6402c1b041c06246010708008503010060f54000d450500140416135030f8566060090212040c0c100c100e40001050f00d6500c85010850b0041040f6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 734285161 1250 734283911 734283923
    0x1603051f0b01050d2a091508060105070b1317120f060a0605070f15020306090f061e0d022e031406060a180f080d080129070c0f03 57
    0x1440d6800122400d40c0c0380580003541c184882502c3d01d145600100b01101103000385c1040c10382e142014951048412015800500e00040c00c10611040041c0907003900451708050003549045400240680602030000c1c0a42021901080c0e50341030a0200e150500d410a081e11129024030b48030743c03641e0b803003044140244013400d00000d1051414440301f07030058130010701c0d017082180380000c1120142c020030010349070f0308410701403940001d48610210003403007e09600980c90b85400020001101c000402016814076803000b0049580d840000c03105000403c800c0214100076604085103c500036407070000c0d084010000032000402e0130700b00e10845000303218007041110a07078601c11000d0b900002206c0198804ca100810743d585040380180416004524200e4402104107061010003810743d400384041c0ca40412041c426014180841c82c1d400d4a107041c21282d0f54034282c016020255522184c200801c550301d1207a009050500480382000e400c80e00301205aa25881280c0500d40180b0080380c0d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 734286411 1250 734285161 734285203
    0x71223310203071a0c0a20040903120c031d010e0105100e150409061e1a0a0b162901060c080a0f09051503041505220203160305 56
    0x10004000c0d0240281580640a040c0303443c94481c01450180c0b0480140c0080c030300c10b100d1130400032420401104214003401e40240c40d800c241c406210000b6034600b460780200e050448280120740c1042c20000b00f00b07500d078000101001d00103030443c01081489004200e00130365500038200803005400a40d40e010942e4000c00c07c1d07807910340c1004108041c5120309101040c00400280c001011100320001c91103024002248041c9076030303105000c9501d081d1021000c0d4102e1620340800f524148900d0294a020300e4001282d03629490000300001c1c464414128010000500d6a04d468140d002c020071080c1d000914800381d400364034403007080c0ca20b21025109180046400055100e00c280b01030203001e0f0700903121503d0070031121400c868070b044544c01102408400f810010351340d01c82e82c40500c030344240c240810b503d0b07090511b40740d0212448820740c42b01840c01c1400b0b1000120350a901c14090450300320814210440a101281c20b0072801d0200b99024003a41ca0000300380700c0042540810b0854007000082 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 734287661 1250 734286411 734286481
    0x4170708030408120304030c020a03081c0b0d1b03020d0c03030f0c020d02040b0d05030f040905060a08031207090b1b0136030201020708041509080105071223 69
    0x40e80340203e2041c0e5900d58400d43c0326441c0462850001e5030030500901d0700c8692030060760081151482030b5441281c0709240000c03205c8151400e40381c943c1d62044c4044e07062003140340c1c05000658100c608031015127070458036891000e4030412400f00c40011075020707028091203596400d242c00b00810500c419400304680c5071141d400079206d2894110b04c150300405207100801c0304e4003408014404e0704500354000f400341e91110046801040688001d040280e14141d81d0781c10a01c00b602920390242178540941c0070030000b030000380c6000c0182c0b8803104a401c007280246e940d00070116000c0b0059441140c50f04800641c2103185501d040c0742d60596502a4002e00a48007051101640c2c6614204401122036036802040307481300981d0311454086005c2e1001504280d515110500994441e03480004144060b001440354140c000b030000c070003004000020415460440070180907801c2030b040c0c03522440d640d28905042c0c030042140c001044441c11034003201c6468100c031078642d1803074621080c03c0501c440b415100c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 734288911 1250 734287661 734287663
    0x100503191116060c0e030a0c030b06130204091a09191a06030114150a05160f0b0a0f15050609060306041b170c030c191404170708 57
    0xa8003505648106a40020301a0044802404440000d2034030341ca0801000000e4106890a40d0102d030150340700151a251502d0302a040c0d480f010f00c198000c3d08201042d5000c10313502110242100d03041461000c143d0313114070006020100c0b042c20709112503c0468042403220041c5c3c0f00300d420210010700d01100581070403c00c0300b000812606982c00c0d018550039509050416009604250184520317071003140080000200150026000f4115203503907020507480e80c0c40d18000c43c2129008075080d051416000c03c000801d98030902084030301420140d0549410003c9819a40c003601d1b4001140c1c40c0d0318140131003840081c09142d12503074107140c00c01100e1300e03a5400c140410341c11100002c180c00d140010302414880c1a410040609a1041da181d00c01d046c01885c5c900c2e0b00f0f5545a2503a980104c058041120030281a1301524401040d0003e204000061908004641818001d8003a2102001c10300e081120030041c1044000c07444a80420001040b41081851040c68051482600e4003942c07604201c07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 734290161 1250 734288911 734288917
    0xc060e09090a1b0b070b040c140a120809040504060209040b03010608101e05180105070f08150d0606171c0e190807060c0311070608280504030e1005 65
    0x704060b400612072080080c50046000341445900c07012030240301c0d550389404950f0f8008890035101416080100700420100e00031140241c82403010110941d044107010079030702000d0b0300600e41400198942001441900b0059a410a000400c20f100c10700c3c0a2030200043d4208640450150303040108882103032a06024000a5800510080c1300b0004800414400b030301d54a00b04900070700043d001c5d600d041c0341500031a4804c40c25000d207140040820040a400c482c0f008044200308004902c24002c07040e4021425034120b03058075641451701c0036040010b0109010440000d1401c1c1c0b62110028103007114070782c16a881e07410b003811b5455481280c9414241c416502e4030b42c0b030000b01090034554040c0b920883c0c180d05441841d031a0420709482c4d0103960324001d084e4000c1c10101d00c20001c0201050ba04c01c1c9026481d20b0003401400d00e0516101c2c0c080c00c2040060316803034112018034484014450385030b0400000160080040c00503062170308014200c280d90f0759409001d0015000300102c00e5000e9012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 734291411 1250 734290161 734290171
    0xc11010f02060c0a030b030a0c0f060518040c0215070905032e051305010906050604112a03070203060c03070206010f081b1c0b27100e070e040c060e09 66
    0x70b400d181d582c50502c0001c5034801c0101000307042d910050654181c40810003103070310710703c200140c8501a017441d90124000150707174089010400100502d408101c41c0100308080742100340c4021500000e00f040581c2003200c00c40c04581c00215820401c62010340c01800c0c0030403600300707a06440c2840c50100818030010000b28103009481a070040c1040328464a502407070703001e00340303082e0070003900000e0342d5060035148000d1058968584540a000080ca0640700c0d8000740c0c102d4015130787c0b805000240c0700580305598101c01000f2a84142207810049060003203410b03031036005080e6045403500d0765081410b070300291406001031080c80008a20440e5500f8040300f42c07000980249140b8404d03039401d00050301180700030f6400c004104401c540b111000c01c0990006403180c000b1000c02d1514101c602045119200014404520901d45042c2c260b004160b07a0040490200d0201d01c02c64080c0c851031a16030580d1140e6604002e4104120612050340d1041080d2002d41d941e1100c50024130341000f04283d020b903a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 734292661 1250 734291411 734291413
    0x5010615140714160905010608280f060504060b07060507261003150207200d0206090f09090616140909040501060b0406020102120c07080306090703090203010c0c11010f02 75
    0x41241c000c21900003c45052508410440d0f924074003640f040d903107210165010359541c40d00c85006008440d0495183c990103143d5003220081c1d151207801d0300a00344a40803035644803da0300c0180e04c1c0c0d080b01a4000e40302506000d48140f20490f40d48103200c2c46648000c1080c0e480c985810003140e05c0c02d1085489d03100700c1070070107603255454008012a0001140160007002003001e9040d001000640d218400381c031000d0145001078a178042400c0c01182c02c9140b8202e88011604203d5201440d511042c00d105c081e901aa101500c3e005c1c001c001c10350980a550807598440c6015041281c11031000401e00d216810f201c034040c9541c0201c582c1a82d000c000d0840048843c8400e1016400e10f080c07003001c45a10601680c0045400c65030b40020b00620380c06900701000503500003400c6c110003114205201e812943c50714900e8a01125625000c5041c08082e284a110b29100004207048034030035044680181d800800801035035180c0c0c0d6024214084000f0211000d205002051500c2d41c0200c1480d09150041c0d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 734293911 1250 734292661 734292667
    0x8130206030103150f0f1a040c0909020a09170a17031603090201030f090b070f0207152001150302041d0a150e0f0604060b09161d0d0501061514 63
    0x254480003110000b0004140080d85c2e107221410780c4070306004502103005e1500000686000b00018011400b40000c60356003e0b50520148269299010301040704803110348200580b1aa050401100d40711529802510701101038420701c081a04045142c06042d0321400b07051210204a10341e00010340070488403c47e40068011048070081e000f078101c1d064045c414907000804180120f03003401200c4407c03500341d4506a241c0c00b002440381e00005088483c800750300042100741e02c1c0800750501d18192840020402000c550200c1204001c10441c41504031030f08000d0240060506031034050344924803041c0d06c101d00708501c8030555a4184421010342640c000a070484540b140c0326008a0400f000b48090003590300d040800c0c0b00f803414030281a030b01c28041c005d002981040d0500c1400d444070340b003c583c4a00650806e2180d03201d94403101400040d01814045421440351483da5404090304000d6a0400c0108403007204002040d40700d0400d6480820108131560b0b074a5000b10f80c1c0700740c02c0d000790207440010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 734295161 1250 734293911 734293913
    0x11010f0f0c08090a030f151a0d1203020c070b09011d010e091005100815011e0f050906040b070201080c0414130e0312010305070b070b2403030c0a0308130206030103 72
    0x110010700701400f029040b003541c0d9940e0307035540d08114090303002641e018000012003500d0080d640074014500080e00704150740340b44000002102103003072560041069640c00a0690407500030380507600050079074010345150075600c1c0700109042c1d010342e1145001510443c0881660102c1c00646a41c00c030040e500d45018402440c180300c11503101800742039400d80303007032400500e90751b5103c00c000c4a010030b0b80c0d0328600d908142095070f48140e000d503561414004001c5604003a000e40013192070125005150030550100540010744961007a002c54640080c0700290100750020120001c02c1c05074400c0c1c2ea416001d0741c078078520305524060f40c06400184018007a074410985456000107104080105001480107a41c010340e9145901c20740f0b00c050762180300001001400000e1104400418004038040d14000165507031000c0180001d10300c840722040807291000b012900f00c4514010345024003140e80d11032454940c40d5946040e61001c4000508100009503280840b07100b01e11f185a028081074150790031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 734296411 1250 734295161 734295173
    0x30210060b031302150d06091514010c1505042405090c01031104050405042607020904080a020a1205130609050f10050d051f0b0a0e09070905060711010f0f0c 69
    0x401905a0348092040713031020020310808010220700c1248180010814070b810010000d5620b09094270340b00e00c00700704080000891401402d61154400d2800c00b00060044ca0540319043c0f0a844500342c142c50a4200700c104003050215a200344e250b81e021030100c0c01c020303000038152201200c9400e01354010740c04403482035000c1d400114481d400f1403241810580c462011400302c8034120f60586140c40149000501d0200b1000404070420411488600e400c8154010407454040540000c021b0b07080040e844000620901416a45541c0000c0000020344410384c018115041008440701c3d40070001d000007155400341c941c407000c444000d0880c80f507a0b00740710b042040e0400005040401e0110070441600c001e0540c0c03203141d205510088011816645000d0111390007441c030707040700d2a1103004200d02e5a000760440b4000c6410001140d0440440e990107504940305c0642d0381c802034002601145a404025410f118903440e0403007a84e800d2092220750404413030703a80c0c0d0000c8650114200c1c0300c0120106007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 734297661 1250 734296411 734296441
    0x1050a241a0c01050f07030c0206010e010303120f050702010e0f0d1205040c0f0303090e061c0b2d1f06050409020a1808033606030405120c0604030210060b03 69
    0x342001010b4142480302182d1825500c00b02c840d4030540d070f19142080052034042c4035842408010744003c1c0740c10b60400700d00b1074200806001c0a428070118040600b44080c480d0041c0d82002000751007800035090826001c0e018007482500c485580c042c0127480780d800c6100045401066840b41e941138034110003188008000c19018006170b07009000c00780701207806c03c8848010002035100341e0303c040819240084a105020700030304860302c070703141901ea0440c1c0d400081d00c0000145822a4552160780c0301c9484132000403005c022043e03142c0214a40002a51010481052041c1c845582c1d20031200310b26029683c5a07035150003071801141c420300051060600940c06041c14000c581450a40c02d44641c404c091100c400c2c0d0b008540c243e0000507046240c082d20b004407900000d1040180c00c421401c0321a40e440401114001c9006003c080002003e2143c00c0207040c11000d00d4101d10341d070750005440001e4481204841c203a0240c4208108041c0700781280c42124100ca041004081c04e5881e00611603075511 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 734298911 1250 734297661 734297699
    0xa05160501061d010e070518010e0a2d15021914061303021b0a050d0804210b0c0901020c040b0f031203061207030c0303051e030901050a24 61
    0xd0b503151404a18141a01007420a4000c0d02920692562429094110040d0010041801c0010034070841034984c08102c3e050203000f50900f8a690341204100102d0090071059100205010807e110b03c800d0070180792401c241c00c3c1100c948081c4a6072074001c0e0359181040d004a00006030b026680b004584049515003090b46d9200b00d6600e100c14071802541481d1805c00c2d204030403120b04c00402c0d0020107404115240c0c2c0d21103040c0e20301e41c2076a01000080c42202d0107118040c0205144100790040040c10803c9401804401d6a003000300c1d4a07041400034150300c071303440442c0d0300306106003c41e0304880b00d0401d584020105030b00503c45c0f4070109007400050a070701818240c120011280f01041541d0a00201c400c0c4803c0ca8070300c2e0f0712031408000300400710703100d1418030240f42c1040348184003084100781d031501541d4050410310b56607a408078001d54044c50070103078500c680b88080203118652006401039030141c1040c841c2885625070076505802c020a1b8425102e2550103407800400c00380c03410000703405640f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 734300161 1250 734298911 734298913
    0x12060d0519060b0909010504022229040b030a0b0123031507032007080c1204030302030a0e0f130b030f0d170a09050316050109121d060a051605 63
    0x805420300408455075821500326070301a2602c105070341c203092800140c2d6214030305000034090703810550045196103103d01007109074400040c50034400702003980c10402c4160121809003c10604c0038024000e10754012900034840d42c2050308047c010702e4001382c0720310426040300c3c4403e49a40b134943d030b51106074005140440f0044021a8100c01c55a05110740c150000f0a00c85009080c580040000c085600ea5941100c0c126001220150310148600680d94804d0340240c0540d0358103035580e070f442c0c130300002c00c0c069511103e00041d01008159000c0040d00c000021b40d19001c080c500c0003006c21206e06180030000f0740000003004508040405a000088000405000e0310800d11441d00d8603030412001c20706201c08540381507030b120541425444c080f0b0703100120300c070b0400c0038030403594820341c4a20505c00003864414600d421a02885070070760220f050b80b07030702a00429401410f560090b02c0071411104404548080c64607040340c900b000030032039000c000c4655802c0e1400040c8511940c0300c00a130f41c01512a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 734301411 1250 734300161 734300173
    0xf07230a090b030106050c06060a080a02040b041413030210022503030b060408010b120f1e0715030c081302030c10030b0a0b0301030b07020a170d021903050106030b01020312060d05 79
    0x5800c40c02c0c001940070340003035078440d9034a0449585542c500400544203a00441d240001000b40358000300e40c00210b164102e80202d8140301000004019025045c9070400c4a01c3d154140065601c51445480f5418840d809980040c0b51002070782e0102e00800d05007001c00340d03240d54084110400c0b0300500c0000e0f4400e0800180d183741c0300300411110341198001240d10b0303544200c0b041a515000304005451030700c8a000300700406000c103085403964134150254460b890600d640300d03031103002405500302800c0014048601c80e4515880180a0035401c400c420100303101c0300100303505900c1c40d10040380141d0080c000f052043c0780f14082c402ca5406800161080540d030303032490815a65840030503c01011310f054466125415070518059055001d444d032010340d441041c0c040006240b03044d8070140000f010000d06d460360340c203e0712007002c1c0c4078844c03441c189126200c0b00c40c020941c15510540c1a6400d654041003102c60110040e80c3d1380c4516048a007841031060009101d42c900f003a4900310f214401c5040d40c0c0c2c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 734302661 1250 734301411 734301419
    0x6181308030a021608041d011809021309052b1e020c0a120b0c1c0903030209030d0908071a0d020703030b031504110a060e09100f0e0f07230a09 63
    0x448000c4e607610440c3e500300300107400c00c00c08482c04c41e883e403800b0000d242c3c4034003940b500d40e016070840400300314545210340780c205900c15503039824048040c00c00340c143c042c8400c00f0589006900c0710179100c032161101c206815900c10240c0c40c03510010a401513900d5514040441032082d040302d0200300700c94011803041c0c010401fa5900e40e10403485c020400462031581c000d00903c0c20300b600321030080500240341d1052000d140350841710f00440a03c3c9812800008540e00130b0700702280a40328228000760140b11f08a0720044056205054a04803002c200a81d280c0c2c903180d100e40306804000711640013030302e03800384800d0b203084070540d00900c0028883e0034001145035003000030038241404401030001c0d220411080000340110103c4040c03042804844103010381d8141070340580280301206840780101280c0d0005a042d09144e03800d100a4100400300e0b6039696514108200080c80c02c5900030410003144003c00d07600d5002e60030000350308400481038111104002c000300c0d5140c000720006070130849591800a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 734303911 1250 734302661 734302687
    0xc170a060b040b1c14060712050702240406050606030601090608180d021608010c0f0c1a10080c040501050901120615060e030115182f0306181308030a02 67
    0x501140c4d448401038181d6035a17810701c07400d154403a001034085a0004030030480000e40c000b288850884524100150645801d10200d25188a8103000080c204030103030410385101c11103245d144524410702d03042c0207980c0c030740d030a1159030b020644040b80400e60300034091014a005075007d03544442072100140c45011603902c200c0c80c228001c0101005600642c0d01100e104044018110103002614006d21034041c090b18000c0c01200c0710035190b810412041e01503020004051102011004036000201242c1000c80f0745e03003c5d550103882118250710132014551041d040c03074081c5c1e504031600108400896842e003d00c0082c0801e5001085800c507680f0302c5100c200048070484880940700a40e1015508491003050508450031540100075481410341c0030070031891455601d45c11041c80341f2010130048101c00d140d14042014080c41b1480c118181102141c4c2e018000c043c5100707170700456000c4c05400046e41c0341d1510308001d0f2241c580481111208602081d5603800454001c807884c8001460f00440441d11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 734305161 1250 734303911 734303929
    0x9030102070602190c0506010303030b040b0a080d0e010801120b04080f0c0d0f0203030423160b0702010314010815130f051f110304021c0203030a030204030c170a060b040b 75
    0x310b0300c142d40402d00041c480c480c20014100305505080c82c442001e040c3c0c81e0b09980f244140b03c01004c040d21000107032095142c5800c003907501c5102510348400c1c14bc403039203070a45490a44d1600c200040c0380f1300141e4099031281d20024122190554600300305a9a5141c04168400040095a000308200042c01040d05108028920144980042d2070310f1200010000c08480ba81c20501086500074020b2101280004400c00a01d01c0540300708000b1000c800042801e00009017071014100c03a030750b6000140c0c5104a00141605ca20036a402c019514000250010440081c02070f0035240d40110031540801c10364580403a0420900c240b6809030b50565680d038881c10025600403100c60300314030040032051034643c000e1040c10a50100034001008038120140f010300000300003a100e4402d4804002c070344814420b0b090002038000d000e6a640b0895040041e01a5000340320413920b03030f1000d642c001410010f04110f064120408405020100711503120030000d0080c0050140c2d100303a4a55950120350b60781618 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 734306411 1250 734305161 734305163
    0xa140303070206010e07020d031d010e010501080105130f0318050a08010e0f010b1c0c0b03090a120c0c0506030a0b030d11010b04090b0105241b0c0a0506031b0903010207 74
    0x655807850041c00c0282803050681c0010f00300c0504030180401590082004a401001c5140020319000c0c0311401e0300c800c0d121048040429482e000000c4030403981900100c0c10780d181c1200a12540d1140540203180c2b9035500d41c05025121500c0e54100000d06c40c980d407050754482c1c0c0504210350358071000040e010f100301d58000d98540c0e55401d0050036084091000420b4030202d54003c000715121000070071400c41c0c01d07070740c0e401d07240d40880480030402001001c401c000d0031842c96070070b46034a4112142c0e40d440c150700702c0540703540301c51442c4500b106215400701c0d111964400706005950b4600414000a80c20181610100035140c0d400c10079262030410403a41c140b00f2550b2034104640c0488045821142c98201079070099040c552078401040030030211904550080d50480405035101d0700c2c00d0148202846801181040000d28140c0364280c2c844004000d5814001d6524003202042048941a5103208241e0480340610001e050f00c140d00003500008018160074a1901e411203001034220307401010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 734307661 1250 734306411 734306413
    0x30609020f0414010903110402091203071202120a120b040e060406020d0f020310050d0f06090305040312020105072307150522030e1318030c170405011403090a14 71
    0x3410002e40c0102c58042c4200070f002c1c00c004924a0940d110100c01441500240d03000b40d80010310a42540c454034400b1540104000c1a00e8580295207481002c105224020300014400e40e409100a50000c0d01107404040315030300c600200481e20b0000307901811a903c045075119030745401489180000780081031040e40b15520042e034903a107040d07504048841c0301d034255440130700c140204000190302101c200e080e2001224001184c036807900d80048500c0c0c1d4035400800c2a0300701341a800c10541c2002c0680142c0b84519807a850b0b0911000c022030807104100c541c0c400041000d1080c00c8141d52810043d480708200755000b0b40303800d00c6030320703024000140044201800c0355180200300707004c0aa441964a00d2442c000d80ba050308070303680c40043c80e038034620b071501d84030b0084200d5103050300191754482086c00300003a40300c105000c0507080140c5011030860341a03075000340f1a03030220064000803040b501a18816110210899041103c071000390704000e01c1001d05100300740004011948001c05802001c076010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 734308911 1250 734307661 734307667
    0x61d070c0f050124060f020c13060b1611040e0a020d0501020f04061d0f010c0b060a03020d0f0c05011b0b091e070f060918023f060609100f030609020f 66
    0x4841891580d0f002c00e080000c4546d40c4100280c1c0401c6180d29558101c45448a81090305110070040506501c0310004c900000362032140d09045400140c4041e006031001c00d0480c0c280d0060006640e002d03c1c2604a0360805010000140341844945c50b0960240b00018140b06004400f510198406d4101002050619010780c0c0160001d411a41041105580e0786c04800002800031701034280e42c031401030408004900007401e0b925402c81102c02990001d2a0340102c4006007000b6041071010417041d5000d505071080070030594051401080e9171200100c0512081c071076038552000c03501001e0301e8129035005001806072010940c03482410f101c009a4044c18441c0c0c90b100701c1103103d11040d03001c0d49c18800c00120801c1504604094150303845152800544d0341e156580d070b2441045010b03085403980166488042003900d5503031403003101210610018000c81e4954808015040c06440442030f8000d1603200d20300b410b18803440d02e5500072002810003264090711141d101c4d003680c001c00100781c140350000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 734310161 1250 734308911 734308961
    0x180a08070503120a141e0d091a091f0207170c10060503030301060c020d020409060b040c0309200d0b090d080609101a0d051801061d070c0f0501 63
    0xf071000050045210500703030300c0c1812008024080ca40d0340190600001800720300d80400c10820003501520b2401980c1090342c40b850708071000020841e0b42d0050f601481c03204144100401440c44071402000120300420b1001711140e5001c0540701618241c2ea50035400348003070300000e1b1940d103000f001650101019502e9540c05010585000d44012440711007a0034580304000319100481102e0565625191941e015402400450300e01c02406070025000b91404e103030074090003c140e100380d6911a003203800b80120b55001800310143c0b2800f07034001c4d10302000da514842022184203010035030040040e08110310ba0009440e10024400201d80c40d900d86e80000e078000a540c0e912070381c5140d024100312240b49850910070383c90311440ca554001d010030010364030a51820682501c1c252022400c240c0014030903880c18610700b00b8800500c022030886036081200105170070501d00605142240c641c420740180d5680ea030400c4460814108041d226400362082c0c0e680402d80038040c0c10048400c214030500219a8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 734311411 1250 734310161 734310163
    0x306010e0402010215071b0c08150601300506031216050c0108190c14040f0e0907030201080a0c1b060209030d080c0f13150206090c060f030c180a08070503 68
    0x3c103034881842d05c100e4040200c0c5a8001001c54000b031a01c4003264000c04581c501100c00000d650005c2d1050b100300701da2400d041c028091050700c2400203130b0303c40c01c40e40c10320200c07c22140a541e04c1020841489000b84e000c01980e035203c0c6601480040c120b5005504005510000d6441f850108400300840343e104014000308100ca5602c0507401c0ca408080c80c602000c00503100d00c0100d100c001c03020f486122400e0780c0c030301c603c0c9001d40c009540307507085030391b01e5880b031442c0030800c09032040c0c2200f21a2007000030b0036550049020402c990301a1240351603540c80c41581c9000b40741c080a003c09109110305072a46810800003a003006c40d200740c50059444440c042003614241c04040c0c0003041040f0801003255182c1482c055600418482c030401c0e0308c031048010b262840c954076400c14241c2e0880c0c4401030444680c002030b070034002d40e41038003070341c2480b5010381c140001031240c1e0341820403c2c071003003003c5078031003000c240101031038040d0403c0c005211501c1030000e070110b90260300203a510f60100c4e00a00513450 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 734312661 1250 734311411 734311423
    0xf0906080703110d061512290c0a0201061a12090d0509010f03061d01030b0f07020c010e01030902041d0c04050f0115180617060f09040b0c07020306010e04020102 71
    0x280800505920b0b203103a4450041c1c58118070518004c1c0759081424040140c5508044150003580200c0101d03252a04107191110442075401d403941d11022076080101a020300c540c4060003245003040300299680140d05409521003841842190b503139440c001403252a070702403500e89d0807050051540d1003c1d81054a03010760b801410030b0740d064100b4031100080ba5000360803103040c0042800c1c0303600a0b001402d41a4002d21151307102e80d440c0e0b2404091070515400c11507445041c0d074810500d54006403038800b401e40616000311001070240c0d000100341c250b03035030080142c903100c1101490042907044031540070409480c3c0103802c82c1c2115105410400700040180181100817905980400c624940340c1403140003003006100c0c0300c2510301e22001090209121b8a8107002004184182c0050256030703110041c007001404102c100701545010109801d807034051004000700000900c403600f0364840342c0700d42c0d058440c0544804110f2004002c82801070710305100c0240203100e04221030b0100e180c10700001e420a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 734313911 1250 734312661 734312669
    0x2120f0c13141f170109020a08150a39080604091e02010504080a030206040c0f050121180c080607110a03080703110414120f0c04090f020a0f0906 64
    0x1400e00c0c401c1510207000e25406940540d410f19902509071403c05203880040a50f08000704d030824040c2c0044001c6415040b1080c454400d43c4c01d0300400d03945805440e20340e440f042050008828160104282c6131075504120380c10035003d0040000c4480c4c01d0000814880d50300202c00c54003845545401e401600070f5481680103a09903000d00c000030342544c800c40f070b03070101042500849884940f21400d5900c81c4003902c002e040e60004407084a04070f403c01035540c030011581181d00c01840e010200f0f030007140140c1d0b20300300d07401078550700c0d0b182d590071034a5087c803082c40200301c0c2c03074a03502c000702e0f00f64201c0005404903581c0620307440822107007002001c0d400d2080081142081c03000048560202131400500d0140503500740c64800015111510114042c03c510740035400645008103011034802040c2ca00d01014000c2180c8022341240a043c0140d10744409a140307841135002884010303a80c1c10941c0001909912a0700700d601c0004e10303607002400f01c601d42d4120b410350300c40100050000b0074144c42050094 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 734315161 1250 734313911 734313949
    0x1060c0c26011406061b0102040b0417010605220c0c0203160801060b0705120307021009061b0f090626010f06080a02040308030a09080c010c02011e05040507030b0402120f0c 76
    0x54584100170402c64402c50b001d2003000440f03110782103003007030080d415140500074056034282d8442e500c582807040c2d07410f250300000441d4640710340029613180410010104407e401511901c40d03800c3c0000c0401085003548403401c1c010445118001079070b0030b0020001240100b502c0444060508038101c1c01c54401303800108076000100029404600c3c00103243c22a200350000c410390302d03940c01904030b0030040350f5808080381d5400c20f9100410400c0301d17042070013403140c02e460002054a640c2811a5034000585009001c5807103c01d05002e064440d80441c034490100d031510b0f017400200760b0800207034154242e120564192142200784141035010042d65004802c0131030035402c140c210340303c05456220141010b50f415645800351010402d00b81c007a22010b1303503000000c1120010700600a8064400d09440b02d032101c42801400c001c509440c490903004a810100130060107086540d82c0b4074141c0c01400a0ba40080c1e071318407111103405c0401031070350b0407404480581703408507103102400b03c1140014258020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 734316411 1250 734315161 734315201
    0x151e12032106030307060510090f1d032a0f0a0c030c05010908030a0e010903061404060b01050f0301050d02031203130c0b03040809090426072901060c0c2601 69
    0x807643c000054071042030308446c0025017030b11040400305620300c007544190700729400d00340c054a0100d11341d13024000521030035104020b90584002e00e240c8030300c681001e1440c90701c2151850018480c111204c25101301540085070a01c00301d012085180051000c0110b40c002c900704424020024a02c400c0c1000380404e090207900e09081001540d01c034000c6012200410002900d001d159a105040000c000d641000c0200038000d074a511401502004883c19100f85080200f01101c0394810b80c122580c402600c08007030f00390303400d1030304010f55400700130002e9a0601c00d40040c0310444a07994010360040050100c00482c2c001d8614003132004050300c0e400420454001e00c03c00c404a40c554003160100c2400702c50b9000c1c0c035034031460f0004044480b617003d00c8140000b1032042d00303030001010042007800c0c0580d0824413440c0400d40c40b21031009030325601c800c5110008004100c26405242c80940c2c1510a1403d03961842e25100c80d1000c3c0700f48058410b00000000483c805400340c20b114680c0c20440d26824010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 734317661 1250 734316411 734316421
    0xb0303070818220504050c03070b1206130e0a12020d080106111f140a1815020717030126061b0c030f130608151e120321 53
    0x70440c01186440355150000c03400c00303015581c458030f400d0210300c4a038840702c10054402035404004c15040380c0464861141142000e40d41c034000503d03c00700c031800d0030700c640340c0413410300c0d10b46820a0240006070421520303269441801c2ca980654503820100c14001e003001145030602a040c243c07605007100654010084c0c1401050303101d0715080c1503480604051400820365200e6615107442000944017142c041340d000a000c1081b60010f082c09500c85820103415140c1940d284101c82005441003a070413200c2482000081402c100d084103d1321340500181025026200c0307a0400a0310402402600c0d400030050020686c0e01c040204072002920050305c50034201e8441c180da484003e00212801c805207030818214950070b10495030620460020350b501c80064400f03d44240d0404192485064196240070031414402c4503a288990300031911201c0101c400c805200c403940010840c0c3c900300d40040c00805a9803170b1410f0b0a50303141d0001d001540d0701c10309080c6a0b05d12000002c1d440c134400c54810b0030300c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 734318911 1250 734317661 734317673
    0x613022704080c0a051c0f050c060411031903030906111c0b03031309060617040809210114070e10090504230103050f070b03010b03040f082104060b030307 68
    0x80e03201d54046030b0740c2e6692035001d0910389005000c00c0024124442d4200001901d4020350501540790f5264880800c40c80b4015008d640754090002d62070090350000001401155020031105509803020701652100008400507441c0400f6005090f0007003911420a0300820460b88100c41d14070b48418805810300342e0302038490704d00400164643c842e190300d680c0000714540e024421560701c1c903080c03010140e1542d40c44001c440038010a11580020a00304000c0c41000354690101602c1140d20159080ca000205d608000204005010441c0d4800a006541c10080300900c03a00785030580c00810700e03100e45406c10000700500010b150480c0244480c00012070129004a04002a26021900852078007140f11a88101c07454200704100b80410410000081c0034000c06c0c9500201540e005642e120340d21029000500d20007842001d440c1e000400000300424199686401042d1082c44203d2404030310843c084040c4800403507403941e2920060038001040003038031912800c040306034040c509004e19919a4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 734320161 1250 734318911 734318989
    0x70f0902042601060b120f060609131109061c1d0c0103090f02041103070810030f0809011710050f030105010f05120f03030a0207050c01090f05040914061302 69
    0x5108040c80c4a000b10098480070b40007440030f01180c51155494908088104108010031303030340d07100744a80721004518142024001c54076032500c01341c580031010140507060b000902683c148450a00d03400e201d180240d5681e040100803c250101a0b220302e41d5240d03120004440c030110740c4042010702040040321621022540440c500b6007400c0000d814002c1d82401c010007000c41d0802548140380c110619240c0a20b24003560050005130340d00d10095036080081c44c0c5d500003a01000d0302c0b50050320300c02c0c030002d0141801403041f03a406240c0b41a50b0707528140d009201d0360054410f50000c043c003400a000c1e070b0070241c90080c0e24944c100d00038401035140c00707184c2c500d0000c140039043c012148208485003c00040018000a01a050859580b4680000420000d402805d022a41350182d0070911920758800c811001c10758030b890b425105010301d00010000103090402c8101c88074144d25000e081c012070207201c0304c0e11030000c25044403400d10791481000842514a000702c07404130400f03105011036503485144 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 734321411 1250 734320161 734320199
    0x60906042a050a0801060612140408160605091b0d0c14061e040f080c03070e070c0c08070f1a09060d0b21060604090803240604030302070f090204 64
    0x5881058a00003090000164050b00016007160b0034800000b40a14154030034400c8856590303c10f0702032801c444464040c0d80e00700c02e4018400400501203000305000c000100070305180713503c24010034049540d4403c1130f200c1c125819103458106003101d98120902e00d4602680b6807040f0360282c00a007590b41c03000b0681c8998025100c00181c10b03000302d02c07542c03506412a025510321000c0a4401c01600c0e042001a500c44c2c0901c3c5040d9080d9413002400c0c4500284941c001200100a000c5940c241000300d121401c0007400c07c8100001182d0420200340020362540150113890042c16000341060b20120480c0300303e03401003100c50f8480d072403003c0c03e1194000b42c0b5410300b4216101592902c0d11803840c405000d01405c400e030320807d604c0d844180c03518255000300e0440c841740e06480e4560703500401c10088482c0c0040203001c14208000241c6c2240b171102056100e07554200310745000c1517191000c82c5054202d03400440142c1d004507014003a54020040a10084c183c0d64025880c060038601130a0800030a82c035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 734322661 1250 734321411 734321453
    0x30b01120b01140d0507020c04020f16020f040c0306030516050306012c0a050a0b03030f0403060914120c0114070512071223011d0610050909070c0506090604 69
    0x108000583c03040c000e90312001518620b0548038080710950400420040d00c03200090300c60b0480202481c03c043c02502d61602040c603c003420411030084589815800d0b950890740218805400000c40e030300c520902da4502c00075940000c0480c20740c580103160010406c141c6c2002501480308220b0303940c00040207419075000d104100480381d0325240e5212504070707048040090540040400480145d194001403080800c10403c0c003900b11960141500c0b440f40b111003101c01801007006001084a80d00b0001c006c0748240c020020074202c04406a05201c070031428070b40340403c0020003480303031030302400307903840209600c8010f036150304050030040d11601c14039a64580c40c8401c0c0317001400c0c0500801c200301c1e4a010400c02070100c111301d03501e000700c1c4c0034807050043c0030302448400104d4004903211001480e0062840c3c4811262204c20401410094941031003042148c00c01c4002c0040c2c450300c0503036020750900c3d111040c1c5900c3c240750507801d000008000041c103502003810400455440c0441030f0508091038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 734323911 1250 734322661 734322671
    0x3120a021b0f0307180b0301060603141b0301061d03030c15180a12050903071806061d04150b07031e050909070f1b290408090f060d0e0715030b0112 65
    0x9415013000e0b1046c440801d40c0b552810b100025070036019000301002601d000141200c65640029141803000165181444038206000602656004841004540b1050400d0121188040000a07c0c6074801e9401c0c00c485c0d000846a070b1300442c1100f0115400040784101c40c51f804188802031a0b4409a0201c05401c5088100050360014021f00407268901805401d850008e902c5041c102d0412060b010220512442c0901c005441d40c8a90003419001d41e0354010400d207a05400104400303007136040c200144140d002c1100042801d0908010b020b054401c2e1035541d14014001ca00d100c003083c20355002c4041c01020000360701c0381c0e681c04080a41c44581c80c1000c841c1440e0624044405103c1c40205a4111720703042d8600c3c3c14401203900d038419a80c040e80c0562000c0034000000c02a40b00c041e900208242014402e8900d145883d00c00001403402c080c18403420243c94225020540b146114200e20390741218500b84803c02150f03508d64207841841c1024000c240030900000d2201c6c01d0411901d001c69030318 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 734325161 1250 734323911 734323949
    0x302030a09020603070207030213060e010521031306030c0512060108091903050d15030206030112241a011407111c0503031f0f1403120a021b0f0307 65
    0x141d0040035015005080c0603142e241014019607103038121b000c04ea21980c4442005009008240201c005592060310168280e0b442e10090000b81c1c464500c03440044c40c100c08184400c00c2003000034148494031018800010f91401102404883c0018211000c02c00c04101c80c408401c41207296a0700120300f841d000c40241d8074420042c0c1481c0010b0701115400d100f05100340241503108010302070b04202017104004038104060900820401440300075007180040c03004110080e00c400d81b021034540a546442030902c02c00003ca1081d6000c1d078180800e2681e83e804030a94542c1000d04118a80402c0c204014290700d41e03035803a910f13409031003401000c0c44012250301c013954803141114159080208280c0e0901400d45c0380860b01d82e0001c50305007070720040e2105000c05a0401120b8482100d50b02515050140d00f00f400c228002800381c035280790180f288420080040320f89400404480015501070021881c86100c1e01c0e003011003203600d442c8540d900014000690342c000c02c03640d040325582e4050120900f04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 734326411 1250 734325161 734325181
    0x250c050414010b0c0a05030d060e0a05060a050d21050c0129060d060f060302041802280c02030a150b03010b06040b07020102150f06010f08150f0102030f0d0e0d021903030203 76
    0x2c2d005c4020514000807840d02c540c91940e070082429a4111f441401d0701d565000c1c000400c0314003c499582d40440c5d403120811460904d8100c0300703140e0340101030007230300308900354414030103103501d620a20001440083d60250448080c400d01b9034a100c641c180b6000415107030034000d0400f06030a611441800001140080c100850380104018a500010a45941d9a448028000f500103110703c2810440008580701000c0310383c402c442215000d0106101c116402003038854030300d64000e42c2c60b000d001c0e16146003000f5a808020303079107a081c402c6110362052590381c1410302c00c1e41c184500c0d071800390707042881c1030b11181c1d1400c0681d0181e079840c0e0781c140c1d180c040600041741350944d8014442c00710310306882403007801402110300078410002a00c49503407190795400111208142110195102405003480120501e07240c480700c1c0030b0900510450303003002d0555403e41c005070b200d101700e0304c03049541c0e03d40003012a038144407181c1141000c1c00a800e034a001441d10f030728440c5040100904140e40000041c407102c40e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 734327661 1250 734326411 734326423
    0xf06120e0d08060a030c0801050103050115180510030f05061f052d121605010e0117040303020c0318030706050901051b0a061e0f020c0a0b0c250c050414010b0c 70
    0x82c100b41414103642d03591f51a1030003000b003804203484a5003000501081e80c5c00028580048502c40700d0881490705400e60010f00514003d403c00c1c54040340c025001001c41c0d0b0300c4601c1da0b482e5001c1c6018007820300b00240d2019003e0f012412030b03200002194400c00450744d0328083c4205090150042125080e0381c0c0b83c030700b1654050041e8081c2d00c10602040c0751603c080001d1600103441c0c0d290000644103803110010351b05003102051607800688042c070030944000401a005800a210f420b02505022900300501d0a6421040342031452940000550000740740804c1103034002c1c403150410510703103128080020054868410412810282d800d410300014004000c0812016005003041121115021440b904240f8543d840384426003081f0849011034054401c0b6a40500b400c4002c0a9522041c1e41c0c0303201035040100280c5d48041c0500001301c03d1000d00c3d0041c015003000802e001c600c0f0503103190503034114106070070003401140b50141906021516807402c84c103407070044000d9515610241034062400d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 734328911 1250 734327661 734327663
    0x501020d0c021216060305010e13080c010b060409091118040305071103100608150903220e100815070801121b0b04050310090804052202040f06120e0d08060a03 70
    0x489076401e001c030130000e4100c0d450207840f120303501401966130341d40750001714507420380310019190b5071b2030041400184164018803220100a0010500700c2503400044e549030055401070240ca921084a0340410401c1d0416006a8404030b0345e120350322502c8840b0490040c0001c2008050200001c1c00b0020b104410740d8504289400500310388401e031000301d02202501562013409502e04c10b031f40755144401c06488400d442800e414008605007003040403c503181c0c170202c280002da00346080d0303030119541c1d045d5144144503480024242c3e060350720b07140c4414a4660000208504001060b080c04041da9205529504646924034980c108000d0ba003400440c01e50400580c841140c054940056240d014138080d00c101c8a0071001d03501c0c214180c110120a940804a006080c80000c210512a038900720000301401c1d800c424100141c035034038402400890b4456000190440c031070703050030001c8607400305d0021000c07000b0780002c0c806011350506290340c840040041d101404520030018116403140002c0100039 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 734330161 1250 734328911 734328913
    0x80616140d02072001030b0d02010f030209060d09050f070e0402040f0605040203160905010504180507050705100f1505100309110604090b03060915070e03070b0f0d14010501020d0c0212 81
    0x50809141100c0c91802c4242c4802041d812a041340d0000d601034803d1038402807010b010f07040040d03020303401100c1c3d031541154804149030342800001055100c00010380702e0740c148404005050300a40c280185440448000c0707034107503030101105000745480000722580003581034802054035804200a0000b810030340d008070760030a01c04000c02a100803a08403c10b0ba01145440710415662175000440d010310440c02a64900346903a45241060720482c3e21507036100003180f510a0821840d9034036141004000042d501070b407500d46401d011000038130701c0b40c41400000111000000da141c50082525000c0383c100d01300a040d500c503415000e0001c0301c80c203032300c03040c8008042d03e80e12034603504018000c0031001000c5002c0d1248400140c0c03507110020b44001c0109401001e60401d030343d61603089950a01c100d0b0480c1d0503010b403c0303000400c03601c06001f4100070012210b0154541c2811a0394000700c0d440c1d0b8082c50191018400104a82e980102c0d602c00b0011442c039203040100480d00215030009250103110050f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 734331411 1250 734330161 734330167
    0x121505011e1e0c1b14060d11130e160c080a020114012603030c071e02040603060c020607020a0b060f060c3721022b09080616140d02 58
    0x146640400101c03883c0c1d10500c00e1041481640742110104c0c000c600803c0000f9402c884403440901d8000083c045020601c00081090004e80c061403c01d80c02c4039010081c04103c00740140303c2507402c820f1032980441c3d60020840c5c04c1b071084100800a441c8018080e0a409001500c40300b054402c0d006800491320031a40210b071565200303944611442504801e19081e000030910710000200072040f64050000115a41d0400c80c031610740c810348000c11948403080d110b2036060580140c80300c0c051000110f0049000040000803000040d090401c024110030843d001040403100054610034800c1e00300d54150b034514014020003004c52039508c65640760500034815a14804c920b0010510250102d400000e81e822840ca000d4030003103907221401d44000c0000c0306207120607654030741c00c003001640c4000c50710455001c03000c261007048071007681000c4042c0c4028459218121160001540001040781000502c1c407850318255810614030b1204d504410442203460500103100040140e40400c0207892045503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 734332661 1250 734331411 734331467
    0xf020d031e050901030c0203041202040c05270a050102060601080403050f07020a080c0f0d0c121e03020606030706020a0510150e01060806130209030615040615121505011e 75
    0x50b41e048040c0311030000782042d8814000d01c0c408004d40c1d00f141c0d0401e44130300c0c881401d41e0030000585100b10710302c010080c05000383e040749812010503200e120b001400c4003c00e800ca0009105482c0030a4104605560101040c003520340d078803800541d44070343c062030301540724001c0317170881c030b0a03449503000195011b401200e011907001008203003550400000c460007030003054500305000c8410107608024050b242d46078002c0116280b0741c10f95494107446800700b500c080302071103030700c8007172019541c0142d005903c81403c00c61141001c0055130007810003400184002101031b980e1903a00c60b9000c40d000c0006454103a030445504580000c00041c1100283d05091036031541d000608501045031900e00c210a525494a00315589200b105c2104401a014060555840c8020305481203400000340d089a61071000088860450704886810200b0703694150070305540142c031005842c003080000721001c014960401160b0382103100c2024803035441030110804c2400c2c4006840f1060038110180a03c0202e407000c2d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 734333911 1250 734332661 734332667
    0x509011d121e0a020607030e0319050102070c170c04090809030105160206060604060503161e030b01020f03160b0a061a19020106210f020d030c02010801080a0f020d031e 74
    0x4203507002c80600800b600b20702410b00c640e140b11004010350070035401c10860011030300c03440301d500c43c0d2600581129003162030140400340301508000b041e100d6940c04160345e4100b255500031074008004110641520b400e0034011252210509607106100d16903810082c01049443c0b41520802c68000b0020006480c000c0360001048109910041c014040e41c0c0004540389014000d581c1a9000c5070754041c290781c1d1f2940c05140e20101d0f1542c0710140300c162609958400701c5016000086a031aa0300480d00307c296400181c031780194149011615002030090303601c1d5891907581201800c0d0011503030151525107402c50700003065140c1041e03600802c0c8140000e1110540001441040600d01a8141d81074440c0300807400c0714040c0c0070701c0801c0700d050744203250010610300e00014841d0040c0c408000581c40d030303800a05c02200700101180890100602c1d4030941d030300440001e00420342900075100c50201aa01d5540340c014601000b41305000940c0c0c0380007814851b01070810718803142c6004100c02000000c0c06 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 734335161 1250 734333911 734333923
    0x12030405030d09120305220303020c0a14090408090d08071b0608070f08060307050303041d0c0c15040c05041802190602030d0924151202010509011d12 66
    0x150103031003030032400c1d9030542c0703d1203001d0219000c1c01c04e180303800f010540d002c451903800008420581c2c0300c189903620b090000395400c03074000c521903001403c041521b9024400d49003841d5005d04c28000520418248540f100608254003070761202c41c85035034504c14000146043e01c909009002c1d5000403d08404110455024250450043d028020010740e40ea8044440580844160002500d0001c00d488a140201d0714241c000c070008098481c03558880001c00c0c0346030008c1d4000d4141860f45202415001307280310700190411030541c03030240b614880b004180e9a0b0340000c0004038000074108001003d00043c411030002402009000b442181c07140350200c00c0c4c02d12000c0c402da1040d10583d42500c068502e00528100f10340c000d401450803d1010907640e4014140e114040e0340120380d820401100385800b03414030345e805030000c0b00001c3c03110038440100345841c0c2c6a000070a1014035043d200b000360b80c00c03000781c42c81101c0919200c110528880400c80c50260f00c24a626005410100c20000341c800103d45 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 734336411 1250 734335161 734335169
    0x4140f0118051e0907091a09010b040f0b07110a081b03030901090302150d0c020a141902040504020a170a0b1e071d210c04141302030705120304 63
    0x3000200c1080490455400341d42a4800c26120004200c00300c003c140466807200c3c0c4078065460490351041510140c900b03510a100c822407094070428418a003544420b405081d103080504d04040c00d25003213840c3c41c8114060101c00b5080402c5100c02c1114400302d00d400700e0805132282c0986076440d070441d5950340c0e030150400070300e5100400151941c14000b064440d5203005a69401c1180d00d5602408408207070070455040c0d5145c2000034400600003800b40c2c01089070160300038400100d40e810200c0442180c42c031141a19081a01e84210301c840346022040d4141d01118001115142c40c400601007010390b51120f000c4031080222602c01110103d0b0101c0c5003805850f800c0e40e40e5a4180000c2c1c680b61b0303404110341d00d20009602090403d8410044203002d175006028408070a04c680000528884401c08000381d0714075180d04520010b44148140e100d02c88040d20b09001c2c0160051801c2958036006142d41c5445044cac080000c11743d901046490010301d40581610600318100c403c1c03a032070343d2060003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 734337661 1250 734336411 734336429
    0x90f060209040c170613020c010c020609120a0e09060301090b0405011d0106030c17070f1e0e281118040c02060c0f03070e120a03021e03160204140f01 66
    0x600c2c0040f03d005845460340e404c80089156990b9841c54104600402800802c00b10740c0e45c03d100d40b45401d10b091061500114242d0010021480c08030281450000c0b000300d022403101d81400492035854100104a07810b142c11107a140715941e415001ca0300405408078050301100b03140c4d09200600c1419030207d00c0b40050103a655000181250003142070740d000d0702c0018512400d100d800c03c010110b0b8141566880d0300742d0152134210313644179001d44c41f42817540c02c00b03c40101a00316003c2541840040d0744003d000d5145524400d161201c2e04840d0185403a0503042c40142c55001c075510300641d507211003800801d41c00c18545921329038540094454140c0d04c0c05001d140707012840702502c0d00008801307105805c0c40354014509542c81e01d07115101d400c0034250030213011050148440941e1010318408a0121440040c40301031708604009240480c1104c0180b50b0409000c42c0c170f42801e40101c11030f4804c4018140402c0780d00c11a101042c020641412044c1d140794507402481018801254424100c8410304 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 734338911 1250 734337661 734337671
    0x15060806120a0b1005130204080d110a020907091d10050a05030601140a0504050f100510050d0e0705040213060207080309010e090601090306110a08010e060a18090f06020904 76
    0x140c00d00c452000c040085403210b42c81050310b030001075415180d81d9441842c0d4180224440c0d51a0003180002c0700c0349100f000055000b280030b0013003110402c0082ca482c6041d28001121000b0740101315150361100002038080e40e840d40004817800d0149894030001c0c00542030392445c1a81c0a034807518850030036145035241650952000401d03103032124144003591001000b40145900c0c00300043c000d0001092880d8210035604e80000d82651280329062045504050f0440320b413528500d008000304e090307007025210b550542c0c0810742080e4014151415010301032030015901d00010056460404c0d2544003d0b80503000092800300782d0506130303400085407201d4085030b50841c1c50f0420700f5102d01403020080d0029960005520b200e10b05a079820390080b806052a00c6a19181c3d201c10054884801040700305960004020b0b03010369004040500420b44c0d81d080280314105500040c0d0075a00a10441d990056214021000201681d0103000090342c4007440302144030240c90180c019401402c01284650300e84 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 734340161 1250 734338911 734338921
    0xa020a05030f07060c141f0b090c04170109050105040c1811180112050705130f0e040605090f0601080601060e03010b0a090f18050109050c062812150608 67
    0xd082c0c01c405000901500a103414680c0880c2c1903001e100f42a103045142d1140c140002d1424055900c04020520a5840c01c5454048a20994200420f402c3c06240807104001004604105840c1502d424241c0300d440501e500501078050020400081c0c615413805040c40100312400c81e01100300d502103000041c1c0d03a228400c0b260201c4251500c10703200b400b010440d91841440b050351201d441c100505042241030840039000d412280121140e5010070400030350b1b10400c9038102d068000610b103800c00020180d0401138030305520301003d440104925101e2001c82c0354000d0500044003101c4484085541d9903035100a500c0d40c8890030310412020400007a581c400350305040c082c1412100020346143c41680c90310070618002c0503284120f0021550b035840300b10080c05610071319076595005e507001017500e00f05400c060b81000c600140ca10700c584010000014003003045002130420480e03050760a0344c42d480c150801c0d55200d0700c00542d40303c07040c545040c031517150065828070001d6a0565507020804e83d29 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 734341411 1250 734340161 734340163
    0x18060a090b0c12060603100e09010902120a02010504050402070602091224150909030c0a05010603020a0f0e041e0b0712050c030c070b0606190801140a140103090314030106020a020a0503 81
    0x340b5860104900ca04400140c41d031708003c801144c0090304000c044040760b54801154410f01801d9400500c665191031001056180452502d41e40c1d0341a08060700f02c10060f41d0021301039101d184074032405103802050a4050000c43d50681e0280900900b11592044050202130348070b85000d0f41d580da0581c280301c80c08241100003c90b40d4844c2c6010200c0d40300c0c4400c3c51040204400b001071510042e0b1100304803050074013906010110040e40b00d17400219840307041d0b20411140c01d5070703038200c200388014400c000c005075245400c0b43d0b074001d5000a590391001c8055401d09044024040300a00000d000809000200754805012826440311810401003500c820f03400550500c419034694400420034041003000c10000c010660b0045001000c0b1481e00d9014070306510343d010580c00c21008a0301880040006c81d2458143e0461880101c80b2170711083d040c0355013601030b000710100c074504041d540c038108000c06000d86001d0001b0703d03400090645130341c3d48090003075444510b40070823070040044500026503420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 734342661 1250 734341411 734341417
    0xe0d02030a0813062a2004060b27030a080c0c0405070e190303140c011401060305010617060102070b0d02220f14060316050d09060b0103050718050918060a090b0c 71
    0x2005da104035451415850300c50392a0303040303600f03512122a9086811190ba5841c03061030010655501403e4452440c160030030205e4403041d02106007920301001c1040c0b1070350b0204a64ad07507a03600c6180981c48244900e01c003840d0845820a4542052038942070083c0d140d0484d145801601b01101da03d00500c0c04226650b0711150b00b0704c0700402240b03a90840380100204500906003a00300c0100004550759407404c1d6a41300718080c1c0c4040d0103c2d45d079000502c800ea074483c000000071718400000c035006040580000b990740741c6c0c0d8400c0950701d000200782c00114161540480d080381b000304100048030140010310248140052266100010f800318001400d424007149144440d0310062019040d43d80d0606807054000e001190442000020807401d5980042d912a5901e541e0185c040054521065030025007100e80240514080c000101c03040c1044c40340e44103400050714000d0b0f84100b40f0341c840303426850344140300c000c8a640d680181420040c2c040c034954020180d290142012503e44d888540b0341d00040c4c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 734343911 1250 734342661 734342717
    0x30b0c1b19080309100219080601023912011a030c1c0203010b06030c040618051f1b061a091603051e040b18010203070e0d02030a081306 60
    0x741d10041400410b42c9400907541c041c00745415078005003072107003500081f81e00c130a03030700100d542401100c0350100368002c15250341f0842c2070004009140302090100c9001c58441d640344111944070043e10b0507840101480808848007620130303401c0d0740240c05034030701910084015000358541e259000d40540340003c1c42c0c08401c0c0003e01a03245c00010545014040c0d108980260781640d01d81d01190441d0304e500c401544180540620640c17102c1c01c24000800450820240405166200d42c0071b002c9559040303180c41d42c8501c1c00808000300300c0c24213410740d00d1009400c4403d8120310030002107000d0060681210404480c40403d400d41a2008420068030040a45a1a840318200c1e034100d00300c20b0082c0e00c07464000ca240451258061480e00300c1c105a0042181c04130f5060050100740310b80715000901590003401c1c480f00139421071500c80380041c19903200d030100c42e2040c0001172100c4155201031214100c00e5402c910719507550044449189041d110340e01c00e04002501c1614034960203042070340003034220 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 734345161 1250 734343911 734343943
    0xf0b042a020303130f050c0a06180b180d0221030a090906080c060a0504030b041103010f09050c0114090603160801090b060708070201180f090b0d0c1707030b0c1b 71
    0x140134261606001d448040d2000c6440c1c0c481c01a04030100e030350345046100201025580c1c446c100f50701030b18846030411140c2c892000c404040c00901e01e02d02480c04e100c180541c1c10b60b041c240c10042400021480c1c0c0562000021802d9190080200c0d030708044001e001c00381e2640c5a0a11441d1744400000c21120240715109440d041641c09040b1840c01d00014a01013400b8900f030341c1010344a03191219002e50076281154841002140c0746418202805854842c90304081d0030041c80886888081d180c10003520310504004082d9000481c4410b00800c0d100307000c40181550381c89103003496103201c0c51516a10210085290100001000c40040c007a248003040050041804e00d8a280e40d00441a000050100e05014088040c0c41061058401c0d220040c4001244080d0380e505d0118030b081181e00307202c152801b550020241c90f010416594400044400c07554194010f04204800a07042040a800061510168800348001c04079401e01a01e100f01c464002c1c082d0b84400b064406640f4002a6100502 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 734346411 1250 734345161 734345191
    0x406080a080427021c06090507080a020f2803180302121303060c08100902040506030f0718140913030f0e03100603031d04140a0f0b042a020303 63
    0x5250040c8600c0c8200f2080724600d10070710b41d0310b1008040e81c0050b240c89120300e00c00052885440c099029040040c84800c0c13040005040c500d00092417401c0040c11f0305e0b07282c1d4000640c1d46001061408854220b43d03240743c522410b0782413486114a0b00d403030b0b0740e0740302c0083d0400f452510700443d00d80a040e031040d0704d50028807031055400c0390500e040d001031500b0011198000d0700040460254010400b91003016901c44080e840c10001e040d0901c0b046401c400502841444140300c65181e140803243c002d030080039a40c00503a41c0081c11a90035008100109115080c003800203020911f0414405005500702c541c195140c2d42c2e2412051500c070b510b00b011b0009000500c014441c103005207495507100780040e0a56101d40000f000480c161840c0342c2c0218006120800c01c0e8006036983c41c490010664201c40074440601c0c50700d224480d150014005000c00c582d1074150b4814064664089480f0b210701420a22410403411416086c2201540d144065441241c1145110900c0071045030302c141d60700d00300317001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 734347661 1250 734346411 734346419
    0x90111030c12040317040302031908100924030c0801060b1201030615080d02071a0a050a0f050705120706053610110301050102070e040c03060905010b1e0406080a0804 73
    0x501140b02820581c1441070400720b46151240004c4100d06c03440c0241c00441e5030380b6401d07510403d03054600b2000410840d44c84140080b415417401400101c03030100c81c3c041742202502c000ea42018505020200c0414a4403500000b04402140051f00301d90841000700700d440d40d500d50b040c0030740c4105c3c3c0012078540103450043c40040c9482d44120790a0070303012442c440c1e030703922400d13440e2a01c000001c1e07003005030380182c10030042007181f4540030020841d280c10f1a400d050413508040c1c4180226404507051001403420340461610450941d14002d0300003044030300d0025041103000300c5070312003d020f0b40d04e103090000207080003044030041791000507828015040641540f00c9404000340000280165004044075500c0c2c0312490300a100e503481605a12507542c0d4540307000079140c00741650041c8d4405030010100703c0410000300344801240c1e00050b0124596031140340581c014885800151761228a03510041c2074014841040851001b00303032030030041c05132910601c564460120500900c1c0c0141048180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 734348911 1250 734347661 734347687
    0x5030a0509030d0f06050a08160323030d0f14040f110414090601060f0c030210150e16140403080711030106050913020a0e01080a0314091305090111030c 67
    0x607400700c0810103403410580315070b04500544480c03441e050103264490400340210324210015000a0000d080106840c140744040414040b4040c8806001c030180b01c0c51403039140889030000400c1c00c542d54140ca40d11541829984024071a100e08540c805117015240b01d00c40c0640e030207050043c0c0d04104407646450a60342c072a04c40381d80441c1c18035049900c03803407600505200c401c0280e001d40c040d100a442550304101d401400060720b00d0984040103405406000407980202c1c00f6801d00301d00a501040481d410300d10399812408940c08099084040700030806450301c412a068580d81c2c042d80c5070708070750785105e400503018002d82c00090150f40c0c04201090014000400c44400c00c1c1025001080701c0b40d54000042e801d8408603018607104c120022207000f107280c002140c0001c6d0400550311a02941014070042c0d480380d50441c02002d02810459582e120a0300c00c050311220720300200081c0f00c01042896010140c0307016500107a00b9070030a1034100c4019524420b891144c0108501c00c0d04020700c0020780303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 734350161 1250 734348911 734348921
    0x80c0d0201020c06120609060d021c0c0f1e0f0b2b05090622030935030702040e0d140f12070512060f0306010621090302070e010e04020105030a 63
    0x301e040d481002c486801d0b507100d03400505500c1c0c0f103400c2c68107901d15062060040c032242c0100740758400e02c00341d5202001a90b40c0e0461602a4003940707903014800005141c0008074000350303000300d90240079480b000590031010310302c0c005400c0c0c481803801840c181d0321044c0442141060041c005101024042c00760516148212085070408003a104507001d08a517180301d00f2034400b41d89894203034002c1c4040144218400945490074145540305501181254a0040c204805801100e803800c071400001c00c003c842aa869900542000000310415860442c03100e6403a03002c040c0403402a4142102c81c40b5603140031882d030182e8003980d159219101c006104030302c01a03000804145094905009040500707000703165461040303650380c40743c0c0d96421030013080b01900303c030003030100380301d500560383c1c1c0702e110380740402d400e0304481c0300d404d1a0038400b01040c030140c0c40b0704521070b4120340d041c81c0200980905a00055000c12205141500e01342030b45c0701d03071203034005030000c90b4046d0200310108086408404031340d100d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 734351411 1250 734350161 734350163
    0xf060703020f0910091e0b030103020103050406231501080c0a08040201090f03050a03080a0209030709050a090227090d1d06070b1f0527060a05030304030605090610080c0d 75
    0x822032410f151400041d800c00d5442c0c600000250f02244140b141e51307a81850007001ca40840c80d1180002e2620304411f02d140310500000741010340300c1c004201080107540000701c241d0484000d10030b4031503500c900040380c100112000002ea42000041c200c1300d5025000450207480154080c2e85450500e650035944608050001c9041112880b0700184101d40110203c0146101d10090000440f89080040c0b1105028041c0e103099881081025280d036000103840d4200c07094101c011401d0382d0780c10041c1d001001e084101a400c404804188118084404202451400011603001498580e011001e9a03030969110040218000d01c02d4101c00e089803501c0107801d59802000d0300e1800308039544040080006031801201490140f0200711540c048403600350181a0035035a03030f164980418681404140865000144900c11f5404643d080c0c4998582c1c0740a03210260880c0e580320360b40e207041401403004480d011110301075000421701420030340c0d80c04011074002e400184140b281640c03c0082010034800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 734352517 1106 734351411 734351437
    0x190506060f0109080d0c140708010b130507020622081801030e01290a09060e220201050909180105090a0b0c0f0712090b2a0f06070302 59
    0x6030071700c1120301ca458070381556071450a180315080c02c5108180c1842c06081c40c081412101500128a1014140c3d4000b001f00805800c400490340185c90f0000180c0105010820600d483e42c0c1d003803450352045c07040078800070240e5101c044c80c0c0d2040e00000182401540c400d15150703014424100200034910003407100c59800c2c481100342202c601c1c01c0e03008110309c03101070800648904060f000501a0203008000c0e0584920500c00500002c070346601503401c1c89c1101c070354501c03500600d102c41c2c5076060316458180704030001044071180b001000b64107840000c0c604442002024090a4025a6200302600042c0120300301800549402002840c4010081210290f9104c1000803a40520782040d0102d00649102c203044800d409030741d00c03c1d0880c2c0c0010521100c1c11201100200081c004504014208004121090744541e0290803000c00303070300004002010180660028000084e02072 = true := by decide +kernel

theorem cover : BRFrame.Cov 734172661 734352517 := by
  have h0 := BRFrame.cov_init 734172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 734172661 ≤ n) (h2 : n < 734352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
