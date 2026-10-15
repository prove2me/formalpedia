-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4156
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:44:04.16678+00:00
-- url     : https://prove2.me/submissions/b58444ac-31a3-486a-bda6-d3e4d9b7772e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 747302158 ≤ n < 747482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 747303408 1250 747302158 747302161
    0x160f0606031b0501140a210608120c030304030e121f052401030e010e03031801060510050f070611070f0b0105010c020312090d170a020106090e031801030b040e01060515030f 76
    0x2901100c00400c08401c150520310031f101d4040d4000100d0700b49215007506840d0341d441701401000000c1007030300200c03200300100d64541302e10740b4803098590001a00003000c1c000c5521351185a55034025030440341d60292000c58801c42509901040070322210300c5560034a61a14010500c80081c11481c0ca0740a0311840440c801c038645c0c01c0044008101001c4040025582d411000d010034000f800198001d80416050004504242c02c000f821519243e00440c850014905100c400542003400d48440e1400f09000c2e80c1c8544481c100900070f465002d101c803040b43c5000a181c07080010b0056142c025502074250341d010750b84c84100560b114490540042d501d640980200402c1c02d2a10004091030708000c0d103a150350400d150380c0c2809203076015283c03002a02c4041403510382c443d030912400f001404462010320028103010441c50712440760022260425010709800140f03070b4000e070804880118090030801808021380c40050080183e800346d24400e0300f8020075240c0b03210802043d20302604980c2c1007460b45 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 747304658 1250 747303408 747303437
    0x43c0e060d021306080a02040515011b030201090606030305130b03091f090c080f06070e1804110603011e0503010c081311060a0503090d09030302030f160f0606031b0501 74
    0x402603807504aa102d10300080c083c020101c04d001d10001840c1e42001801048600e10400041e10f80040a6a00f40a00800c0343e000b81da0b442403100c8080130750010f110074008410f040407805001c0c00d000250540c0d061680000416a00400800c00e61142d2101c0148403034541d9040000e503c41a18440c40d99441230054030030110040341c0c484401c0812000010340e841c426510f900c40c4040360b03440080e007908094104e101603030f400c4c021158007140e1890112a0510202c00103115011100324004201d181c101c0080c04011410008059405009205d95225a9601200140c0080d2540d0b41c0f40c3e040440c450004041c20f050081c00d00a503080d0704c80800e00d6a8003000c039005114480c4064407000c410030654505030b01d500006041048041d07458954924010003910b1808246020740010003001c0141000440e40c084142e0701603441a0424a9032500700804180b1003401e41000940310001141c150300401005900040450740304000d00c081c0092808a24114042544a064041110052840030303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 747305908 1250 747304658 747304669
    0x3060f0504080a030b0a080106080307030206012106020c0c0904080406090515040e0c1605010f110c070306150504060b0c0c0a080d0302070204290102060105030102040b1806043c0e06 80
    0x400000641b041d2590b030303541c1442a094a102c0e0b44404144c0e0000261035051586c1031180a02415007050034000600c0b03101c00080d214099100f000d02031135408200070315030b41018800701641c0d00d40240241c80328186030900c01e0040d030052003100e000c140c10050016190500f81c400722000440003180508241c42c00c40c03981440c48000701065559201004203040140c0301e00007a4041c03a0080000145008224688008492104002d444000001c0c0590043d01c1000515074054a41c007000104017000060043c0c1d43c503007441e1700007580c0203007403840c0895140e01a10107000c13500c018400700c83c10045407030140968208240610310240d000101c505034031078060340051035032070300c0a04006080014008142211181010040c0104403198101030040d070b0304200711405003001b00c3c001c502e8549841c014400501c1288000240c213005240e0210440c3e8401c420303a030043c0800c400800c42c03030030030303101c001c8011000d8540c84009500c0a184040d4100d10038681d03d0079035404402010309034072003204226 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 747307158 1250 747305908 747305921
    0x9271104020403020d260708031306110d0e100b0303040e100b07080c0d0302031005090c280305160801260304060908190b011e0b03070903060f0504080a03 68
    0x360403580810001005840304c00e80e1401450040440f912420202d2440b0380483c204005400d010660600880c0081aa40412280c11200d4400c86080040b024034021001d480c408421540c80040840c000b50140c2154004d018005030741d10950343c1c44a4060150000c85160b8000590154000d00040c0003010100c09510341001c0c1c200b580c4801540d0781c41d01801180e1000c04229401e00c8081013280d0001020440c1003203519050500354154546810080c0503040c00c4d1040d980300340c40315408110104012011109c0728090781c004008a00c0240d02c00a180003014000e000c002850400012240142c1400080201006650381c141c40d034038144000382a03809420351204840c0c60b030303444a00144c0080000300020429900e0b012103e0340351108080c01d10050a140300012180000e04500050034131000a041d2940c03081d005811884041800c2c1840669800210008400005000754a60030502c1581180e20510080c8000100110343d2021b83d0016100200310350300502031900d51500075000301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 747308408 1250 747307158 747307193
    0x1060303020601060f120606090608070201050c0d11070807060e120301050307090c02030c010e06011818020603090a14160611070e130203190c0e010312030f0906150927 74
    0x3e1002c0030390551b0303441201c00683c841c0340032442c4030400700200c0c4c0d080a91941d0216003800200f2441c60041481c1c402c0f4403900c80038140301030382c43ca000784d1040c92207000d803624981c11880b40ca403900c8051a10070000c1c8298144d10304a841000740b180248066002184d06035540a0003504500b07180001c0c8801404012950380254001400603422982092040002030342a60000340500e515068000c0b64030324400c095440d0060419001d19000962070a481d541160706440b0a9565550340300c4140c1043c010450060204101c0c407000c0c0120440010784a01c408610840c1c0401c07259990308c00c0d07601d80050a400c030690b41000700d04100c011741650016501150300000d40301159280e0f40000e0400412040f0b04210361300496003201407216400702000a0180f42c2428600382d41036407241c52014082c80604010140c440c8698280301c0c0c0103400c8180010b0340581d00b8420421207403410680050745020301d02d016442c1080c80d44400cac0944c42d01886011111005013010040c0b41c85100e00c1001c01c0c82e12 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 747309658 1250 747308408 747308417
    0x100f0506121c0915120501060f090515040e04060b010201140f06010809030d0e01051803210a09060e0a02090a18110604080f1b010c02090105090402030a06060909060b0301060303020601060f 83
    0x240444585800d502241d034665031740d0680f20482001500b22401a0864810021807a0440318421317002480e15051b24000c40304030032800c2030100c0b0b40750b0900c1990041d83d44240040306110402980d904103a00d41d0f14241c00900c160b142c010b1140140c00011200c180d0042014008140d640d401f13242c0c2d458029200105036072a20744281d05d0b03041903e81000b0100c0090395103408020f0f444ca1b03907504602c2e450b014070019600e044400f03421b100700e0300c552042000b00c1940c5080820300d40c0b007030f640c80030b5400e50348004d05004c0703405910307004e9481e03441d40307542640160f0285c80081c4840f000c41c450b40c03c840e0001c100400030348c4000e4803148a07038680241e40e03d400c40c40800004c2000d483c05c01005a2008000f40202321400380c04064949024001116506000035443e5403001640c404040605451054900000980c0c42c0c1c00002c2c0740c000c0c1c000025188929018001c200c007200745d041000070b20b000d9070b814040031103d00181802c880b254407000e80140c00540c0144407942c4115205900b12915180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 747310908 1250 747309658 747309677
    0x803010b07030c0501020a0f090b0a0503071209051b010f092108071b0f1d060d03030902370806040b040203070e0115030e191101050c100f0506121c 65
    0x210135003240e05c406501c2c0c0104071040802e070740310303a40b06140e0806080340d4001e130341c02d000c05401c02500c036000c054410b40500c482c40001d41b0000d40780c1d51100810a803c6022902c00a82d05800b0060607090b21250600065880101a013a54001c0e0004d03022241d002124044805925034401a41c0c0c1c1485000c84c0c0c844410040240414080152400c004214400400d640782c41e184102c200404aa808108442c2010583e810b4400c0c90454269101c841512600c540c07600e00d1508600825281d10000e5010656034545ca038203261903602d940700348040e1243c0b15100d1059248000340c46455119072002c0f6071211000400042c0700c148055007251016040b00c881c03a40740c00b419406040c1c260000c1c0c11182c48110342c60301003079050080000b400c44040c09841c02c140c0d1052010b40462a00d24050003100038031003002000e902c80d1080380c409903900c80030f032100000c0c60f13502040a07040440200c4c503004d0401010803501c0c0f4140c0000d9085002d581e0040a030320031781d29000900d0034840c42859050107454a03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 747312158 1250 747310908 747310913
    0xf151201030804080105091c0305060a0e090705010e030f0c100302070807030c12030e06040b070513061214010605072a06030e330c04080d0207060f020a0803010b07030c 74
    0x114590203144035000341a00d441c04c2640c40790071140010035104065019000c5420340c8403010310791003482a81442c000ca62a51a800429922902503216030f2102c1d822108002002d90003040c00300031f590007641d80007140313140c020416a48020849502500da0000c0c4409407507482c4c040c9101e022120141009401c01c1313200c1d1076001180c1c00c410820b6020030b035441c51003030402c1445100040401801c3c1820031240402d4091580e40d075030014401030128042d84e000c101100c0c0100103039440c008614103400070b060344402c0010300c0c3d280620302d920f848030b00703141c0c074440d585140303941c014141c450607580e044c2482000d889891801d10900d40854110440404000c200300400b00b00070042c02040c3c8000c1007042d40c4440350761400808403101c0405420a030ba00010821320551400354842d03150340101480c2c1c03203d0002c071903a0701c01d6601c618510b100700c0b180c101c181c03900400c45200325040790300c8562001445202c01e984070080c10b1001861020208014003640307501c580500f004070300038070705400d2801069 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 747313408 1250 747312158 747312187
    0x6040902030312100e16081816060816170a15030b180a020109060c080910091a0a1b050c030a060b0a06020109050613030c050709021207020c0f15 64
    0x43c20305151028a103420040f801542c584c0850050542081c4a241490101e500007180030078901c0b1182040510008180c1012451a8074042c1d0710800c8142c2d481e05040000e08000c002c1544154000700310000002030450350303200035009031003030b5988a8942c1c846481b80b8401068034001e040300c482e15510f03822144c0142a1030241d5014610581204456040402809055140440681002d5844502140c005036032114031074046035800e0800030b4091445103030001c2c490007001d401d00c0e08440341d40c0d403030f92101b98000504001c0303401a0030010181c3d020300d14149058419014508040b4000d25164026024400714114000c1d015900740e03140d0a07181d00000c3d06007865200e007650348a80b1141445a07500d0081c484c40d00400d40c60000300802c42c2c40b82d41c0c054030351400502003020b8090209520003414000c6c100403244581c0300b0280c682c1c00e070300c07106424000d4011840c0341503542025000202d105000007440405550010964501c540c20701d0300f0442915084c6421028480d001c3c440030b000311280c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 747314658 1250 747313408 747313417
    0x60406180516051e03120f1e120601080f04080901090915090608010e1e0304030210051206010309030522050418050c040203060a140301060b0a050909061f08060409020303 75
    0x4510b5811807052501d03040201052407541c0c88503801030034242a00742c9640010300c030f1602c0090340a42903214000014000d6290040d40c00090181d442c5542c81109524064010a801040e03140c01c2e4600f6241c2000450b0f41200846501b07a01100400c04a0041980750f4064150a881490701e01110790300c07a500a005c0c2c0303076802502ca186e490008001d1080465501660014020390720081040110b11102d040c3e40c0c44c00b4040c1e41d1048001c044940b1202c0000340100c82c09150050070003500c80142a10060941d4401d1748050034000d50788012850642c801c0c0280300400350182d1741c00d802c080b025180071a40d002c0c01c3c00c1c40400d11003940070010f03c98540d801455a041c194441901e88080a41400707400c0500704903595210b688100100b08480d07488600c81c105a80045500003405200304000c40d0040c06a5003000104003004a101c81d80d0f1a808002001c800e0801d4440060a86030742c0d0a01c0791002d42018115248080c0b0071001c03003814420b10403c0d5100c08002d101184401c0d858000c203086510 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 747315908 1250 747314658 747314683
    0xa06061d043c15051e04050a020604060810080706091404240f080609070303120e0a0c03151109010c020411030405060f40200111010e0604061805 64
    0x7118100c0e0024419400c0b0381c94100409204207100c0307803602c5e000c3d24140c0318840b139103602102001c0d0041400e1104c108111340125074041c184594541c0c440c80d002e07003002002c61300c82040c40068100400c0c841d0001c1007040488045440307060301e903400e0003440141c3c1030100c0150b540050f079030380c0090340040490000d440d001b4060280e00c26003604104d074a2500100030b40000540e45d100600740b02c4101c0c40042c0d550120f941515021002c0d2103400c4544020301582c40c446600ba204181c08482404603070507194044a114854450800354644070075410b807003189420150090080c03254140650003850000ca1142c402040010600a032030304110f0b80d40c209030303401d55180d4130020812000c0c1c0003101c2c801d41c1102d4160900440d00d0910705d000c456029213040001c0c80c4120030381004100c01154842e48140c15801043d04900c1d035080e80501103d40361100c800f50004070ba11110b614000018840e00d2140000da501a2189994076258807002e441809082c1045403030189100340420800c0c00403a56604 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 747317158 1250 747315908 747316013
    0x9080d1b0f030209090c071406160923090c0d0204030b1501110d0c1104020a0309050c0607320d020114010506031e090106050307080a06061d04 63
    0x405040020075149920100d00c00307052040200c0030ba00e94681d00d81e0b9522900415010f0342d224107a20b031000d602d500f59420284244555000e102c80c1c503c5508100e0780b03da4141d5142c8459659910610241c0c414001c50040560040c0710725002c0b43c14210f0206a0000b841e40d507040c60503461620b4101241d00640c8245c0b02414510244070140c1c1401c081d08080010920b015000030541180460712461402c80710310a000000d61124100a0a840b07890020007000380119224040307403001401805d03c0080480f000c2c00385009640d00d43c43c1c00d0003528041c40c0c003e603860b0319545094185600c2750300c1510f001e6602e10020391100da40e07070501f00000464446141e0010481b2580c0c5804500d4125040e044240301c1c003400d100f0012580501d655680065080485081064564440d62401081140c0041c0e405002d0824041492100050784c01d07104c0c3c2c4191000c000f007940d906a45107900d10610b0542e41c1880180001c6800b19115071900c1030303242149000e4208c8080311070201c0c1c40c25100d4011041004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 747318408 1250 747317158 747317201
    0xf040e1f0b030703080d0902210303190e0c0118030503220801061206051e09031e130317130e24010504091508100b030f030c0a030309080d 61
    0x25100c5000e40c42140d5070a0780101001429503070ba40b2064020016012145692000d1030829036840313860410251280c1c11034441c000e11080911502c039441140c02c0d101c9043d044032600350350750091080c004600c950740b015046803548a40111226103513001d0b0954900c030f1152002c000f150040c0000c0086e0903030010481402c1074030354084417045000c2e03070040d081d51740740c01d034100026101c9074003440045a0200c80050907580b00d0568482800a03030390401c1d0082490710070841d0f1000000014182c2e0072500b50024607100d242c0c5c0860509100c0d03041c801500207071110082001820031040028883e4100513101c2c10101e9440144820a071150b001c410407071000d41c01e0108428003c0c80c4c1c0d20b042c88120171040588640c0300000791a600c214402d00c2c05869480001801c0a00119071b40c5001c3e000b030b0030a07124152440c9150001408000d40001c6c424000d100b030007800240004110380650346c0c0107010703010000c0130b610190000c02e0360480650f2003000c1000065010300c00d40c45a09908105041e808816 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 747319658 1250 747318408 747318463
    0x140a0c0602190f080411060c0a050a14100e070303142812020a0e060c19080301030b01120b0106050a031e1a06040b190201090213050f0f0c090f040e 65
    0x1901210403e100b8010000280800b0400802c2e00c004103030070940308143e442c00e00c8402e0510303000c9000c601a01c1070080103002c10402606d40380e0b080c4102d10450485090800080e40081140c1c03810310030b00101c1d40000c108000082c003c00d00b910326166a8540c0506101c039544203000c102c80140361a007511241c14a0900140350040000d020881114404600b80b54034800081d11828501703a02c0f80c4100004270745400410000c000150800741c00910b4940b1070545071a0004060700b00b80030440701c0321045c1001103012034501c00074401c125000440d00e55164079000c010764860740046040c2d81059200d2a410040c212040841d42660000001c0002c031a48035110924000d0214030101d445000204010000342400c44299840410350080a141c0f0071104030080e4010b062412000f0740000e0703404c92031488806581c0c85640703e4910070100802554810400030080c05044900f404950001d2218550380d080400b050340c07603600c0280c000203203050a01c000d141307484003041081c09409030309000c1204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 747320908 1250 747319658 747319667
    0x12050312190524041e02210f0601171005100f030e0c01050702040b280311100c061a030f1b0a050a030213020904050c0a0215010501140a0c060219 64
    0x148445901c05111600d0095201a43e2003444001c1c07942c03050740c44080d8a1082c1d464445041c1c0d061022260455440d0900808100f422404132000404250640c00145804c00d01502885c80764905a442c410440e402190310401d00c0c00181c8031a8054469000200e41078440d101408407400310360b114490708a50503080142550118400702ea079a8000d00c09091859801100340c4428940c11200461005000b00200300090041003407a880030341070800d4107901c0411910f1010503280030380000c0045291040c1404611251140040000398414a020000c14096400018020020100c1c024000e4440c2e00282c601005260b0340c1400ba046151516401503000c0c420340f4458000f5100000e06626200004600501604c03010303005544801401401840301e60464101e510010410006824401c0b2500b1042c3c1000b00749001510944008019006410021904a950595440e05080008942445540c201c2c2400c0c50600024460741000100c40c0e0000d0899001c0130000000410310080c0001c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 747322158 1250 747320908 747320911
    0xa15090c0b03091c12050a06350d030b1309031b020607050a0b06030c3709020a020a020f1e040b120106032a0f0909020d06050a09061d0304120503121905 67
    0x2030a87d86440410090841180e285642003082009400c4101981e034003c1c050a50300e00441c1071140c00f03961040c04102ea0183d00807558802d041c1c3d0042d92a0450024590482e08140000707004100303031146041444804019040c0002c2c4058165400d00c011079982074907000814100b1100d0300c640c0070070001d031401c040142c0100300004507843c00045044000c40250034a945100b92100c588005220b441c0981c400107481c01021460011035850b00c90450003900c0fa90102e0040b4030a0140ca6a0041d0500d00200200702e616011804890003414080400c002040030390303000b6400600d592290040d410003842210b004500400c0c1a1001701103100c20845e0aa105421b0243c4428412000b440f82e4861201d0032170664080e4640002c4051450000a084131074007980142030508100411032600145c0e0060f0070003a01c5001c0902c200c803805c0c0709294044000000304071a82d03005020410003402c802072100022405601564a0450700c031031400c1042200f110b0030000c00380c100e407201410f40d07214814607 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 747323408 1250 747322158 747322171
    0xe06030a081801031d0d18060f03051005130203090d0503091e03070609060b030c0a080d050d0f020a0c1104090b040305030a06090e0a15090c0b03091c1205 68
    0x40149901566800c0618010b1000d04007200c440050036a150b6402603109001d00803440b410f41002410110030560355148504404c8001031401074001c0c0200c80c442c5c0c800c0107444280d140e0b10a80410060203c000740703030041101c4220304207800005981d484d00030180100d12076000d07025a0300d24014401a1070f010181c000700d01004010001c0109110010a101c0703001c0000d2548105030b144a00c41043c07442c003d031540035003030714030b4503d04004010050b400b400d03249409a055a0194690500700119950b45203e030349a81e130080310003215690f00c182c004000c06c40c40014001184450809620202d810801028001c60804070301801400000c140020021030201c03018405080302d60354012030300501500007001c0c400b022011800b200000e401140c050164403508114902883c101d26581da40b2589003642d484403003106450411100340603540106400c80d05010405180c241903000c00c2c0e000070071350115402800394a04200083e144880e45440195946180b0b880c0c0c00c4283c842144c2014018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 747324658 1250 747323408 747323413
    0x50115090e06060319021210020a0f0e150301140d200a3503211504090c050609150310091b1403150d05060a0608070602061b070b100e0603 61
    0x1018100550745101013845d9410788041e420703083c41c058820314003a50300603111905800864035803003103507203c22480f5110103244d0711400c82c0421501480080340c6500201c0485030701c2000180304151024078100d08901d00a0a01598a0302580b07a1007203181c511140c900181031940d1440225140c020f100201500102100c3c41c45800c1800f600f00452003003016285e6030700e081001c8024900b4003842a00e072004801407138640c0350382071059040c0c14500c0494081d503602000039021b01d6203003402c3c415103032010f078002060001103003040c0411440d83c1000c403125074000c0f01500d030406123644c00d44c0a1800799815151a4904a041600880956200d448a2041050846042040310394448050b90314100150741070760340c2c0d032114699509001900d44040307802c5a0404803100030060300140071032040000481c10002242c8405606840c0c400d1b502c40c41d00140d0101012038406c141e144101d66a080407244010328001c403d0742c2e510b440e0501111415112210701a0810031600c070f90b000503500a008602 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 747325908 1250 747324658 747324673
    0xe160f0905012414040b07050d030608010c0e0f0a080a300e04050a0b04060f1814010e10032406060f050f1b0109050a111806010507050115090e060603 66
    0x9895000389143d4002c1101441582c4007004107002101c0180c490100340c0799645403142031a9960348441d55503100081d1402000003040c10041c410108411f005542d4840090064000c100203014880805030b40003071202030010707030250100424481e2601c0380e14035480d100410070420003810489080403514180711400d013524554800e004844200088070005901e889101e000c00040c00c42c00300e960f8205140c81008161100122511f000f100c0c807594a040841d0407a1052501381d510004030f43d09a21003410040c4202c500d4680001c0d809848000315014845c0d0b651641daa0b2441d00e010300d4080e401c00d20360000c032008080d029840140c403017400e080070300720800703d40140240300b0780c0d940b0101c0e00008100c50303e81c2d8480503035900100403060000c1c0000c00c02802c0c001d80710041c12400b29501c1c0c1c03041c1c562040c1d030b041401c040545000e4a04600450356a00b10042d5807640c0580c0003140c0d1380d541e07045010b18001454124602030502800b00103807080780344900c1c41c0b4000000d00031500c83d900c9842c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 747327158 1250 747325908 747325949
    0x607020c0916031b0909200301290409090212150a09050703060f06180b01050a0507051005070f020f030405030a080c0304030503040330020607030e160f090501 70
    0x70442c1d000360761000040e41e180c04810703049008004510414003105a1200c902980070740c03085003a03040d5810f0040404c41c0320002c2460b114010b140081c01007c0b048148010000b0449907180c58138082c0a43c01c025452051500100030706a1140e08a00030845e0b81e45498415402e0207014084e07103200700e80090090f14501c0c0c00b080842000101305040b02d0b03403074410820400100740f00d480002d6074080ca0500008203811154070141016000d14414074154408065101d402409610721034401030319900d144c441c0858049843d81d0080c1c2059503d4070503580c00d0b02001c4002d1043e103110340a55551041c142c6c440c2c0400900b0051111509805a0310602051101d80e50208403051407941c00002103a450000c0d22060742140500e80c405080d901000c24000300340048055600308254981c0825046c9102040c1c0f840164000b581100006074020340024600e80e002e41e01041e85140004100e0700f0520303400c040145299005c0d00842e51814050070300b0070012503a13009140c054444003169540c0d001450 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 747328408 1250 747327158 747327169
    0x6060901050f03120409020307030e030a090303080c1605010e060604023408041202030c1219061b031401062d172d01230a0803030f04050607020c 64
    0x60007820310542039903010462503a41044120b00c0380d034180c000c0540b00d55503a91400d00a400460b01500071070b041001d0b10050301408400c95143c2c08060322655485801d41d101100d003032000815030002000200003c040044043c1d0989000601c510000304079420b0800c805070038810040d00150140c1e006000320700e0308010704200703400e010740d044c0a220fa141d24070301c5444c0804c40c0300c1d08029013080c1b4005004100408d101e042c0d003c0c4240260101d40e040300004050100ca807044c001c2101090b00007008140d000b020a1250308986030160b040441c111542d001010303405a160030719080030a569210b9150385013540b1b402c807801080d582c1021804800c09076010110055030100300c540300452103041441d110300074580400003000580f000d40c85440c0041042403444050020516107401c0c50140b801c49450100360315040e82c2c42c03000d64461744d2000e0400694059410200a5448088100d001c00c03c21350420165110340c584131510600b030f04040c00d00500f40300c406081b54045400850141006450f417 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 747329658 1250 747328408 747328411
    0x705070e090718110a111c3002030c0a0305312d0501150602030919050d031e05041a0309150103030f021002041404150e0406060609050102060609 64
    0x8162000720b100340f441c40f003001071060818044400700d0104501265a0748948030f054680c0c0310504441c181d020510344542d42c00725a80703204002a100010381000c14400b010b0308400608240da10b02c14200044000c1010b0381c00889a0b0152460701203001c0407042c0d4540902904551411a01c506c0240f51500c03192100020380b0b0b603040ca0031500400c68040003100c08a03040d0b10152900c0c0160001c4035192a910b002c1c04ca01c405486660a0071101d1401c0c114407038000d401c0314400c1c3c000314a0b0161103000d001108014095580c2d500380c26100004603521038030b402d401d81e00d21940c2d034160400940d0504060056013207040404000c010f01041c081156002d1903243d04c0c0c17810354441622503490061081ca4000d641c0b0303110810b581d408000104141e0000d240600d01e08480c0c0036216120899615441207020f1840342c51510f031355060072a07072a428103500c6500c41c9901500381c0c0c2c4000e91144880304004105450032138406544038410050294007407190400791000f440507020b01c0c18070200140d100c040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 747330908 1250 747329658 747329669
    0x20f0106181505032d1f1415010e030a06050c030709151d0a030501090b06030f01090302030306040203090c030d0509100e0f130f1d0f030c100213090905030705070e0907 74
    0x2401c0b031086000f06041e5201c2c3c40c0030003640044070b007258150914000f0741244006c90400c1d05040c070302c0940c1102440300b0403511a107508840300740350036030060044801c1c0d0030801020fa05409100d0204000c07610600072103210b0103400415075500d040145c0018850203080c1c1c071600740e10b100074560441c0554800b02403904504421074103008450b540d00001c02c0ca007640c0d0b2000f8015880d25800400f00041c20b61004d11841d011400c3da2441e1304a6550103080c0c400740d8000400503042000041c01900c0c0580c0555007014540b81107423040c0306a103000ca0310f070907250b102c8880032450224904800b803422001d032020f41c80780c600d8405105000c000100310020b640d01e0b007207031140a9000165411590b141d104a1046c800104144071503d4140001e111980c0940c1c52603082d40200760915541d080c0c004100c0c0d036417500000050803851003d850341c100035084007140681c00d040003140010031204030b01802a41c40d020300091669200e4605d0290320b0121a0b6001b0860070381802c041001c41d0034049144012502d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 747332158 1250 747330908 747330943
    0x15060f030b07050426010b06160b0105030609030417030904050c120106140306130908030c180303040e191803030219020c1003020f070c0914070e0a03030f020f010618150503 76
    0x180e0144103014120b51300701260008d102140030345400103900780c03080807140600011001662078009054694104442007040ca40c010003003081240d01002e98070744102500c2003606d0038485170708000383c15202c0c02d44030001003007404070300c510420780700400c0540104000c0c10702c100c05400541ca003610a0100810301c3d84160140365031413009800507007252646a41c8940c03d1580c0c0d2401d042e8002041d001868140703200c80c548405241d860400000b03ca0070350b122a61780c05030320f64841241c0301203d070301250840c0b042c1342c8602849950a49600e145662a4030a4402684480f007104007214031224862000e0115440000250015211aa00104100038038600582e0300d011a40000b03490b44113504d001454a109000c001901d10655440100543c4103100c1400c01c81c0c64520044074005d11352104141e2000c1040d1003000041c1c090fa500e03203091030b60390050f00c0528a410844c582120142e40c000180c45614898020b80220342d07100c1c02c01c284400d100d0b100c400c64140b80200c0d42d03130103865034912400b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 747333408 1250 747332158 747332219
    0xb22030905060904090515010602150408030c0f25020405150a06030509031b012f090d1104020c010c02240a02220303050904060b0403050d0c15060f030b070504 70
    0x81e2216000443c0ea10380200032a0685400211324050303111f0248a51001400b40c02460801c007107044844038080c3c2e4010031701600f59105c00c7d079824800c3c4c0c402441c005070814108100444041c000d04a030700040d00c02c00450480100d140140300c20364100416030694041c5090f8115401e6540920300c40c241c03074031803800280555441c14030354518400c00381c06006003905082c0f100c880306030541029010b0b02443c100009145005031440e080310200715031050f012a0140185100f60400440c20021780b4044c0b2114004030000c4c034007107001c81c0d115005405007030351660285510150100303c0000d204803c1080000e034040c1c815420100c401000e00400681c41d00040c0d010005500141c3c0ba8250100201144401c1c1d5600d00e0301a010742c1c02902e1090280342806000556500060b0944046079004000b5000020082004644101085108503401c1401808400700d070400c1d8850540608500c000089425017142040451400010144010000c08110501103072801040da00d408107120312650300c90 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 747334658 1250 747333408 747333427
    0x5062e0f030e01090b040611030106122004030f0c080309030a021216061107080105071409011809060501090e100324050f061f020c060906040e040b2203090506 70
    0x1038220401810b00d03075800c118190040c0407200041c18040c2e4403e01d0204003480000c0c548800600092141d0f03400b14403080c070310440c62403194002200450302403110f810107062031000e94111f5000f0342c009403041800304031442c04010341e52041c000a00740a0004504188070800080d42d2240b070140020f0080c4c44443c3c411603140020450845881d03441c0c0481c0030880d03201c15000344480b042140400043c810a040010515418850640a18400e60f108205041030111403441c030b5102d0780d040d07410440c8100c50b92080001c5c005260014103004000030448901e040c0c0010580e03216904100000703000f1501f40080c03010300fa00100104c0e54001905924440d02c5e101c145882095171404212075400e080420503402e40f900c225078410001141d03400c0305011182c0441d03a064590303242c0c1700b016034007009003200350b407529001800904400908030761419440300c224942c141c03020b40d012251038608001344842c050a01e07401c03a9401050302c02c0c1000c1d040c440c0d10f0003000c040c1c2c41d1150030300401d0002841d411 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 747335908 1250 747334658 747334661
    0x804061d100e010906030501050d080a2102040f0902390d020616050a0c0b090a0203100b04180c050402030403173d0e07031404050105062e0f03 63
    0x120340c000140a81a580c0d80c0550180000290202c0c5500181030044003080060082c400c0e1416120b0180510782d180002d640d424405034090075000003402014040c0d129400c00e40802031045207c0c0010150302d40d481d006001280354001e4000074811030060000048120740c15400d810703414041b540d901c010801034442c503207942080800d031100350f0103102c542c49941a000a401402014508600600091a22381c2120355000c0c0d959208005064001c0b05808910641140343e00510410242c61180c009680024580303400706a80c3c20780c07030344c480d10201030901e054845d12081c4200007015024000d05a651616031031460701400d40704540c044046010b141c4600030b1001c030700c0a40c100196090820a401e20b801c1c14402814070304881440740740340e4046071843c04160001c420090b0303411a090406000b998403034002400743c000c0540d40d140d102140d121001190340a81d0003100000344904203841441002482010f2420301400300d09800c1c9a9400c84400c401c1c1141c1040c64402c0040c0d611040460 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 747337158 1250 747335908 747335957
    0x9040f1a0c070203060106090e070e1c1b09091205160b0a0902150a0c0209090a061d06010819030c021302030a140a09030905240412060b01030603080406 67
    0x3008400420100440080c1100c000d04400380202c045450036030b43d81d0b200f29184080d0b030140100010b05d078404034240ca806094181d0511030002c0c0106c01408441d0201c41c07522090105c00c0d10781251807241c2120341c140c501240f80142c030090a0501c900251500c950409901da03011503000c02100043c00000c45500e14455100f0780c1c0d01c00140190380c1061003122010740911038007030b03124000401c3d100104540f1402205e2501c1c0550b100c0d0480d107005da800700314895000400300b8015001d10345040c0b0008900d4464071020b06215071641c103410102078540340c030703028058010141e158052090f100c0c00c0040661124996503051030107038660741c0f20740b01040410040346a0361070102d001205000e648442c58200882241e00002c1d84407440d43d90642c0305003620200000680481d1214009004606200035043c03480003107005d1074502242d030840035540700d51043d804800041180381c0381e0703801c0080714000d03220704c0703074007480c0134404a800c580700e1010740c0c821442031405020a603122098086d13035130906c80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 747338408 1250 747337158 747337193
    0x10903090510021203091507110c1813080405100305010e011710020f090301150911070209070305040219091a100f0e0a1e050f060a08010905040c050d0c05030f0c09040f 74
    0x22040c40c10318020140001d80b40c80c003190303110b0040070424001428800418410716400030bcaa1625860320301c01c15107038103c00d040541d610001044045103171780b1501100202c00c9030304ea034001034640c035100300c038181010183c10503107612100c8070b0074240c0208001034510094401100050741d411000624051070301c126003105030154284074030940c08040c0c2c41005001c9403002d030028490120110b6004038103101d60100258000e0410740490f81e094400d034440c03a482840546810005074503066078111161440e4030112a050300d41840e6003400c8018a034450482c0005d41d02c1c83d0552064184c090040180b40a40a0030408040380341080707031391040c0403280140240300c4140d50108800e1101d0700c91100c640240ba0145100160500050074a42d048036800840303030b5a500700030f9017064062009044060411b582c1600d2010005c01c00d903450361a40c240d07103482400321844503442c1406150034180e0b43c3d8580c0c419130b0081004010710303880d400c1c00d8503030143c2c3c00104684c11b200d444c03034007051041e0009203d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 747339658 1250 747338408 747338443
    0xf0609070903120815042304050a1703010914090a120509180a0b060c0d0e0d08030126060717040f050d050a020c0618060d0605040e01090309051002120309 68
    0x30340700f03c1500144401e000d50412941020700c10140c1050106664281c940d8654100c54140f0100308481c9510000707800512440c00d03201c80d521591580d4006400344c10180c00503240000c01044500020702c5260340e101c00e44080341c4914502041070580300c051440b8040c0528500300ca01c4030840b48260708541a02c00024200071203400700e80000c10320740344201c2e00480c001d03241804a080714038014054414402481d8000e10f407007800b50400700d4071101c40d41d91844e006581500980000b403846e04c0958007034040d45042f40c2c40b0b0b02c134103451075011848100740d00d0310b1904100e0900180a44c0b000d150001d610103154480f00c0c6486915200500c0c413050000544680283c51040d8100c642c0000280400503150b400c44038402c10310300070487d8603c51480c00c04119044005c0d001c0c920304018025103440c5010002c009041c83d943c0c000b003001e880e0303030031070503205655641c00800400d90405c800b100038102c103440d41c5201e030780104000313991080c5d4042114100000480040c905090810415a90303032420500c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 747340908 1250 747339658 747339683
    0x9030b0105191a070302060615041a1c0507020d0905030d030e120307021509150a050601170a050a0f02160204050c0c0a03050901080106020c0a150207270e060f0609070903 75
    0x141581580013104124014010744000c00c80501d400380c541c0713100301101c456462401e4a841004020107804400c1c4d010303400307024840001e8040b20f008103100d0a010102e80802d0919060100904002164560034103110f0051400c0c0015100041c60b00c600803030500300051140c01d0700c00200d1800b0751070580141c010b0000400c218409a001c511001c500e0b55800c103603500354403101c08050321007480541e0000011840c00000d010980190401a00310b030b01070601800504a011062101b000304031a9828020b071244c040c06814441d0303101e5000760500a803021400e1516080354441e00d0441000c010303110f1078954000ca0160500b05e81100c0000744c03104c08488000303610789400303001d5070081c1c107120703000c01c800e5400019100d00226030421324a100500d01000582400350fa40c148c0b0500540e0301c0111b129000c00810069582d5042c258407201c1c0c200c1c0402d00c0454201401c09482c0030b824091402d401c03040070301110000402d0b1441e00041c040b242030078143d6885c101103c40500c96400684803a800ea03e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 747342158 1250 747340908 747340949
    0x406030503040509060303190c08070f03030b090114090408071b0311011b1211030f0409061502030712260f0711010b0612092d0d09030b010519 63
    0x602c1216800c0d13401550030b540b594100350701ea008020b15082c0c02c69040c0c43c0c1e514414400c000455050f40715446550500925440300309154400700d04c2100802e41e0340201c00c240b4034001481d18011b0160f40202580340101202040c55844040c000415500010841c142007003005110a04160b91403140312850540c0c0341005a43e10280100300c601040c0840c525907003e141c41881801402c1c2c02c4030300c00441490640c801c484202ea280d4042002d80030510006030310303120034801040241011140820180d0820002c010b07009940c013540e50940d80100422000280300441c104602350f00350a01189103039000102100707c961802000410311f16200410803220300d58950385006148503540c03044480485ca065500701c900f41c2160aa005100703010b002103016003540242d0707102c4100d4044d240480202d4030181c3c11020f031080c91a244002c41050482d210400f08020000a82c5610f0100b00c0b044c61a102c103036408030127002c0c00d801380b4416140d0b80a003407000d2000f11300600d40317415920324030070060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 747343408 1250 747342158 747342163
    0x1507050303041509081207030b10110f0d080106120f0912080f0606090f0307030b0c042903160e0907260405030306010c030c05030f04091116060209040b04060305 71
    0x441c1d040b110f00c0094818044107040d58414519016440520a86000b00340540c40d4842540100138000709a1135400703010990301c03044a9101031901c03d071900701c0e0f0f031a900141c042c00c0c0440e088010942d544404900d0001c0b41d4414142411240d0764100041804125002d10307000c1d201d060f0300b42e4405414a20000204406000028071045484d079600b5425103540d0b03100748403000c00399002e80c1d20040c240702d086510324002850170b0701010000d0485450903034a82d59480200e8003242e1402071060701140400082c000100143d150341c14400e4000e484100c4a80700d1101408083e01c450b00003490081d121030741c2401030a121131003000c0240010490702e08180000c0c40f104c25941c00584e20401481001601900c4491450007107511078040c5003503036200d80c01152140c019a606a04100400c4500ca01140041c00103004d0013000d110301950321030030034040c00c0503036900c1000046580320070002d08107860005080b005000f5484075016a4440012000070701401120110903441481c0c11400010003900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 747344658 1250 747343408 747343411
    0x102070c0f050303130504020f070b090705090709060207032612040303150303081b130801051e280e0f07080607030902130c200309011e0903111507050303 68
    0x44024012400d07240c10a1640705c0c060208031103a0105d2002c003d100d07519142d00541103002d0711440103410400d1030f40354003d0760a0280d4000516800c0440d0a00c41401d10700d900c15070186060a061100c0380c5007490007551104a880080c2c0000301c41c1a82402160040400034804802552615140d101d03140041144110a43d02100480d01e4080381c0b1a04d850718031024403c80e41c164075002c50340c0e0385540344100d0207240780c0c401b540700c900b0401001c420428201440300203440c002c8000941d9203040c4140700d4104003842c04944111105900b0010041c0180c0103c503604602096400c80820140b01c8560141007060f200c0f9a0500030000390b80061500042d0060450ba2010202d607560703101c02c10b0070b408413503103420003a40010241c4443d6610103480d40001d08800f0107460710b5140f11007001c0c594403101c0254000c1c804982c00004a1581b00e6920a42c02c280e045058200c0c0d80c550428184003500c0c040c00381c4030092012081d6401228a991012498440075060405140d9105003034074040b92607600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 747345908 1250 747344658 747344669
    0x7080a030c02251707170a11240919080d27030314090a030c15030e030d0e011103130b0106020f1f0209040e0318060f0403030e0a080102070c 62
    0x900240030446901009040c0760040100d20a05040f40c03c0500c1a02060b4401c94410914490742100041508001c800341900b4a04200901481012881c00c54401c3e074000c8840d45c860b0030000c981030f50310164008152031550b0301c0c45c0100e0f610f031031600c00b2400340b0407240b260000d0207a5071180040d030074001082e095444142c942d00c80100040d80d41c0e0784020f541c1640000036621000c5c040c144006800b4200c0c0c4941c801e40074090310f042440d414001113007100780d60821a4901d0040c202000200e42c91902414205a0f5080134840c81d040101c520307070f881c020403250b0301c1e01d10344030040139010800c20761003160083d90300e5100ad90b8a2800380310043c002c8211036421201009200c0c0000f030114404034891891680c624050302c400740c007480c01c0141c0c01905400d00420b07150700b04205680366403144150401031000304003541d21003810b005e01c401c0340d48410502034090fa1080018a00c440d20303c4040b01c0503290f0509200001803840004504070103840c0e048401d4135840003500c0f42c10320000d608408102c51 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 747347158 1250 747345908 747345913
    0x1090506061002030c07030803190c180506070b0a1802120307050f1b0904031b3c0f06091a0105040c0c02030a20130204080c0a0e041101020307080a030c02 68
    0x100000300301d91328418010f4204030b0b5045000141b0004022400944d002000d8400640482c10681161011185040e8210001c214100d082607142c00c000390380f80b40145011104581044826100c052150f02d009100003035060b900c0040250031004800903201968000e0200120700c50101c008656a5120b040140c03480c1c4942e0a0b1880b01200001c0c080360000558405052030101d00010b00090801c041e10071000c6c0032584000700d4908500038031411034035000c0d0005c5a05482051200c141140b01128000700f02040380721030b1081ea5119055501d0015800150040a42c20360300b004401031086d4a0014419209016003c1d40301a00360001410b072a001c6400704032090185609a506900c4000000c0d00340c1c2140c0e16840c082825071100e503e0749641007003102c040074001c00001d1082d80c8070090312000240d000c10b09022044040203001081c46054900c1d110302400d01e01c4290107080000c100520b51303910b116805940364401e2099990035540040d44d182c0341c440b6000040c1c0a02840302c00c180051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 747348408 1250 747347158 747347179
    0xc090a0f020a0315140612040816050c011701060c2009040c09050c16060b0d080a03020c0606150729010923040305160309080312060a1502031215030109050606 70
    0x150005c0c03038180b136010b8000301400c0c6442c1007a4804100b07040010700690f0340007005e100325041301100c0c0a50b0302070742d44901c01070062040f0050025100c018820780003d20146040010302149400903200200960498041d0300a446030b9103031144044120700a541c1c01c42550014032080004e2220345200750f80b005002445a42e40b0541400000c0c041d0000400d51000c0385a60200440d1a46c0e03c919440040a082c1100221241d1a000525407090800c1000240d0006089000c0d007010300445420910444c1c0d9024001010500740c1014020004043c01070050580182400001c220404200c0340030224030345155130750341595074010501780d949401c024540f00c044115590005071554800c0364541c03141b5080071290544001d10034100c901c1241401890b100c04a00000b041025040700e4510000908103458040240621451a5442600c80104107000c01040d590003100b0343d45040c1c40d4924164140d03841302d80d440c002c2c4114090381a01540b07443d940109114010403020b1155000341c403c5400f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 747349658 1250 747348408 747348419
    0xa020a050f061501260c030a18020a03290403030b090f07080c0a09081e0c010212030118090f0f0308010f03170a05090306070305010302100c050c090a0f020a0315 71
    0x1241e1048034045281d4104182c080c44640c00781c448010880e89540c0d075100068285c052401c120360b82510503000c480004410030445030100d01a03078055901c020004a01c2e08215808903041460341c2c00000c100400b02c14080a040280900e034408040c501c503445800344c202420003800030600441c50307500554241e0000707040820f21104081c010207483d0364901c06503803a004400216003207540c12104100f4040c10000d81c0400c204810b000c130301561081014038145001d6540d01c2d0a27150346c106c0e07065411000010705003404460517681190400c0d50700d0200081180b080304018116035200500c0c529681c00920305100d8009a05c4180701d10903101c07186181d0702c0310080c02076041c042c80001c1203801500e501030324100240c405041d440849081980c00c110401c03001900b045001c480d50000240e81e040100154906460780c05011049400c240c080d9803525100c7e00d07101c03541c2610203030044081c0c0d40829104900769025603814070400004648840c002d800060180c08440742c404c3c042004c0d084007041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 747350908 1250 747349658 747349663
    0xe01030605071b0318090603031e0806030607050a02120c033406020d0207080c060702010b04050f0a1a040606020d020f0106150c11030601090b040c03050105102001020a020a050f 78
    0x88003030400060201c509260b9134200e4076540141c01c0c03c45091051480041c00012a0145c2400385220761030f0042c086041d9038004c1403a101d903160341c50400810300107115840d00c010030040e400181e1494017030758132840d05405a1514408181d002603500300001d1583c6901c0010001d48400300249084070f482d0011000c0d440741c2000081c9141c101f900c1d500c1724003000100d265005000114000b240541001c109440d010040c0c2c1003440c2181040d009001000310190303080c456803441600490b000c0080781443d04071240b49078070081084940035a00c001c81051581b00c404c152182400081081c0885601c0b510000c0d11418500d003018054424010000e00c0310f41d040c0a02c1c2c0039a9104c220854960411342800c81e003034241804151103441315600c81007415141844201d010b030682c0000400c0390542d0b5018001240d082c072000c0810580313040014031456444490300000b840325171805a400c9060050341041200000301a0545984000349144c0e04603000b05000144d90f004d101515298403501034000e8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 747352158 1250 747350908 747350927
    0x91506070b0a0b030d090524030112021815060306030c130e010b030f120307090f060f080a0515010509060f070606030b0c07082b0f0b241905090306010e0103060507 72
    0x1003224584240503e040c01c8850928015032040b0101700782423901c0d1b030000b07550b00c282c00c44461081a100a0005d500307045c07000c20342c0048c00c400400d03140d24110546003281042c8100640c415540000441d5503943c1c04c018042107520000d24002914080000003002004215481c10702c81d400c00e03600258134500031901c01203180d110006045d54002c10581311126510040a83c020b200308001d001c0303134000b81480108058403440d00c41c2505c4041c00d08003c1c2032204028408007a0604000811640e800444007042c440d0000382071039500caa0700c4e040090b0407400380c40340850300020081010000e2100301d07080b050803a40100140c10702c80e150072050425a1095000c041d141c0c0e0400c2048007503540c1c5180080c94041c00350402c01140c6210580c49800b55070990540c04105610be40c0c03008428030340310708140c0e10303001c2041c089000004410b40c0b0341d401c0d0040c10700d90455400c4040c3d80ba0280303401078040301c2c82080e00070251842036031500c080f4402d045080c0403d5800e00c0c0b0702000580964021524036 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 747353408 1250 747352158 747352183
    0x110313120c0f11010903050303090706140f1c0f02070b0a061e0611070306091a0604150e060613120b070c02010c0803130803190f1505091506070b0a0b03 67
    0x3141d040e403941c03030301e4840b050b0f10f403002070400818940000100c0e20501c041d6000c1d19000c4081d041c498581203000f00a0031800e8103550855208102404c2e1440303087c011200c01c420008140b22031242c2c018551402003216040340b064140c00041d014041004070b0280c1881205444001c002180e20b41d04650381d0408941d1b110307018809506414049603001e000f0314440c0310f40307002c12505032a4803541c41006844110350122164034641d6046c44c400c4a60510407903010b0001e035403c021105c0804502c00b800160740c070824190241c6034002c1071841d103d140449960542d5403002118850759264101030101c0054010303100403201030085840517110320b0351011102c1d0141d40f4010b18010540f156860395001a0a031155401921420000181030b40c1c003451040500440740083c1d524444c1d15901520182c50034000c10502c0c11000c44020700443c6c40030029200203840494981c0e44440c3c01408580c0d141140552040300030400740c00700311121004500c69020984240302c2e14a03500149943c81c1c2c40c1c115035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 747354658 1250 747353408 747353423
    0x30e030d0914071d1005040c0e041d060c0d020f0a1119020922050706020120071a04021201020f07030e09092e060323280303110313120c 60
    0x80503c0c01c0c00c21038011780000105d10700d400340d0f40c3e9400c00641220000c13802200494105443e840040c0761a118001103145501e04070549010a210001d03114040200b840e4200310000c038400007040d6503503050b502c50000d6508045e46c5c0b10300c0c01c4c1010701261009808846e0a01c00d642c3c000d0000d01c070200c02e0300b4400d80e0207840038502e504c80c00041d0302070003c040d802000c0d0300c1103402c0c10b601144080200348000c8c005030700001002110600c00f55501c04a1105034003200c0403c00c00900001e9400184508908618140700c90076150380c40003800312042242503000540c00450103ca01c0c10b8850001d081d0644241c42c2d4003240182c480510042841c1280c0c105115040843c0012403040c1c4108624039461080c18482c007280810f50684084510035002a2541b0b6a18980c00340c0d105072452160604207039650040c1034103a041100310141b1038a6040b2001d0f42080d041d044000c140c0a50401c1c074207680c405140645074900403098414503024180181d034620458030b00c8185540c003070510100d00c0c3e03402c42403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 747355908 1250 747354658 747354689
    0x15240501031a2106061e090603121305010306240c03030b1806030f03070c062709051e0c070204020903070902162001050712030e030d091407 62
    0x15001054800c010b42468104202c0d01015039980a410341c4001c2d0464101e558420740c0c5481440c507000c00140114043c0a0310400e01c81c41d03c3d00004503c5441340d04490300080d0341d44040100f41001c0d0f405010240004000c20103e4030170710010000e80a0300c6003a83c0030400d0640d6550f900e00e030401240c00070f45100404803c1ca5103000c0c811040a0303045406410701049903403444012a034082310b110000c030500c3c050081400880d01d400d101190f4500500c030011804d0010faa1a9005c00c04894414a814010724220b003005900305001100c03212410f0a040b16090380c1c0e510b081501500007182c0c000c1074903510500550746c406401013414010f520902200381007480e01d80c20f20000b9404502c40c242d051007190340004641c001800144111617003614ac10514010074989030700f0024442c0d048112030180c1e98051480c41e40c0c4003050782c0c4d24a0300308402c0c0b03601110225042c0e004205481502500e4000003e65001d4410030350800740213180b03ea00c181c02d000c3c10030714456445080c1c13401407810b600340000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 747357158 1250 747355908 747355919
    0x2205090604030f1b0804080c010e060910111005010e250905040b0607140a0c12080a05030c0d091209090605100e060c060403081801020901120507020f06041524 70
    0x200240740c0400e204c905000d6000c103d0300c0b54842a00f256100c00450b50041c90b4494055074801840022141c007501c03074506000d800360010300c405070440000350410040e00c02c1e40400d400c1c10041400c42500c3c6410030040d40d40c581d0321002a810048680c6041040901c44141020451420180d0760840540e41c1c919090b08000801c8043d05100000b5a8001c41c240030b010041503400c001e20200c41240d8004003000328192604000b4100c0517070000841201d040d54140104158100301d990b03250141c644650303030f0f9841242124490180d0300031080340340c0c0b07018101c3c020083c0c43c00490518407403903180c2c2142e0950b03649414068850038058941c011120b00070701d40d05075002da0540640f000004041d00d04200300c3d510158034041e8125800d41c0001c40001c14083c9010300640c0b10301954030840020351038a10b5080001e403144500d051000341d0541d441000a914520a00403850b94010b07140641d011410141010501000c00c0d0104d9002680303402c8040d1902612150304080055403144401d040c2071511 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 747358408 1250 747357158 747357167
    0x1514130302071a040803030f070e0a0308090607172d091f050415050307120506100e0a0b04060309020f09060a0b180901030302010903030e030901051c02092205090604030f 75
    0xf9090000c6050301800301051444c41070010b5403281020303c900800301d03e4500c0004100c610441c1210b4024030030090207001040d5140120b480d03103901a200240d60305180d1030b103c80580f14528181107202c40104000c0c51040301080070040041300141d2500b410740c00e201d9190035130b10490000c40d84c40b0284c1103410800440840c0b05504101d0745e81007003030030950b988c1319030b0052104c00d1341c2c042c0010310000f007044213080e0009182103030388070550001c010500d40f000104546a02078400032090000d8551001110f0303441080c1400541802c5c81c040f83c680340c0e41c03035024000d0041d07004128441c00d602281c105440c01e20100c0103110702c00c02050101401d10340050b80540d540a810071004000388103482501c2520f541450034020761080e40005000141810000e0880320920000d0f010b9420400110615aa009040e00c0d80c1c400070100c44131740414041003d41c020b1084154007600039581c00b000e1981040c05450703810905060800034003141d139031004101c2e100c01040340c000740032542d010808036495214 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 747359658 1250 747358408 747358439
    0x2a02040b0303092e02011b050903070f12020f0d2d0f0b01061107050a090e03090409080c061e040305071a0108011b0908100513151413030207 62
    0x9410b59260401c00004504900914000c01080390380040002c1482c5804050b5144110f003548001c0212001c150041d580e04d01a618404042060104481005a50a01481d4020302c481926084495a980003062042c0c0c42140260320500100181007058140003503142c80d20f030781c00710221031000303035003880d804c1554580c00450084407610f50701c040005030700340701d200040c5000f070f80100b40f250301d00321000f000900e40d640480c0c0f0940004d0800c03c803a4031021840d00903120703141804285007c0c010441850f6000e9010350301e9109085c4840141400000c60040c150045042c042d1815a910081250040a0071384000c851903035101c400500881e00c604d01400505218118140703880c40d420070882c010190a0700a108541d40d10030f01d046104d440304122040b24540790822201c400d140912240c1c450880d400e010150740c1d20340c00028000d4805400c92a012944074030304408000702c603030462000300610030041070120a1080461010301c00d017002c18001a5160b0700420303050b41040047c0280310071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 747360908 1250 747359658 747359681
    0x2e0905240f0d090b0a0b030d0f0e03010f05010b0301030c1203080403050d02120712061703091002150c04060e0402042916080904060506031902030705090a060f2a0204 73
    0x8050003119070510190040c03034040c9018041d400c0042c2820302c017540456882d0403455101e40d1000808901e1b2542100403400c0740e070402d0414480030248100032a0140c2517089900061503d0000040340303440d410300146041c0c90041103c0e010701c80c1c0701e0030103010005078654041c010480e914000782c00688100e000301502a0456805030401184903450011414160361030760114886100452001d021403083c14020541e811541d02450000a003098a92242034582070058900007006c95050b0300070084074132a01044010003490349845161481190001e0003500700180103640101168603060090310300b501c00c006158288003560540c0c0c580c588001502480e941ea8040c0a400c40d038104001003800900d01032424941d0307070240038081004a81107a0400c5225100074002d025003e010703070b070b900100c0c50b00d00100140d5036260080d0503602d5025010040340e10054605003c201b45a1100031101005510f44900c0c40f0840c030720142e6120100c04181070080340c00900c401301c1c05860940c000b00b50f40310 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 747362158 1250 747360908 747360937
    0x2120a02030a060b07110415050d0318120b0907090b060f09030c3601060203070f06061a04080118051902040b0a0902310302040b2e090524 61
    0x150740d144da440440d0400349041c2ca41c1c458504042100741824014007118920381480c1d41c5c00942800001141e451142d4006001c011444442c1c0842c03180c0400d422001d0485450780701c2c1c0541440ca0703d103642d20701c00c8540b9075042c042d0000c0000d140c0c00ba0b014143d140b58000700540c0c02c004152001103441d0300100e1900d689480342c01541d50b903c0c0c032074032080c072490818401c0100300000b41c00c00c411103440616100f0700f10f81c851000100031455012058036481e0754009020b8145800302d05055019001c5500403840d20b86008000c0c603004c4103a8401007013280e408030024008a40711001c0b4010140300241e02900070381048a080000b20b40d6600400d41d11840100f002072203034500008a00c409101ea0404e0f004140c0c00509640c03085540070520030410030079804c6d145030249d5924080c1c40c0504a201c028007981d111011103001e9590360384019501c400360385406008481006488003103c0002c1643c0c3e000c94101003001c10642407964441000d490304c480c0b081040c0704071003114805d60340300c0d0249500f00b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 747363408 1250 747362158 747362171
    0x1003031116090e0c0105031603020f040305010f0902010e040902010207092d0e0c030304060c0b13050609101a01090e060d1e0506060d050d0f120905061902120a02030a 73
    0x86511082078000350041c510001030b40c000c1c41c0310303052816841c0611507041c40320610410000c080f03400d903140d135401040c1c6000347c1c544121140c0540240180d0700024829402d09424041081c2e0a41c07040860900076603d00c81c003005a1010302085500d5000041d00681003c030f07060005a502e86c105840100300c560100e441038140d918407242101c50b0740542c100f502d48404481b40c2e0142b040083e81d10a4000710051850140b030000701070104441204000d080700e030300c280003503040d0311510800d0500340e4218095500c1840c01d050070f262a00e8800901160303062601081a0340740760441b40403103003c541a150036810506250b052004600010b01036540601034101c41c000003402060b00790844101030b001c0e102550014909035013081001042d481c061000f00c4503681c0403ca0001d1155a0b0480c0382c1040304541d03404450484000300a0380c0c04c45082030074540460208100001c1481c828550f100070100c2800ea141100001c0c1c0c400c01d90300c030b10107000450201e14440102d500954001c0400e910002c1c84 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 747364658 1250 747363408 747363433
    0xc0905030106081f050c0d090c030606030318080613020d050f03161103060709051017090d0215040f17040305060a020306030c010201060e0c0a0e09010f06140310030311 74
    0x2940c18030f400115664000b600040f4101444801c0c1e035003d1100040d0500603840c16203140a031502848000002c0d03030780ca5442c0d40d0240200e808803032000c0c54014400f80800c035164140988020f02021041a06192030200000c03500004107103940100300300f005da0342e910111602001040103c035407040d55240520901c0101158003007004040c000318080d6003200c04030003820031038003244400d15014080e030807042c1048022503200a00c241502c404554510b540d80703113400100c2e05004440c50118100030140c00f03005411200003000e40150388a0341c21076040307040b00701a407112424143c9004040284990b000700c0000c403508a07000142000740c021501707041c0c0e03d4444a28105040c1d4070100015400828040a03040070711000da150042800203101c034610340901921542d20062450f06014030115020445600c40c124150500c00c00418a90255840c4e21074000502c9541c4517000101d91000c43e00010b80c264041902d01c42c150b0491401141c07031468400380c680c1c01034880300120034010396840030345 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 747365908 1250 747364658 747364661
    0xf0919150f030b0603150408032413020408190c050f01121b0e010c170d02160506060315090601030b0a14040605090f0a05070b090307030b0c030f06040209130c09050301 74
    0x30b5002d101c60200c07504000084c503040032011448294144041e01c200000300e604107007203a4020700d4221501001999800d941c1c000e03201c00d19800360f0302000e251000c885a00180d0054010b035a80742d0181c80c00408840045034800c000420001c1c40c00d000c5d43c000300510b1602d01d0300035000010606040880c3d0150301c68820884c0e0002422201c090945668404144ea00401d1205050020300701060701100d0764446640c24041000000c0b860100044c500a210703d59405031100c03d24284560a5044001e14102d0b44501e800c07581c1c24081e11070703500c1c12011280c01500150144c0b04d02800745c0096421900d9100a8007001040b80054984410b405042142503134842c81c81a0300400c1f00007040d0600c201410300f80000f1034034039401640418844c030007103040480c41000b11640c103502c00d5560401000401c0c2002c80c81e070700c080e1450114030100b0800340c41d030b00f0096100b080104004400313036840500b000202d0084900303083d000b00c8403094004541c1039035400503424180302c0c200740c218182e90703200003130 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 747367158 1250 747365908 747365939
    0x121080c0a0b190b0a06020a060506010e0d031d01050703050d0c1812060e0f030909042a0f1d0f0a0905011d010e06040b06090a0e03040b04050f091915 66
    0xf00c600072509445003040415109a09044500b00c81d45c840051800340c1c029500e503020840541180e58070008100d5980c090500d8030100c0e2009440d205001806060142c1040c02809440c0c945100c6550340c030201e98884d00031a40e84952603200c0f1401e00412496440040003c03a110b8418041109822180c101000c008040203001c2d4079211440e607003141c50070b07405440d1102480ca0141d030001c2c0004400c2c0d0004001d82d20f00c01820307107130b035192076613282044030348000f445440c01551060340403022000b10b40b000c02c1d80103541074013080034003956841c000040d01100580c002144580c00101250000d900e0168036600020a000089103c004680756203084480b00160219409000c000603d5541e10070b000e5040100721000140c0103d01e41621010106c003401420360703105082d2a1b00007001141d050f40010a10604d40044907100d5460300320004e00341d4864005c4a10130a0300c00d20201c0c407460700c924446c1c03240d0180030130351036010400382c8500040c20841114103000050f010303000c90b010300e0b80700070741 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 747368408 1250 747367158 747367171
    0x203031b0c03010f0e0f010501050913082205010f050703091a0702151c0b090c0702030328110609101109090c120618060f010905190e0121080c0a0b 65
    0x5800407040c0ca45d00d14001c600c1c1503030140c69040800400c941e40d14481da056003c1c1403c0a14804400b8618284c440d510440c40901c4c103003040e0038500d03a80d008480605030191502030b02c5443d009100e00790159028065520010b001a0046506000d8041c0110002a0040325540c2190030511254001113002200701c5410100c4400032501d01045100e500c1c00416000791003c0070400403100c01c01041d84400010510000044000798060454400f00100c0b9100c0c0711070b00340300d903002149807507101001200304200703070000f01441d0b0315007028440402c1803030289035007100a0140c14160758108010305140d01c00fa1104400900040c3d10030b480d00c14409100e0098140e150f40c1d200254011100694006000c450003281c0c0103401045011001c2ca00580043d070071560300300810f0095004a0303040010390401d54101d40061900910450308400080655050440720441c5a0b25800400021072803040c22154140c0504020300209041c00014010a0b0203041501c0680d5220b03125100c0000341900d20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 747369658 1250 747368408 747368411
    0x1515030903080109090f11180f0106170603031e0405060d02030105090c0c030708160609080909090c0f060304020406030606080a05070906060c03050c0709060603020a1206030203031b0c03010f 84
    0x140e004041e80300800d980504503600e01000b0401c1c244c1c407000b00d07802020b030000305000c0c2d039002031418130390f04d034060b0307236402e01100c12006005d01d480c1ca18145402400e1141c500400c403441d030800708610100c1c0c42d141c480c040103001981004140c0c0303000a08101000d0459000f01401c10010807244c03100801004000b00c1d19101690300d524003414062441c100905003440720700300303200e91808080d0100844164030341140490340c9541140c00300f10f68122f00444002c20b030034680440d40080080c8000944600103040301c00d4592903a0710700c02d46848144c1800c210303512008280100308580361640256030030600180000071643e4880d924482114030f69000041c0c6544000004000c001c02004000050040c0030f0f01403285601e4001c0c050455450910010306214000c170702c00c0c00103d401c002c41d00c001c10080c1e1007030199a45d0780d940a8000d5008420724000245000c03420398014640b400b84c00201ca034042d00640c0380c0110903641100140311901c801c515405108411401c81c0d40074042c02d240b13003042c1e100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 747370908 1250 747369658 747369671
    0xa0b0117060d02122a1f020f011803020c011103030106030c17071707170105040c0507050d051b0c0f120f0f030d1b140c0f0604080301090b03120a03151503 68
    0xa00fa17004002c5500604000008101307074011345c0c507051144001c2c1c1c40c9070030451000003e000d030140d0a108440c80d6400e180e43c44e02c10717516a41c3e4060031040164502a03002e8a850440b15401110a00101e032845110340d40104010050188031b580403400150492a007140c14620551404644031019900c0d54005964003801c112520100c111042d00072546040443d10b922510a080042040500c41c59214541e60b50b421140c240c041c83c00c40d0b40196001058407420a011400030307100741c104c0c1002c5c6040c0d500806250503004030001301c9141000c801070103c0d010903104020000140400781040e00f1038041c01b03032180c81902c82045040045c80c40807001e99203840e00418410101c40a02003080c000040302c1045884594020b04c2c0c0b02c08101c2d801817200d6a90682295035490f046a0015114503407140c9001c0006001010014605807000d0341401c0c0b24511141c81015507910380755014100e460300400201d10f0150007540213032815001c80d561301d49800e545d00c80d051101e0701c40030804d1b80807030380390301 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 747372158 1250 747370908 747370933
    0x60212010608311113240b09130902130902041506170705041d01031401140c09130212040c0618030201050c0f010203090a0b0a0b0117060d0212 63
    0x20b40301a4051210b0600510a070121101002e4503156010100c41d2100c0450107442848081001c20840520280800792505640454440144070b1102015641c00503484c000d017500c1e00440340c00302150b84082c030f61400c0c40f2000c0100460060074081034084a56150505401a01c5400c00640132800d04507000600d010240148015623240c1c2409546902021740140240d40c1c00c20841e540a90000c1807524055540050070740702d601c11a04a0b1744e40038840118640b801403140b9405041e2445103805640f80441c0001071801c1e40e03c251a0f008000121310002100600c184e4040c1070022401400900d012a0f5510280e080781c1c4013411050300b50201d03008210a01490200311001440715181c4220780c503400b041040d0b241a800d000080c1004070010303000c1c010010400c0315a14501c1c16000031580c9062030b02d030040c0c2c1e40c003c4210440381210501c00241703004035903202e030072183d000684424030074071031451034441d005100501c01c0e42d003d00441411805030701c602000c0c040329000b00c1c0003000341034481c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 747373408 1250 747372158 747372167
    0x6091c27030b011404090206041203030f0e010606091a16031215140a180b040b10020606120d050706020901050c0607090f0e01080a0209040c0816150e0117070c0602120106 75
    0x98130740504c1c1402c480c1001600d4403c101e90880307030440801e2414a40c1460110007411600740f92800c101c0c1010034000d003602040d8484021141c1ca600c902c407030f05584521401810704120116483c1240500010304501e031503c00c0816598404c2c41d04125040750410b1100844410100b2652048030303160341400804000541070790300240807202542c4403031801143e19262a000c0000b03c0d50a500c80720b2010b819101d036045012007420003040f01042070301c0c01100035070b6907004a5601d8450700001707207000031105002c1132100d841c3c8800c0d542c1c01c0c40c20b10f1f04d454100281d0310030106241040701c00c2080004e48101800301038050b400e5a03507846921441c09580407a000c0301900418500310341340c0b0040100402c006030905601d6410b440b0300f80e050743c5900b02a0010700481d404003d0601401c6e448070154a0001281300c161001001403950411240c1d604480d0320b0803090550303001c10a0b0480301aa09900300b0905c603804a0300e0701c0c00305503002c084e60b91003060fa08a400300c050043c03688801880a076411 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 747374658 1250 747373408 747373439
    0x15060408030a0f2604030e040e0a05030c1203040f02061303050613050c0103110403060504022e170f04020103090507050409210f0519050d050903070506091c27030b01 73
    0x240140f0034040d030840410b030070400245c0010240035481010b81d901e51600d800c0900881ca0381802c2d40c8e29900d107405c1c000c0c2c0300c0e8000a10901d05006191010381e844100e9010349000d90381285810355517209650034002c10340e01151071918010b4140c0700001c0050800c008207845802c101c0003c2c0761210b05840d0103071900d651040f02606140c00c20701c18086410300d6006440840780c0060000c106900c4900204d02030b40d4118041d0300b070006005d807150b05201075001400454448940c1c542c5036511800c1f509c1b21680005a070070950040c21100460059803180e08a110040e0040c001c0d160629030b40c3c00058120340b40c0f120300312010b0403070403d122000b106180071504503d0050510100305516908014040e120f51150650961a01c0c0e48518070a8850400d680c021484001c0802c0981000000540e0702e806c444000c6540d032040000140c041c1501007030a008030074907850400010440c600091f2100801083c4804011055801002c1014200e040c0d2800071402119070303000d9941002002c040140743c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 747375908 1250 747374658 747374687
    0xa050c04110a2d020610080d05091e04051807090c0801050d03032301050f030d120f1107030c1401020a0c061107170d0612050615060408030a0f 63
    0x242100c075480144008007158810711030b502e0120389641a08207289035400c03101c10b20344585404080800e1040707400246450042c2008040440e4156481c100e140c1c2c2c80035042c020303200141c03092100e1040d03810180c0907031000c000402d820b01170080e1207501007011140c3c111941c03003460322030720040001c44805000708805854841c2c81402100e03003249001d0000c44c03040c41041e00803c50b51a1200c00d05110307038006240e00e40020200d510407811440b54100c201401e004051168580c4000d403070040c50300081950142450b919004240a401d58016005184180c1c0810890f516a1301d0b03060100410401000c4840c4203071203030010800d06040c07403040d0102030182c00b407040c1e1042140c2c1c96483d401018012544d0b501020118509101c1c415804860040010003010043c01d0014902400701c10400740c01c44020100c010450642d4a0013aa071114490303410260042d0002c00200716007a01ca10b09841040c280a0181c80c07034542e0b0744d00c0040c0f8560025000302c0025a101400c0020943d011008102920 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 747377158 1250 747375908 747375911
    0xa030c0903110907051c1d1c030506030c040608010912090e011e09051015090501080c0f0f030c1201050609060a0f020f0102040b1903051e1302120a050c04 68
    0x78255661085800541460244669044000102254801d4040b0b5880c18000c044408a95044200e94000b90400021040203881d0581001078000c3c00024441c030a62201c00000c0640c1c01e032901e0030b80040c01c02829031909401060781034600c41c2c85600030900140562800003172074002c1170818001075032155007000200700082004003c280c00020007a41034034800c213041c60035410064040002040c1e01d43c00b00b68030f98102420840900c042c82c020004607441020887c10700d20342c0c0d0202322038654490081034040b45c4074402161078043c2e2900503080380038416404070314012a400000c00d981c0c00890344450000000604044100300c0c0780c4800b80141402e69000c0c0c00e01f000e982c00203255005170241c0700c0405c510564904403140c402c1159031200394506000b1982c803a1100030703a82c10b9510610808410482c0005039444580c82413040310300ca01003c401c120b200c00c204501c3d100412501601440e500078000313060101507078816001480400087d0014a60754050386001030070401c1c2001900d218a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 747378408 1250 747377158 747377177
    0x100c0306230910030b0403030c0306210506010807050d0f17220602060615090406151133100b0d0506030c04091e02220e1207020310020d0216080a030c 66
    0xb4100a143d690061f9040c200801c071407c210344201c009040c50b0f480308019001d125035080941c4981c4440340c24aa000d030050b141c8982c1c84030402a03907040c03103100f41038100e80c541550f036000c11864045254800d21074040c00100749140c03100d201c032980004d084105150414183e0508456183c854036000700001d00140140d4030f0000001000d81c844810790030700303900d0000340390111903a6540c0850b0103010585080382030712000b12402804540100318034070f02449110007089280213004484882d240c3e080903034a034044500a8800311004006c0e0072001c2c580c18903803011954107004800f8200880f5035003000681464080100341c500084803070424001c1e80360082e00008220a280058422180602a880d07030b83c0440c40400e91800f20a400c0403c0040054681c3c04161140d4103c090300502c06d100711808a802d92070b141c6018415840300030350550000c070141c0b0304044e69402030702101c4580e2400500b80400100d003d000e003801c02500300c039000c0002a6562225400d8890314042c15854a40423641 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 747379658 1250 747378408 747378413
    0x9090302030a030f021b06060a0906080d0f1106070203120c1303080a0e03010509151b120a0e1f060b0408070e0901020c030403110310020c100c030623091003 69
    0x341c0c81141031280425441d10040d50007804c07550101d40191021450700c0200e280c0040c08251941000c2c0e0b8030030300c603094408002a80d11654003c3c8020b482e0040064280701090700b00c182c4040d41106038800038401ca00c006034920440c14800c4c10321486c62600a15907401c182c60b042003030004010200c40080c0400d000d601c0030000c1030300c00d02c01a01d51101751035030350701d20064044d92042c4200070310365031560918007041540314001c1030001c60001c4014661110761600754001c0c2c02940c87d04100d01e07882009000503164480d062103800c1c1c00400346000040d01603c0442c809041c515850001c9070039003c4100540501765a47c4200c41c02003144040312401c047c2030000c1c003511880310b4428110000d103070901050b0381030307020350444000c0044a0101c0f591a5070f81e1a0205034495188a01442400b8081100d21114a03900807500d0200340503003d0310004103496144c4000f84100031000b01056584d1401140c00300e4400c2e01400403103c0442c010307841d60016820002c2800c1e000708401046400403008000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 747380908 1250 747379658 747379663
    0xf040b0307150f09061e050d090f05060601050325030b060c0d020c0913140c0a120c05010c0809040507020a050d0302041a0412080f1e0c010510080c010e040e010204060801050a09090302 81
    0xc000e0342c161b00902094040041160381b4015694060403e5152091020801c108140c0981107103120794161402503448000554103404202c50005090400d280e010042c424600c1c01742c0c1d100707402401c00090952424011a02c81e80000301d245c0025800803d030594416010800c81440a40072540032a503480c111481100701031050500421101c680300800308188410310082d5044140640400d0300350b541c80c00b0128507904081401d80b00081c92240101e100d511071442c9558152300580c419140128681c01e11000301001070041007140034000c041000940d0a20020458500d255030250310f45040c217005007420a448a020794039240100810003d054503800b030041c00907008090303691144401406244544644a0348510a1060750250003001e03202030041d00d50f14040318000c101541d1601c4105100d0b01d039601401c0381d964011500c0c40c1007980705201110350140701a0010494a000110302826600650032080c08202018014000c1e402d1801d00b00e402800c0051050046266070384010f034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 747382158 1250 747380908 747380927
    0x61d0c150d0218030a081201091413030e090f160507021806130905010c091d0105130209060c010c080f07050d09020a05030a0f02040e0d020c0f040b0307150f0906 71
    0x603000b070700420103168815015401c251400005010341d5001c0c492032501242c56407040d9000b002c0138155000100d00b03903526100e014609008048803144a841d001000b0030740342c400d55400c500f00040d1986050f00349d00e0ba001e420380158284840b400090500b0510400c44000840002007049820322521001d603481002502d42034000a00ca20101e8640d107021444a071100c1d1500031065062280d8002005015440001d1444440d581c0407003207a103e0003210074240309200d00341c0704406400010b00051418901040c514041d07030000611382032242e008511240c01142041c01940d41d034000903441c0d10381000b8140d52180c0c540240725283d2504c3c0c0c038068018020301c0c0070f0000060381c07042400301b1500c806030014041c1c00d0003400c45200758410700e4041d0008803980303400ca004a0070030480c0c0340c962a0004180010808540290000c1e0a007101408514400300355845e40c4035480e4000a900c81d1800d11885002c1c1592001c03010311240506806041e6910071120a4101b000e0034200301701a5074001c1204 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 747383408 1250 747382158 747382177
    0x10051204151401060c05070905190b01091701050402030111070f030e152a190b04170403120e01080631020a1d1f050f0403061d0c15 58
    0x114000460701507104002d016820801403000080c1c8004070b51207801c000d4884440f88030b0b404450f9515224064075058a405840c04550814940c959200c00c21540d00b2004407a9010302d0904456036850802c82c040ca03424400310f6100765510402d21042d03040a000b00e40e856080d00c285686410410360b03500b00c0d02e9802490240030000381c40400c40c86a0382e100c0f01c01e007510003031004140e210b030341c410380b01c043c07440d42d075950035001d10356101d400701222001040789104000c42c3c48090803c105a034a528070940b000900c00c84110b0750600d0030858116a4001800186000301c010811001401001810280b0304081c002d040c0041c2c0c0c4208845030380d91205c40f800c0300300c801025440075054850a06045219903800481e03a60020900040c0c00780c2c405158101c07111200c5581c44010b01d09018041c032004103489a98844428248820189001c1c0703005114014040c0b048074607090b0799844032801c480c485070100003c418103031800340c3e41090030803140c04042400c4801400c640d5041890038407a11506442 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 747384658 1250 747383408 747383423
    0xc0f0301050d08041206060509090f100f0b0406150815100309020102010b0405041b0e010b090607080403051606140315010f0c060510030203150c07030c080904180210051204 76
    0x2c1e001041045400d0703a0090922001000300d5400710302d010005409180101340c01050041c0001c1c41c400f40010b00320f10f0044a8030003503d0302411008a9001a022100503c0344003921014400010340301d038403c007001011010b910342c00340c02c6810b20041c45201d002d408030200e0122804c0c030000e1039a50456801c03111415040000b070004240c40140d02419040018603070061902e000c000900441102d0b1380250f00b07040c811222566205d90131109000020301807000c02260520000e50141010001006241c0c0170b032403458100b90b5290746071458510b1001c00e807070306500e907400c082282c241c0010040040c100c0031016581075181c1800b841060030b0300070b210310341084a108003100c101c17401400560ba40c5900858180f080c0d2508541070703400035000c0c1c4001c0740a0301c50b100462010342001c604450059052050301454616580c80485030603100800c00d03106594208151541603035548030b03414585122864800c01d40445004009210103901814020301c542001304e100e00c11080042140c0c0951300114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 747385908 1250 747384658 747384679
    0x4020307032c010501060c260702030304140a05040e1c11030a0809120a02061321020c04110309120304060b03121207021513061416080c0f030105 64
    0x4a019101c84050041c814003804681e5030071020302000300b00692400402440b2690303a6010446010789450000740c140034846541403a500b03010040030341110030203107105007061388a030002806c40d070003648450004c03c0030295a030030500780a00060300414003140c041014808590010b51141c04601d04041a802104503401440d40207043d03e44542490400b200e031242c0000d100941822419203054600e032180000c2c10784090704036012101080fa469010b05996200c0800d00310000c14100c0c0d00300c81e80d03400c0700c2910454000d070360b12164640f200c55000700342d0b4032054403d1004a03134140c2c90120998000b041000004100080d800344501564941c499523540c031420458002c0c410300340890340c540290501c40040c111228040c0a0198040122160781c2d142c19030240d0340d81d515000300f80c80e010000800224060841d940c000c140030b01542010420507900240209100821666034003d80c00304442480005e41c01b0062540c403500b5504040e01d819015071403540d040c001445500d100c0c40c054030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 747387158 1250 747385908 747385921
    0x6090601090e060d1407180b0609060f07080a030501030b1003120e01020a05012f0301051f11010c022406031b0102120412110102010b010c0204020a110a150608031305040203 76
    0x50081a5558005c0b030411000d020110703450740c03110800d11944d0907407041c541e2900d000d940c1c0e902c150350308044000c00700c5213480b402206100c15500304007074031008404148500000310305400010081210035a400044545c11071a0028030140003410310b00054021010034400030b61541c0c000b000340702c02402d019030348482401c0101c4c40c082440e00c00070803d5092105030790300c0080050424002001e1000c881600740315103500d0038030300e010911460383d00c00300115140180780c49008a1004580351031525414110030b45500c10b0944904680820047c0d00c040158110304006603801c0e002d4000078070340c44030f071428100c0000b44d540d0401442c2c0d00402c40410700344a0181c1c001c10008220601c0030440b00c0e199a03607500c000581d90000d14040d01d43e6040b04a001c1010741c4180315042d0694416181d82120240c25024800290170980d00c0c1030500c4004c4101507854501000f9182c1d19506c5030480d20303110710200c024001030350307070719408110719a0080c443c0800c18401c8896040541d1000d40d001370700da66500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 747388408 1250 747387158 747387169
    0x601090b0f120706231914070b06100207050123210403030606080f1311120303060406090501030b0c0d0b041a01020c092a0d0c120506090601090e06 65
    0x311103550700400030818180450310104802040303030841c4e122800c0c034403100c0040c4451840c1d4081d40e1710b4004c408000e01985182d0180d0340c1d0f8800c4440d864980400300c0560500c0a030b5074440307441035032030400790130410600b49062a40280c41000320f00c081c0051600e008006084405000d0310703a00e061000036a50b04c843d60020099034a1800d000025079441000c030001003102c1d00c4207850980001c1d042c020086000c03030081c850780e80a5140f01280054903a9007074084024941000da00329030b4104944c0e001c00d0305039913008581c44080e11a00c0a1980d034107180c1d0401c400c0b11016400209403604100041000ca902c5044e442d80c4800030140b141d590f450f240440b6001006600c81c3d40d41c1c041c0c6808104a21300d4180c9041a01e001000c2e0210381401d42a0b0041003447d6000303d400b0b146403100358401e202c106400307550080e85c0340220b6002900b044040780548003515464100b4400250301c822940003c014a1700403160064001d4440c65024106280020140115030107603d401402d900007060184e21113 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 747389658 1250 747388408 747388429
    0x60a060518190c1d0301200c010e030307090e0f070e09070c061109120f0709020a0306030203031605071211040902010c0b0f1503010203061309030c0807051f0209030601090b 76
    0x50704030811280c0055840540b12a04061900840590b1641d0112117804d0500c40c0da90007440300c0741e000e038000c8104400c41d401540050304150007952580c03000c030912a8104091030094140e900d48100c02410801d98420000000b006116464008801e0009030b03a0030540b80598002c1c21b6450901da5a2040c6003500c90800e0104000c01d05032a04c0e00800003446900c001d41007c0c0c100b11540581130080495079a95154507a000005030740280404009584a03603008040b1120641004945503a0f650002401c0d0f401070703080c0e41071005099411908002040c81401c015243d284540c00046001c0d403511000c40b550718451034003940e95074a80d0001d5a0080700700442c250382c401f034011101d2408000d140710380340041e501415056183c4590143d6031606001350391043d48041c20b601c403055004500c0702d0103841c5c815010703414001204600e90200344a40010525240100002c05d1500d0692a13040428078001c240301110f04d105011030f086642d0040703105811a540344c41c020070071002000004400000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 747390908 1250 747389658 747389701
    0x8040201170103060c14090a0501080603150109020307020c1e04021303080a1107050a030203030f0a03020408250518180c1306050307080c01140a26040203060a060518 73
    0x4030a00000108181342e0490006800b0780e5641d804425001c0c2102941805901c5140d0b503c00b44980c41071020394407a80078144d01110003000c0394524199480b88100b0384000ba0003249000e034000041203c155010070255031140410303128003001c1052486014802d0300b1f4101c145105503000524500c0403220081400003a50b000007859507120030072000034080c0701c0702c0c1b150341300030740500480007601d450009101001c4940113005035150860344114240c061340804940000e00da42880040b45024080060315042c844820600c40030303000404085882c14104e034099842a041000d40300f940c2076100d1940c6403c615622400319021480b1201c0c181000c9000500c96001100110111040c400d01d81000e8200c41c0c082d81a2400c0380d80341c400c140d40302c51514150728041409449030f030851007030076002030000d4141d91270030344c00c2c40014280c0d004c42c2d042032018064850000c2070900041d490140541d03504040942c00c1000031600d820082640c4110019a240d86000d02c940002c5040300c3e141c819000c81513 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 747392158 1250 747390908 747390947
    0x61815040c090f1a04090b0301140a090c14030307030521040507030b010b03250905100905040f0605150a021c2604051e0309041104080708011a0f06130e010911120708040201 76
    0x40d1900f42c0bd8010449003400761a1000c043c4d00004114038403800c009801403000d0051481e00340303252825a0f00d0350052403445001c00c0d011142c41074000301c000e0a01c0c080d600c2123020b007100078507506000c4104201a008020070840c20000c3c407285010320301c0e8150510b00c103580d040c0c42c00d070006041030b500b905580e0302442e08004804980032032a940640864240c8000311410440352020b080c012044884602134550040c901c1e11502403420581300180007825080c0c4100c601400c40c482d0013a490444584412000c102c0000108001b585610503000c14070854044e0103555250544401e5540e49031070000c05080040ca4440e0030b015901031007283c0b80c40c00c024100784000520002428026405441042c1450040020114107001c060007842c00300140d990200d103203030440d80c0400c4020284030851960040c410000d6004040001008134003c1c00019510755840d854814004259598102c0305807010b2410050344900943c2c0394035040e040021840c100d81603075102e20040c0c8101944480307024449 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 747393408 1250 747392158 747392161
    0x12030f08090309100f11060c0903100504051011040f03050c0a270c030212040f03020606061c1104120516143007090501061403061815040c090f1a04090b030114 70
    0xc4800f14000c09c0013039020303811121001200515a8129070003514028003d030019143c0c0c4c42c0c0c820441d000001007580100c3c8052800f6900d924203442c07001c590340700f11050b03040041d003880749240c501da00c42e005101d941110345414420007080c00c000c0c0e1038080b00c0a0f183c0c0d03440c03480038100741c4281d050b6180002c4142c03504840341018180158805540d01080380148102000a5481d05207602924425201c401e1503408220003404440080d004c0300146020000d0240f000148014001015007442030107000905042e160402590000f078030150085010404d8070b141d9030301640c0382c0d2100e0b000c44061402072000c0000754650006000060a41140454404c0900220720400d165000604032103e42e00e0701160b80113402c0040e800740c00115104c2d907109c01c00a41c880d0b1740c840201c0c0d1296118000c001050b42d07403044035001808407484104840000b403071104040c0700c106220b55030340001e824500d0f030400f8900c1140381001e20302e103e1405140c50194a500748440b00f03403025000181c0300c0001c03141c901d8a6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 747394658 1250 747393408 747393421
    0x40c0e0f0a0c120e0703120302130303030b0f10030504021003050603030f22060801081c120b21010b0108180c0d05030f120a05070903020105030a0902060412030f08090309100f1106 79
    0xc5c1e60b070070b000c10b850a2080c81100c00f0050b010388200c1c0c40e000c1a00c1c811460091940d14240d0051010240c6642c0088035a8414113495407010018209000c158400043c141400d00520220840c140d150905251801060003143e41e000800c1e138004035203c2d8002642c8e10340011b1000700040c480050b407103400d004044040b43c0540c000b04294180d4040300120740c54200c03d003401c51003500e4001e05000100740b0251100b8105030041d005803101810142803030001003007881034107c4144228540001c80c0e55243c800c10074543e407000c07007550040c0100c000701300650066040c0740d86810310400d126100750380c3c002201c0100101403041d1021210642010350311035050020803100608121260200c0c1450200002c80d1180501c0b65002500e4060b91050704581d46da0920030010b0402d1401680d11070400c4c080083d010884a83c2d210203944269a45050304611400141c281200600165119001404030130102e40710782c103000c181d81050b46015103030084a450152800d40d038200e0b10340714501490041051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 747395908 1250 747394658 747394663
    0x606081f0803070f0b0907030209060d031e0f180b030a051e090d030e0609120d060803042d12020103020918040308010501020f1b040207080f12040c0e0f0a0c120e 71
    0x1d16034005c3e03c00c04819600c0e9a106500c0301c1050100035030100148002c51064100840c054036002d100782081c0544880e184409890301c4d42c02c0f1580c400050110304071160551f4000d801c100341d07210b040d604030a01d90500c424034400d800000c051880c0d882ea01c200040c0d1180d100062440b07c14003000c019007150501c8110b5585980d43d0b080000c01003820010404884c0400044171403150100c4009882c5ea03007201100700d00745520105598282a0301c2e10000b01d00c01e842030006100a11384059000070602c2c40021010000040254000b4107480c0114104206c40e40740b902503405690903e8010b94074050080080c0c40c146041302d030b2911b00020201000209034100b600c60b4141d078800d8003120882d40c4072030901a030700c800f8102e62896641c2d000d120070142d03041580240002d148500b0f1803500309148588202c0058000c0b9040b4a00c3d204030105200500030803103001c902606840020101c145050344001c00c05802c0507094240c510f41d00c014150300144200024083c003050b2007024055a03560284203039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 747397158 1250 747395908 747395933
    0x3020a09150f060206072f03190903080f070204020d0f0b040b1e01031509090812010503070e0403050d0b0a15030f020301080a1e1a070e01030606081f080307 69
    0x2000e034901c0d1402003009103200d24010201c40c1d0303d50062085603107544080341c1c1c8840310322881080c22601c01500c1164480341d61003a80110502c2c0c000c4d07440d0100780c0038907d41c95441c0070605003800f40024042c80454100320880d00300c0e806c06186a5621000303032000c50000d109401c0080f40407450010455010345081e00201d0410404a906100c611400001c01600104071011000c00500d070700d84200c440d5019412001289045038580f1402503070326041d490540b2441a001c5802c100c0001c2c941c2078480006000c2405443e00b9801814420704010004200d00805031020b8148000850150301c0c5c81c4098008800546002d44103808056554201040b4101d4811500d004030f401c2400d00c0060745c01501c2524100e03140d6400508001c0400e480c1d030310001101120090341003000c490007a0100e001c2c000c0810680788600c420076402d1410a400074041e000d101184c604050820320100101c9500c0341c4a02d4101d08111800d000c6426240841e861407801503001c6280e80c0008070300d00040c07102560105 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 747398408 1250 747397158 747397181
    0xf09153a11030d0c021905010801050f0102030403080f0301150c0c0b0309030c0a0311010c0305040c17030d090b0402010908010e1213030f0f110d030c0809011101051f170a060207020a03020a09 84
    0x20306c030f02111501658505500d8040d80340001ca40c00700420161400d0907040442d0101030069928240d241e45600788240d0200d10300030b00d44100000100b0045801c004510700385c03122031501e014610019514010309004a1091083c2c1c8440800404d00705e500c00d000b201c0b000322a9200b00d034030004140c07034081d02e0391020b001c0d456103552812a200308814040d0003907038859607000e052001003504124075504041010002c1b5081c034401480b102e412003115110b07031301d40705004603801c3c000da1901c1c2c4001402d07920290071407491a414041d64007260b0b400016001c440f1440e40d004140c5a07009036402c3d0b66014080d6201815148031b0221110600000080040034180541c0c800284258507000340007904404050040c000b0f291500c10101086104010f0301c12900145031800850580d02c0d105820340b00c080e10044e41c0030034000040703810942007c03020380051404042202e810f07403c0d204040c1d102c141d040d40180c0349a030006108400c545e00c44034148007969005141404035611046804020604403007903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 747399658 1250 747398408 747398419
    0x2180607080d0f0e06132303190c0f0f0b0a0911010806060910050d060512030d052502010c0305060f1008060402040b0f0301090c1d0409020f09153a11030d0c02 70
    0x9003144947d512015050b00100380c1d0003545000c242c01002d03104941102c400804101e401c0c0c01e0701001811600c0c40101070b50143d02c2c1e01e25800140d04100350b1501c0d01802e9130f400540f51581941c0000e04070240000c6160003401c09103915070320f0001042e02445240b500036400b000d071681e40b080081e00700d405400740d03c2c061142001503d4403a401d110401c1c00301048800c2c950310a00ca00d02c00c5c10880e0f0000c5603c103020203810205044450800819503101c00e4006000d40d44501d510105d10b03a051080d1035200c0001c481e030380b601c0b006200100d000d030206000c0c0107082015290009180707490756011070380144106121a55140071000c0385c000035400070b010b00300510b03080184940c000340c413807010310221481ca07d9030409004c40142c2080300400044c10100d801c4010b00414509583c2c49420907403280380c20400c03241300101c120301000a00c400480c11410403140c2010503143e58500c4100c41340c000000281403222842441c24214480d840c1c210059a1610400307107241c8400380d1009200341c2c0341e4425640c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 747400908 1250 747399658 747399683
    0x1b030f0408071502151f1706100b091e060c06060316031718030d050406030612150c020a050703030207060f0e0d03180e040602180607080d0f0e0613 65
    0x402890100709840602c0c0141d01844ca10074007400c6a940a503001711b80b00c46000d00c8403071000008412011036a0001c1520000b54503486240141400b00a81c0507610001c3e035070a05003440c1445005010720030f480d42c059000300b0100640c59083e10507040b02c801000381666112030381d04c80e0306583c8450407140e080c00703802001035a0048141c43c8404400392036020010800c0c088081c140303440039400c903840e1001c180d83c8890b01c105142d14103002c0a45187d81e240ea416aa0b1824894064103662182d402482007039410340740c0c04081403241c0140300f2008181000490100000c1c0fa040703142540540001e40140100c1c40004105500003d010084519903140c0c9280c0841451040e114003074402203450300701e1480d005460009118054040100c4502d100900845455003000d1b41100000c450884140b503001a4002a00f16214000d0f44155401c8904918020440c0d4542206008100c024011240c8074589500b0415594000007494041d140841d80303503140069a0b041e4490b6a02d20584800003882c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 747402158 1250 747400908 747400919
    0x30702030f0a03170c1909080f0a030e0904020d020a060f083904091e0b04060503030f1305040203160905150a050d110c0a050615151b030f040807 64
    0x3a800a0b9903406854488098503248800b95407024001d00c201401d003020011000e59214101d03400e030f039a200941d81c03e880f0604049a0354079080b00340541344815800140c400b8000b0740d20482c8170404c44403e0ba0150f103991514408540c81c20031004000390300001621020034401d52040260b848103080d41c1d00e00240361180c0c44200c2040d1500122240400c0702582d0142d1070b02c8000d00c1c4001e24009a078075151600b5502c082d0b1208031400d0000720b16643c146409001000d800b00c1c018548998412141005503624010000e6500d118100440d403072074001180f034000e99540c0d03100b90801804007130010355407480d01c4103203424070014030139441c0003250b400c0780041464206041001c0300c16400600c060300e0401e0b24001a40c80750400c00301001c000d42c445d404881281d0504c405001508000c00c020110701e8402d103020383c1446d1004044002029040e8807007a81d40c2d841410883c00c924590031010f65070000400f0100c43d903c03544001005a21000440070192600c0e800104211607100e41520b600300e4640c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 747403408 1250 747402158 747402163
    0x7051c03060f051011010c030e060f0108210702030a03030c080f040b0105133b0c030a1101051317010b0411070605072105010905010501050306011d0102030f030405030702030f 77
    0xa00030b01541011041050105080110883e154103d03075090203022200f00c1040d090a403151070b0340c0c08000a441d05000304564000f0030099410140da41c660441300d40c14140d4050b9601c80030340076440ea82d900c281d200d0800d4910141107401058021742980d10180607070401030040c0440350702440c00581d0200c0050100d402110341540100c0e803220030181d0300d03442c0008020390b01202002c40803660380d07034007524030002d00c0002c1c0032402183d112180b14a82901c5031080e00350181e945104151b603821080203c2c15030b550108030000715990059038022114498030040341c840c028400c448068822140010443d4003040c00c01d00756410151009002c00d107000000e210603501e0300101e40c120080e040c40848005403441e0850340d0b01403094070303040034489100340404e039040300d400001210584d0b0783d4005011011480c000c290142c0b0080c2070480c9107040000c00200800c80a070002088080006103040d1143c0c13081c02121000a2211400346c0c40e81081d0820580b00c1c0e0003024124030030f03c6120350266040300003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 747404658 1250 747403408 747403421
    0xd0c031110020d0801031101030f140906060d0b070c0c08013603020604022106040b0f071d0907050f04030c050307092307140f18220e07030807051c03 66
    0x4a80d01c84d0300992a640d075801031031040c100c000381455100c200041c1181e42d184101018010b0804501c00c10303080481c04e460402c3ca016140d240105490080e210101c4e01000d00160040da003841d20882d20b80403070030481d007501c1c25034100200c5542014200d031496451035200c01c0158410b81102c1c48403e0b003050000c850380c51840001130140c0c106c50000380151400c03603200340807140c502d00410020f01d04c99440c84e007401e8048a049910821513003d10401c0d01d180300b6840da00c05010f003007060450b42c5080580c043d130403161103100d1107402a500041e03c1c162040c4d09499604105140c4503031107980700d250180e51030f04103000382c50182c440c00c5000900704000d400b4021514103404c00455002144010050410200030300000500c46400542ca014400d030900a005051102900f40d440d1003030410880c10601058648610070507224448030000c1c944000a942e042e151140002072a0284900031801d2a40340d50000d4201ea03404241501030181c00714180003400412100c1145100800c141038040b80d03072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 747405908 1250 747404658 747404683
    0x1204060902270c0a0e0405061206040b01030b010b0a120c0e0a0b0903010f0c0c021212070308061c0b1501090e090d0807030905030901050d14090d020d0309020f01030b0d0c03111002 79
    0x20403404145003401c06d0707441150001c0d0003806001c504282c03a0003852a00c401a0740c00c5540c071455200410a0200c010805400360000ea0100e5241a00d145002030a0a2556100034446581e4402c400e640300d004010305e016109010341403803113581e690703a02040150442101e0314001d50804004c94200b01c528410010041c0ea10f4035000340956554003800542c5815049440180c855008420340d2011040302822029100ba9503002e0103290440c117200b601201c03246088246200b6a401c0301c006000e2991499010840d007200764800001d9500490760945c1581c0040c4600c03190806100c04142c000c2100681806141c80b0a040c684038141c0440c1112507216014090350010321000c0407543c42080140700f0380784000408545803001812060294105950061281d03220004448009406010640455580303080410031018541c010400303600c00101c1d40380c100365a80036a0882c56484880c0410040c0e0040e03006603030b10b6102d150054518060512030341c410741c030320f05032105030b54800541c00d071b445070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 747407158 1250 747405908 747405917
    0x903072601091214040315050402151e0c21072924040c0207031713050405060103060b0a050703020c100c0b0901060b130504050705030c1204060902270c0a 68
    0x40f180f40c0200c50001e001c84102c10052401c000c000082603a00c40000503032003070300b180001d4606061041280318030782c110b81201d6030036003807090b0505800e204015040310310310403178101c1c1c0d40c40030400d2080c20302540d01d411080104040f1464a449100c074000741801d588204c030f400c1714007940080302c0c030312038400c0c454031011044240001a43e44101803054028540b800c070303070103c0e100003035a00041c2034901c17010000c8010707031200008000b40000c2c003a08603240030200030400e00c1d0441c1d0350b000b03001c800301a028031409591100f0100e60564400e40c04080189508448191a2443e50300c00914035480300e1003d900503c65803c8424462070311700403180da0138444d40c0b0703140d0244503607507214000c50758020104006956075042c0015503136a80f41c000c2c01c4043c1d081400c50307074141c1041c040004030340c405403642c001c0020034010000070583c000215800c4004c1c480043c41c640c2d940e46080805043e00d90802500040a4004560031a51240304a40c842c20340c0d0315004c4060b079400c1441d01c8a400f86035458030004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 747408408 1250 747407158 747407183
    0x501170106151206030f08190f051b10020a09090b0414070f09031502040810050402060714010f021612032f070602070308160216050105030a02090307260109 69
    0x12401030020020803e03d140700410b42940d0b9880e910701400c00054107542e000c100140b40d0541007180c004048081203103003000381d841c2e4003403a8020900d000d011a0b48030b000c0c4d04400e00c824544401c200740343d01054004825503944400140081904002e8829110b4882c10b000300300d5040c2c03400b8080c52848041c0151002c10759581c2000c00c46908901c00c401e40144500204e010000c00c00e2a142400745a07402c03a000740c1c2c0c440ca043c0009140501c4000084900e92916040c080185e40708000c45644a41140078191b54166482d1014010031369454020000e500c002190703002040f80e103105446440c01404220f00400b8605000d13010307a01d01d1740b4904000c1440d109905081c0b8801c140000e4041c0c4815600c0d0304080d101d982e40d000300d80c0403007000e80c003044481007040800c20362840800440351480c030103813400000300b8400e40995a0940100c0d41071080c080005078401003994190f85034510002d0454414030341d507041c05052070301036202100311a2003101d020001950305004000805500548003c0f04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 747409658 1250 747408408 747408449
    0x906080d051c1a040507031a04050108120a050f0a0c03090b1c110705060a020702030105090d080403031a031515060f09060306120604050c1c150e19060501170106 71
    0x20441000f983c809001d141d00d003620a6103892251511079011610b0008905d24040610b022600060340442e108500340340061100000c041014640c0c0000b000003c0c0e00c07141810303006c0e102402aa240103603004c8011604e0549294040c1c810301441d4000e84a080c90280c403006414210b10641494066090074040402c071075044a43c45004d18081c2205c00504119207540c925007020002c0d900520701940100381d02042d403500b0f1040303d8011039584010f01040000380300c0500781c0c1707100400150038540d4940c52041d000741120400c460565009041d5034404c090600b489410b0070f800c0c0c884420710444802006101d0030315800701c611110400c5516030800e51000c0400c0511780c4010300c1c02c0e802900d46014100540700400c041400f840c8901c014105003039158091211025151075a0740403c401001d011313000c15249801540c4a411402d0301165440c4000c100c0307840c2c1841031914100c40184030507840140061a440f0506950b4a150b1004c0b040380180101030a0360780034055920340e00c014117050f442 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 747410908 1250 747409658 747409661
    0x3020901020d39050601080706080f13020a24030204120f02030a1a07080a0c0c02010309141e0601080c0604180605060415021e0d0e0d0c0906080d051c 66
    0xe045151260b800c2c01400303044460400f07042c03c052400a0042c220700c0d03c03c211080c000305014200080041c269107207403403c0280241c50103071601024111500129005100c490894910385401030500d5038015591000945002c8242c5000d00b00241c4a0302281d00c040c0c441d00803941265802180301d2240c041e01d44031401c400b801c070390301240c1c03500c50a01d100c00080c0680400000e4000c0d112080d4081d440d0100c0082c0c0301a60003844520101d1401c507a50300c5298100740b0906000d41c0a1030002810070051074826040d0542000300704552180c49104e04548050506100c2000c44c1c440c141c4101d80d90702c840c500c0c6d81e00180d8045552011040c44180886000c01103010071125403d1400302d0a25500c0000c901158030542003807040124100c20f40100580400c481c0a42c070180b4907011040f484014a4240c681c590050700300b080058011806500d0f035603203c0c117201c2094005000c818120390340d10000000380704d03d200780881c600038003505121007401002580c0744907443c2a5450390040000d1030890 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 747412158 1250 747410908 747410927
    0x605061b0309100201060e150916113f04140d06020406050d0501050d11010e041121011706060f12030c061b1e030c041502071503020901020d 62
    0x80c0d440c030003070140da2001d50354140b0102882201ea0000190b20341080751a8039030190062402c0e44000524440310050303280c422005074882108051314030054040301c0e040340c03424405884100340b40700c0c00d2200142229240c0409103968050b0b510450302c1000000c05030300382089216071801d02401400b04100124a410720980e41c0c10004101c0380c9206840d039103030001c03a0080d40000c40024004a4911001203051048a002d0034040300c14070310350702c45035541d04200d04a0f50443e90422100c900c0c1030396680c0f84ca07048a40462201080d03551160060200d4809140452288603407080c18a00000380c46c89454506041b001c20000181c5615910381c01031240e150340003c2460f810a84801840042846c140003600c480a50003015041d20300344449602e160401300010080718400070050305000d000743c80300c0314040050321000d240c0c070f80c0d994558501903401203501a41d5900e0705aa01c2020007540410000140c46140700c480c03085624102c4210200c0c01181d140902585c4800c41c070b40d001070b010320340b03e0303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 747413408 1250 747412158 747412207
    0xe070f0e1f081015050402090d260708090a09021c1e0212150109230414040305030910050402100509041506090611161205030403051c0e04060506 64
    0x2562003680c480e50b0502d0500f45584580989071394051a008064585041400034034040314190300704030341d090020b41d0468200d0b800510f01034511108007082810110510141c20078014500d4070b4081e18140301e500c03540705000c594864005070741c000c503030401c5a2082e14800380300383d12801d001d148682d00210091110150003810540007400a0105008a000401141560140c0707944039081401d03035100041006c100803030520202c00b1051003518542c070820700440c20a981d0005c0c002546501040040c1034080c2c03540f07891549001048181a0480000d5004d10042412515840c03040c0b40c10b4412240c007681c00035840718110102100c0244208050700215200602c0000c1d900781c08010301d0004020740d445040031a440b090100700c8244c0100c01441c1480381c0130054415001142c840c0308201506001d00c1c60046151030503401440310400030f41e005140c0c400b04596010342200140c681195810010400081e40203070403c146e070034240288000c58001601050600e260302050201544c8410f03103c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 747414658 1250 747413408 747413461
    0x12040f080d02031005010e0f01023a0c03090b0f0a08041a01030507140103050103051c23030f1503070302090c160803010501030c091a1e030a0e070f0e 66
    0x7007440c825440c402903025010b030400074084180f0b0b001c0003401c1d00801c2100203100e425800c643e90043d0743c004c542c00854a514185405810b0010201e456100c4080740e407243d140d09182c600c01307001c640c0109001700440d019031241c4a10507551032a810132441b60b02e240c02e48030f0b0418044001564094003140760820304c103540d0118512901c1da01d041c44003501340d205682c07a03401400100100024000e004080c21003c0c42d0a110070342c156161240d403415401c040025511740c04c4003035428940310360740884150b42814002c0c1041c6801034a030f600c4580040d00d0204142440c200840c2e07044050302c1e94503040c1c0c4ad02401410300136103160204014018028207100c0140c0702001140e1296940e803044240d82c9204030041500c2e54100400141106c0c00586a0070920881890501504080e892030172a01a0001c0b0180e41c0c89100040200d010300d464400f00310216400300c18003100003181d0b004025a14600400c840300c2540d600b883e0300009203607104214609550402064071030703c0620102080d88825010b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 747415908 1250 747414658 747414667
    0x70602030403062d0b0907020f03180a0f0803120a180b2503140619031707080d0e1506012703021807020d09060516230d08060612040f08 60
    0x540103a01c40500444035141076a4140405c15840e000e4036841e000000ea00c001c0844aa84029155492190030350000221911462800040d580d540021000d010b241c100e6050b000c2d0386080069076a002002c0c510309080810000500d01c40700c034032402142400507086210006e40984a009000601820040000f00c1c00a48803070186460100c0007004101c0c2d41e0005445c0c030050780141d55840010700124455051185550040c42840c4003ea05481c2c00203280c4032084194582800c2d00e1145030002804540042100e00b405089039201d105900120015100205000f40244c01090b60490720240400c0d4075050305180e0507400d0401d1118509584991240140c594002940740c04030041c000080c5114031040055681e03042c0540501d0310202d05091010506141014000340500070030741100081c0560540c0a012003511142c2010740b581c00c4c50600e00014440503502c1c0d0841c201d40b4000700c1e030813501240701c608100c405c071040281101003000e00350b20f8680d83c28810860268050761044400e12 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 747417158 1250 747415908 747415961
    0xe060d0b01030905160e010b04050904170c0601030f0b0a141306020d060308091503010609050d03030f140907060203130603090212010501090603020a120b060f01180305070603050907060203040306 86
    0x1181c170300c007400040400a02d1900c1d055407403400ea80160880c111180c0188001c200341d0325060305840d0456800014500103001400c040c180034040c0908034011440781000020030301c94010001c4c40514056260340e540c50703803182024810b603203a0408601b107902222000400c0401c0001c500c1403111b100d02c03400b500e0480301c2003071401030b2949508190303400100003420951a1800700810148030800310700103403c543c90800003510011103441203500a01c0488001c00801d440303079100c1c0300f81e9034184808110042c298644040241c604640b01245442049000700c0c000c0c0c000810341ea8110120720418403800d040500840251078005d01c1281c120303841280000704c1500a01405003c0c1a00f12000604a80741d4010011501078540c0b0508180c0286c62480011482c805c0c4229170240c0c042d00c040100240c04d0f4012a07055078070070180c0f403010036203140200800c0400328041084404540e82402103440700a003140e12100700f441040007680c0f080000708001211344d00720003a9a03001581002c08c103021700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 747418408 1250 747417158 747417163
    0x150f03120d0b1f080609060a09051311010903170703020f1c09050616061a1314070e01021e2e050f07120e010b030f0f010c0e060d0b01030905 62
    0x10241880640c03601c03a001c40b141802034a100c81c032220100b20b52400c0743d035044050074a050240a0074041e9103803400042e1a901c0301c402d01d000a08501c401000b80345051031064085494103101110a071052040d2280703203620a600c000162600040317500c480800d050030360300503a4801c0b032084065004102c02c101912609004034450800d44a106014070041a00001d29019039500034510503401840002d400501400c02c0b1060704c2e070720000001d0116100a940041003042543c0e444c1d01c201f2142c1c000c410003207607812600c901d54142c1c0752005241c0318618107440380864006018016445240790450f901c1c2e10b0000c0a5080d482d6030252070360f1007032003e50385c4034242d40d4694101d41c040c1d441113800c1c1d1200840c40b80f164400308503460302901d8241348000801001905000c01903070754903541e40c0041c103c400e41c4181c0412400900f11402541c000c0b08890721029001c2c21000e640d41382041c0590b100f80507080310b11980b100109064684150250800c00400c40e0700d48403410143c1c1d0303180010028404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 747419658 1250 747418408 747418417
    0x912030406020a15110306010516061503030e030304030b0606210408030117010e0c060a1b031e0201060605070b0403021501170d050405030706030b03030f0706020a030c0305150f0312 80
    0x30340c081c0c50183c0c2a814000380302d6058203c480d2526181058580a08900d8402d40307400c08000d2030525a40c940020030595418041c0c0009400c682c0381942c16110314055401c0d40c41100c0c4240c5400103220301c07040c1090b49138020342c413019180710712820018544d454444004d00003601e2244049400c207400d45502001414215011642d0f20720000060103130548509112032110b20340c0c4002e021009508450740c0c5ca07150580410b80c042c01d404104401020b005a429108251005150b00704040131030070010006007500c9070314070720090340c1041c03203480300d01c10b010b103100380c0b80140c03a45072600ca002c1d0313949984410010802d0b02107000c2c401c840c501100d08811014020b000c6402e0118080109226282c10100c640717204030140b05c4100010840340c1c4012805d2000c540d0345040004aa5400201003070440c8210304444842800008400042004030742c05006000321655040102c200900c0065084500c16152942c03030000b4561000304a187c011a03a01038880060b06459031031a204210900a420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 747420908 1250 747419658 747419669
    0x8070501050613021326010515190b03070c14030c0105040302070923042a0e130305090d02060d0e250e010e070c0c09140c09060f09120304 61
    0x1115801d004031407070314100f09103841499a4046107000d86050508003103040380c0c858880021130051b00c0442104694518146c651079060003880a032400020030204a07083c1c0317441a2150300b00d68880c802c5e00400d0700480c1d094071090340c000d0b40f8548038090140c03034100144e030046a2410345102c165803c4002071018207200c2509800105041c201072070041e00b040d00c0760700000c0d1010324051000401c04401c610316803a1010540b101078041d03e031b80c06e01a24006854117605c0100003c00c142000310120340d0a100c0403140c00c5200c1c0c0d20991100e8000c03841e03070300000202900185c81440010b41a152035403401d80b12074801010285444641400c0100742c0302d1008408109801650040c80740207200800c021f0601610040085001e0031701c1d2000410350310602441e00713100c00701c01c0055015405907a1110409400030307070060304107644000401c0074080f5055898658084c071400314410419200c280c4d400c03140010820380c140407011070807214523001040c2c00e40e40406201940c400a44083c80207001414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 747422158 1250 747420908 747420911
    0x70c0b0d050f0919050106030204060305060f010605120105190f2c271227030703021c0305090607081b12070f03050705070e07110304030c060f0c08070501 68
    0x80880500c004852000300a1015000c059042000400022440300d40f83c0e1001c0b02010402e03020303400e2950040101d9000203400031314285021050050006603a4820034040c518107440785e8940704111070500851010024400b03100380144418131b13000042803c952940115540050358032000b803e4540402e078452110300c002c5104040108030040c0e414082c100407c6920f8030242000c00e4606021036200c0e24044e0303c4408004550440842440041408281c91101c0f079150700320f10040440040604105920010390324007052010708002c1003100480e600100015040321441c06032059521106004504100c020401d6180c1680c0c6d03100500969802002602c0c1c840d84c400340090f09205c4101c0f85076940b98890790700c1a90701c1c21900211041c0c01d5000455581c4662549003d80c0c0c64050039400502d00e0007107940c00b09202404448003403281d12640e07203030403851448034001c0ea22840b44c1c0c0006441e05550390024401d4030301a84011024184915183d1401d00d0141c031540c4640e00021000c8070680d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 747423408 1250 747422158 747422167
    0x702150a020a09050307030c14190303021b0102010e0d1805040f09060c080103150902060706140f0705210702032520030c041d0102070b0405070b070309090e03070c0b 73
    0xe03603c14601c801a003825002800d41c541551550038a41e0701d248a01d40301e0f0350391032044e105030351074000000d44040342c1d280750000020348030b1401945407051150309107002c07507a18850417007a610501607226071031001030160140c8101040c0444010300c040c0e81707114003c54014800181c40c2c50754881e800d81e200d115000001d6031482403500900f550600704e01c901c1001103034001400421295110361071110901c64001407070402e24030100d05140982c00019003542d24041e400341c1d01410400c0c81910035058102c1d0000d0039903c02009440a01640e07003562a03d4080c1e040c000946001c5400031508031300e03103004403410b04444100700200380310080e21494111903030602180421200c0c8403112071020040448012034403403179020a82c1c6c5c00005071306905c030301c0e200c007106041c0c00a40491740391160a0340009642e1110181084200028140e41c01c035514401c062001076204080820b40e03070540e90603500c0c440443e00e00403400015000c01d40112501d0f000800550001a00000803100200382000c00703903489 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 747424658 1250 747423408 747423427
    0x40f0e0f060a06060305070f0c1106180901050102010e0a02010c0c170f01050c04050616061d070e0906131b05030604150b0109050f040f0605100519110c01080702150a02 74
    0x783c0e00d440d88008185401e040c00d001c0841d80000603091005c1c43c600e00f131050f01804c1d003014100705034401003440e003008001031201016408000c1d0200c4415050720501d2503660b070362004a003216000000501150041d100000040d0311840100845d1400b4100302200151a072258185c84040c8030030440c01d541c812106044901428040c10354000c0d010880c0d103041601d032901240b100d11030100054100b4080c00010001c01480f030f44058140340b00000e90102c1500e00c2c42840d60350780c003d1702500380d0740990305000840c4c4110008000e886521808149021908980c0d0f0b030320032000c9150725042d6000e900c3d503004100c9480403c102032080f8014200d1040b50020318003284101c500c0c400d0081d0401082d102d080c411030729010300811109000f9500042c00d0f40b4800e0b811401002a60400c0c0d501c002c3c980d03500e600c029800780c003500e40714030140105030355801d60030b005490240c009002005680c0040003807510641c01220510ba0001840c01913402080c41803042400203041101c9130a0440e6002c01c0701c01c038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 747425908 1250 747424658 747424661
    0xc160801020909010f0f05090415050c09040f02090d1118130201030b060307091422050402150325032703080106050f180a0305070308030f160e040f0e0f060a 69
    0x10320305c41c024a60380300e080407604d441c0c40c50740c1d004030b5005411100124003001a0248010080e4910a00422550074010000c0d4040e502140f4454400c6043c040590080354042c8200c62881d04000c1c0400c1d0502515a07610f825802e0116080e5802210b0098002044113105c00c0944250314020010701020702510015040743d02c80703403105020314001d00c100f0141542101c0c1c000c0c02d80f528203081032091804040058180511045c04400c06005080d15003407180250708002d010324800c0f5040d480d912088807079284140000c84a0800200d2042085480703250850661103c821040c90701003104600b90034070460280c51846007806140110410030705055000080c1d601402c00c0d45083c602d0001c80300d00344201e80c06807136015181c4076007000c000c48065440f0b00722500103607404801e40d49560365904281d2066003040701e4951202e2124000508110500c030f000d001030380a1a12128400c02d172680c2031000900405049104d4a5582e642c0b4042c506410482c00f000c0c19030714001841c00789401e015100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 747427158 1250 747425908 747425911
    0xf142b060e0d080402010e0f120316060f0203040f0609031b0506072a060e07120c1a0a090b36210a08030c040e010b07110904080d020c160801020909 65
    0x30045440f060100507a80b01102d0a000a000c64000310b040040380c0001d101415010051502807100241905c119000320401143c070714020502006400c3c480c000038000d905c0704407401016544441d13110300000e080b690003451118000c0c80c0400d4500750030010100036540f80e6009483d15032000c4c04120f4401d0340450150030903c6109040c0078420111400c000c100d20102100800c825140c48080c40e98000c01c04c20b1200a007516106200154801d08004a64215034055508401c11015485c0c0000c48802e040360b03410f1881e6a14401c2052612507445940e4101d4030500f00c122548100003904081031208090700140403410020414104208010861800400c10301180c0c05200707010880e800c0124001c03c0d0b840d00210629925940c2c5006c000e85807180350003c180144660001082c2c8035400c0000d0b10603c0d1003441c2d9012040c015000f0400d400c0070443c3c0c0142518410007400a43d40250303000303004507108090440f0100d1200c00114948100b02c3d402459003a135010515062500c1c00d5146076 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 747428408 1250 747427158 747427183
    0x106090b10020106031e14030d02130f0b070b06010201380a0b070b07050c032209050f01230915041407080c0a05070b130c0f142b060e 59
    0x4c202c0b140c0f450b40d60102c0314041c0108070b41010415401203003881000505d600c4092469000d90313640d040756115030b80094014040388500200c4601c408180550030051000c1551002c1d4104c0303003000001e6441510003240102101d045540302d8045010a505059840c950154041d04030700041c40309800300101e040180c248240b08041240c0c0800c5400341010445034640d400c884000030f50741c1c8852040d00c0c18405c1941e0700d0b00c1d5220000d000e1400042e40411101026101d081c1c04a5050361881844203541c2c0c241c5040e82c103060312000410180c0c0b02c50303107000d400a20040321014030346502c0c00060780f802402c44150b807010311032001c152080d25240c890310203103049160307100e50541003840d40207200c2103008205c00303800c44000901c81d41c0240524161818564400704c014050710b03041c0c5c030921098603024411030b030400d40c050000c0360961403824081c060b1100c0d804aa10040422003c100710002d840d0314030300d00d080c00700780e148810f2010400c000c030650f405421302061007010448828544043e480c101d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 747429658 1250 747428408 747428411
    0x1d0303181c120506030c09040b0103051e0c240f0417030c03030c0307120c020a030216060e2103191803030504050603150405090c03160608070c0507080106090b100201 73
    0x30715082500400e6503841c0000000307000980d030361040042440c0c02050810a50311000315810402002030006080b0f0681c1d11031410740d5100501c80c8800c2c02514500507194029400c000041c007130605040301c90070b02c640d00e01c600c1d0a18510416555008079403000d030918000d864002000d0150b49102d0300040d0300e4100c10402980b4041c014240382d512800040e12529071108004007240b10705104004c0768880140420781006404032440300690380d109554022009800b685203050b000307483c4c00c0c008104a8100c1d45550034100c030b4110030400741610908901c1d841203822000100140f03410806810950072600844a4604078002c2c00342c0f07880c0c1500d40424401440640520010394040d01380c50442d98180c0e8001e0b141c2d01c486c04026070220b40b90b42038942240c0f50104110494000081410886101b901510040d840e40da80c040d000c890280180c50109418101192106215411840302c2d0f81c083d00c2503408060302ca20001d400e4940075800200816160110740c2c3c01442e2103500d16640d541207000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 747430908 1250 747429658 747429703
    0x14060d0b090a060f0609111615060503030d020c0c1e0f150406020d09091a060309010b0301090503031e010e13050a051c030507020318040e010908070819020a0b04061d030318 76
    0x80340f982e407840704c0340c00922006e130420410100c0d0305580c00550103003000404dd84c0c0c44001440455000790490380920109114080a20301141400c00c101d660580030303206031021155001080c0000c41a0600c01290441007000d08400c25215590140015003400c1d0f01602a02c1001d1310010400c01d081d4008000c114680216074080306440c6098005080c4c1c140c5034282c0703035900c003108580105040c2101c0794045d42003070750703810403c000440114030507460a02c15011001c0858000c01c641282405500006a224400700b20ac548019002c0380d401ca226404481d8020401e6031440e0818200a8020740300f403550848180406400d070040319803000300c6100075424246009040c64010002060160040340e882106080103442900140c0031650030864032541c0f0001c0d80380c000c00503807040404130b00299200d1544038003180701042c8a06203640011141c520781c1c944ad100c10000380403076100c2860a18607d20241e10501d8180055481a2104c01c10351070115a10404c5606003008a0a03002c622240d02c1e6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 747432158 1250 747430908 747430927
    0x5190f120524040b0403110a0c1707050310090f150c0e06090d12120e03030a06080a02030303070305090a060612020307150917011103130614060d0b090a060f060911 72
    0x700c5a41c1d0103608466025410344a504080d1007447c00745c1010b14090140280070b005201803011000c044030640300041e2050907210304074503294201c0e0f0085c0c81e071582000c40c0760509a55143c21405003030340514007080d182180c0395500b0101c0098003901107101629042d020b040303a50401d5086100307240c103407031107460300c0c8803640098001821504020400b08420314070442c078611540b00c8a122006d2110200414070841d0315590703590700104c0c0c038003810a040020100b080d070000304000c120140d02800450458580080079070143c00c0c01007403136110381300b40040240030900741d004c2c0d480140706500c41c50800d1401401810305014440d004003000302589000101d07803643c04071010040701d07146002c0100c4202c20714205030241981c079a40080c1c0e44408418021800c00c3d4440c20941c451041404001410012006d09000b02084502d40e91000b000040e00b800b240d82c200d80c13180d0001e00001550b04800c45a0360f00000c603884003d21010940d920700080c0060801d612900f080525a001402d04103041d4a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 747433408 1250 747432158 747432223
    0x3020703110f0a05060a0228050c040e061b0909010308090910060203031302030114010b0a02061807061b120e03010c020105040206030406020a1707020a03120507020705190f1205 78
    0x7440b803980174050004815050034802d000c05d191070507a2400c1c540341c0d031407044000c0307001055010040d038080c000e40002d080340d442c051060a00345040c400c050700c0e01d5a200c040500e2046004200f480c400407040007446400da552a50b500d0186215003205a207408550040c800c3c040c41c010030840c5441223101c1d00b032210300c0d000820f5a9100c2c1c05031004080031821407010901400843c189484142e031507000100d184d019100c098681036086508503081a518242045c0da00085807440e52044d420010003400f0300c0b880f4100c2511a00c1c0351404164502d410f0b5a20210103c0a0b060340800050b801c0c00c000c202d624082c018178040820920080c440c17420300e500003522510003d0002408541d00240403581d16002e40760000503070b4098183c40425203000304000c0e40b282c01e1024201c00152510703600340000c01d207510595000d851154001e0500c3d40c24001404441804841000c1c05c00700c85c3c407000200f8404800c039001c0a084102c0c02050020f440749444c83c6070000e000035941e500c51b4099040a00e03203104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 747434658 1250 747433408 747433429
    0xa240f2301210f020301030f050c010906140306040e030a020a063b120304080702011812150609110909060315040602031003020405180c0306241c03020703110f 70
    0x200380540072403000a03240b03a0010034030303004840c0c00b580c000310001007405401c0101d049141d000d80142c40395a16001c00450b2481210301070310021685903040c99984200c01e0022b141e1011000d040000c1c1d950404e0807a03450f58001d10054130059001e44448020040350303002d0031011384405010075001043e492600301c086c4540b8501002418481300c014170019004002c0390364800d60080f030b0580d4038203160600d404168480b42060380814032001900c40e5403662118400304490865085c0000c035402079a07002c0020f1207075103820103101c1d03e4850108018200380b05614549040c10b88295031411070006003c4180c00082000348241c10044240038500d880b0340700183d029611040040c1c0c2c940d03540c0e14a403c1810141c101030f400524120402c00c0c0381100001740d50586151b84119103007803140c40c0c1010780e1103004641c03501070b80c0502d0207141d00e0707640700c6124035044840003040c0e0143c00340c5400d2480790180c4804801e9005a02c00101007003441100e00b4000c64148013524240d02c0c40f402100401d903c001e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 747435908 1250 747434658 747434687
    0x231005010c050705180106031a060a030207020f0301061226091012060e0906060a270603120c1202011b1b0606090c0e0103140a240f2301 60
    0x403040e000c040000600040011300030080540f801400007240e0728400d40401d0282c1400710341342001d11191000200b1b00c110701c481000300000d24141122a048001c1d4002c0c603804c0f40c1080f94584080d28559003801000060706080e1506c7c80b80c0991400c004580d07110380605200c0d808403d10f5010480c41000040742c0696600b61703504143c0d109024001c583d4001c0c04462042c03054644040403a207141b10820240c0140319240488940f9102d10003001440340451141d1545901003248064000307065422540f050700f0300c124005a150380e2074a607000c0d5a03580405000008841072092400c200b151108c40310904003900c02089902c00d841040001e01c09020703038420034080c04003001e803042c003a0030002d4600aa8010020710640395680a0040901400408000422442804819207511034402d100340700c541c0201c032028035182e02e08030380020060f40300d42d01084402c210000010703413058031445000788001d0284415003172602c4407100c00e02c0784013032040c60b189400004d4003845a9014424900a00c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 747437158 1250 747435908 747435917
    0x3050f01051c081315020d090501120603050a0503030609090d1b081606090c05010f0c020405090a02190519231f0e03010f02030903030112061d0123100501 68
    0x2c1110414aa5404105000500f0300100040750444440c202c01d9100c00c4030a10302481c02c2e980322514083e0380f1f81c005408070400040b84540c04014075031140c426007085808188000031740c29140d4070303994141011103000b030f501640300009101c06400c0061144d40d01c80004006000b00072180303040100504211911020b040580d080d8590034051880215108004a00000c0003000a00d07e0300300003a24401c101503c0c2c14400c0c03640014603500905000e40c002c82e09603034402404016908010044c080504800c905100321304011006031911801d07000000543e403600c0360084d12709002c004a140c00250715241e1101001020002203240000c00d481c3d040c4040c002200340b401010101d40f51480901800c80e504610500c41c00ba0346030082c1c0b9100c0c094100342c00074001050035241c0301d406e038481030707421107400c1d401080108502d840c0340c0401d09129110b40d9000c00d03030106c2124540403203484129a040035954a10400003d40000e403008010030301021310358403081c0707098001203d8682540c4201410300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 747438408 1250 747437158 747437179
    0x10e06030705090405060604050a051b0c01020c120705011109061207031e150f0303230d1104240f0c050307021306080f01090b130201051603080702010c03050f0105 72
    0x180d606110010107032034003400030710b802e190070304000360707a8007003074840703902491912011800b1400c050064600c0741d004008001c3d021074802401c40303102e600c1188031755001d550a0040c088041d00501200034481c444040031a202c034000d080036400c45000000344040d100040241010303944078441610300324000315002001070799400001b074000d40b0703400b910080982c0348000321005400d810b81c0065020080300100840964580d1141c0071150161300018000c2183c25880d040d0480c6030304c507178558a4012100c0c85040584c1c003816001a00d030b030200c06408594010400f440b83c008c02d10f4070800c04480884030144020050314000d0000f00c4c410003034001300001c1c0401c4030203120f0700b0001c0b0b6103019400341600042d00c03000040300307000f8103090281c3d644d0750184040c00680c0010500070040b0260300901022203135281c421408410100058040b418070106020154130854810102c0411600a440380d000c07034940807000038211040c0207040d401380742c6000c0c140710b4412410546d15065440584064400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 747439658 1250 747438408 747438421
    0x3080904090b0702010e070f0e06150d0504030203090405060321090103020405030a0c090605240a0e0303130608130803040b0903070803040c0f06260403030b0d0c050f030f0303010e 79
    0x9080c0302040030384100500b9043c0300002c0c0d81580020002004141a42c0e492078603820120001c0c070705440b420200040c1240442d20354070340a0381d1004515007100c07459150000c0595080c060f150300f10b80540241c1c201141d407880da41040d014a90b40080210043c10300c5809094418101c8132115114000c040b201046109169003c0d50445015200050860301144040d140035110510507021750710809040c020005030605000a401986220f1005501c0d40c060b001c1c0208449500940780700000c00ca45900c21071603648060000706a030081000d00c00140c5414184082c00504c0b01401c08041c641c1c84d01260000324070140d040d04e0304603601c0a1f407000c0540b5854682840d40c011028007924460001083c03008005116007418211130402d0009898541d455000340d03503801d4082900380214419840607018004440c0407280d0083c8039007000184031966201081c00d110a8030300031900c00811040030300a0785000311112110070400c0f40100070551030311400382d80303e000c113202d0881c3d0011008042502c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 747440908 1250 747439658 747439661
    0x804060b030f1b040f020c100b2b060b1e091f0806070809060c070b1b0d021206060412030f030209090c040e1e161107080303091e0703080904 62
    0x210031140c00301d84070202600c01c000060a0f840c44100d01c203a1500c842c4024507901802680c180540c1e4a005c1c19030a006150000d02501c55100d0040d0b10004510b1048120b15124044180030742c0a6641c44854542d42c0c03824000b15010001c24034030403c510b00d059606088040b04004640009561103000f907128161655083d540e030000b100c3c1c00c0322036100045000c100000f581c0e803152009544851071a12900800c60302c0d040f068900030345240c0104800c3c008100e8010a041c0c00c00c07100c0c0f0941031080340400c8620130355041600e01c404030f00d4001400c00c0340e4001030b00e480790b08041c0854800d480e25182c0401803078840010a4003c1c00d0241ea800c03d042c1c0c07a406079064500100024050103070520300390701042850351050041c08948606940401d01c0030700c0841d4241d4030703c0e4040b2140074580d211800c1c0511705514400b520350401c0a4545a58019807091100000030400c0c0c0001f0354682c20600e460b581030040100ca0201c0c46005030304030450800340041c404040302d0308496010755403114940481c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 747442158 1250 747440908 747440923
    0x11102313080d02160e0f13291509090d031e02040e010e0f040c3f02090f0f070509060f0304150506040c12050a0b0d030206091c0804060b03 61
    0x1c50034081d514944150640202d0007603110b101c2d42c190038251603120b000070040103a05a98200030707050001c00007110091103d03000ba400314083c00c010368100c440781c0840100c00b2121024035100f5170042051042d140040058181c840504a926080521b0244074042d52090b40c00c80c001d04154035004800101740341a804403450958216065550359114950b4a441170340c28464002002e404074002107400d50070b491554001c03644046c0c944400c03480c01e88003890b60f04402c21100302d415440c81c101c644182905101350b175140e00f5210a0352200e0304c18010040e152500510000e00c00030340b00200603a240116040302e03404141d50410f00d48030020040450300741e000b035070400004101c0020501082c020305656601ea030022003131041c4001c3d41c5078402e01c010742e05060041c0b000308044480f060b03e41c03503140e045036500c8049008001910016440010034100050340285c000da0050401c0c05614441803042c0282000c542e010086000e80ea0326004000381d000501c0600f0310341c3d460b02d1010580d9010702461 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 747443408 1250 747442158 747442169
    0x406060f030602030415050c091018170d11100c020c040903081f060c020402030c07020603040f12090e01120c030b09161d062202030411102313 63
    0xa258203481c1c1c03402d0700c025032090310192516000200140c0c0c8850950283e10320a4080a160500707000c000d4062042c2e07448404100c5051141302c5250b2100310080c001010010000b0b0f2030f805011541c84003040b03041c444001d0750401000300303070741c402200d890001651500c22190800001000d6001c400d040742018a0940c1b107540c05820000da080505502080d00c40c018100002d01e103e111400059100e0000003500c103403000b003034940102802528243d8065588251801d51a078503200d841d5002581c164811030b8100c1d00038800f030001c4414040c154481c9244a06242400030202c0e0030b240c055110004140710349118240200c560004001c174040e20180115800034032500316041080d0380e1a103c0010506282c0c0028400100144d60442001301d150394103c0b90f0074000554481005200c442d100206400c400980c035140c2840c8036258500c02144201d0040080c00c04034a903020800c181d034241940d1240401544190a04218049054118628001050041d580e0414581c490b220f8002503124 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 747444658 1250 747443408 747443429
    0x228140c0a0f030c111009060e010207050a030506160302070506010e0c1b07060e060f030a0c0c0c03060b0901080a03120213080a05060f1b0301031106040e0a0e010c02070305030909040606 82
    0x42d08101508503624401c0c02d4030035a0152580032201003030280380d0032250b0101c40050110781c400c00549016150300e105600043c415903d0443d21276001c00c059054071343c13040361558040c4003042085044400d425000d0151f910301940360a229441d41540c500040c001c6071083c82e0240003082c05d095a050844a80b05121400079469003c414079035030321761889105050202d06c3e0278410b0f0140c0d2a001040300c503a21940a003690440d2925640680207111480c210018000f00612041c042102d24070460010740c402ca10100e283c1790201e090140030038060340031f158254801c200560000b500803500d00c20380f445240006848200100c2c4440c580522a4400260340c003039a204c400a101c000b151030380c810314401c0031a0b041340e150b089510070728a01d690107040488a09000600000d885c1c0c4100c50a8060014001c40c181a150701c403181c1c0742e41c0e040e5141d804240c1c0e03a88082c0c0116000703000d4940c0c0c4d24220f00250907124550f449282d100d01c15418110300c2008100009001c1160580c1f0040107000c11070003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 747445908 1250 747444658 747444683
    0x4031106071a06030c0111072606010f0f14010c0b040c050a060c020405060603040b15011715030c031c030f0e010204060f030513030c0201111f0228140c0a 68
    0xc58a0421810343d04203001e4064620003140d0355000d410391011300c008003002000032601c2c00221080e803041940d1440501002d6505042c5805800c0185034041c0c01404c02600c00d07107190801c1702440c0360550340944620790745501c64205c40c0c3c0e007046801c0685500805640c2d2650f482c0e00e030100d5410800d41001c5e5014450714004500540d0181d6031800ca90320039034040017103883e800b0030032800303000807100140121a000001000074031100c006045110040c10840c80c60400300e04030035802d6101300e9062225640002d900e4460f45010050a01d1121050b0301400ea5103460f800c20450179000c030f04e203c0081c9610760307078000a501c90660180c50400030920007152581e07100e43c002803243e100032481a000a04220110380c8e0a54401c4803840c081e545902c491a030181c0765401990520040e003540c1c41107000b640e4800704589180340380015840d1002c076006a6500004015140c10350b48280d1501568415624092007140c024075895101d0701c2c038822842d210b82c0301a503418908902c40c10018113008201c00d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 747447158 1250 747445908 747445943
    0x1091806050316030c06050a0c06050a0e150c04050607110d06021e030c04062a0b01080f060c0a0309020a08011503110904200a0803130f06080405030403110607 70
    0x5000c80155441142518520300002c04000354461103404090306440030a00c08000c1c6601400040a60448504103c2d1566030661035440c02c981c1c0c101c903068040d607201c8881d601c43d9001801041c164048103940503c1504000010032900c4c040d5000e4640200c10000d07110742448400b9241101d13581c3c1c010000c02b1450128a440c0001e90461107100c0b09c5030106181c2d81580501c0c0740290b078070a5007202d00190819250500072590390040c4604c0007202c001101100c014026407010388000980903081501c0e00d03503d05001c4601c0c0845504102066400500038404100c0303160084403a190003c0c5000f16010ba65030002503e48000e50740014540c1d032800d074504e070300801c0d48644c40c021640a030b03506c41384640082040c410044e4007124000c005064901d00d0034413200348480910603003c0c2c00b400104582c0d4403038840ca4034540c8012483c0003400c90200701005a5905c03078001c4000b07040546003113680c071b00341991003d5a03400341c2e0000500040c890504070b950f0780c4403c000d0314012034019040d41d101039002c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 747448408 1250 747447158 747447161
    0x203010801020a140a081504060302031903020c010c050601261906110405060702090907050a09020d0b03010603050601150513090c0e030d052704150e010e010b0301030b06010918 78
    0x1070000013003070701105150750f0006044152155119a0b80790062980d907524030308100301c1000364100368003594610010016850802c25070202181c0501e481c009900c0780d0a02918110307820172440d040200340d100d0200051b5003c50031604590542481281c2d0f4a011a9040703c03011000c100600644610079403e14407000e0940d00c00c8880703015072002c1012203401100490a44200d008031a04003070208101001030030419410b03a403201d000c109441904e40c88800084200601c1d60017521100c0e0081041101d82d00c4604c91290310540840080040901d169903098030356030148907960701403024500e01c0d000b5501820868101c101c420b400960713039070307100c1544a004003101c003541400a0041c40030b66105050000e54800c0d00409038a41c40d003030080884020b124443c1801400c1080a81c00803845040c3d10b0741d000c0c061016038001000071800d400c0410314420000141d02204403c0400700040041d402c124048905480d00301001304039035980c03080140c8041c007056002030b40c2e410031516030310500c0105 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 747449658 1250 747448408 747448417
    0x40b0306491e0b0901061d0709080d05070b180d0c1406160f020105063006010303110d0804020609013204090c0e03070e041a0a02030402040b0d0308011a0706020301080102 75
    0x43d104a9060340f9120003107401c8454a025800031601503540007034002d01c2400b40e8941c0b2403100e1408084070358543c40343c00e00344024900800c1c08503202240344420000003820441e40510204190131000995200340c07035071001d28404c0300e000d10600c8005602440344140c8081c0f1401402d030300721190380c1000d2903049070807003090784c134540007035075051030380d1b0380c292041c001c1c540110001041914105640d86010f100d88a0b210f017109814519514a40161002070013454001c60103034841c140180e00103440303241800c5604403404100030500c8100401603917440d065410f100300a20340a884140c1d8440010790382e0311841800121a4003a82840215a0402c4001d0099075000304c014412003c043c5000e4a174440c0103d04543d150b0044c1c0380a116004c4004401c03a0310a01071120001904001c8503a50041e0038243c8031f100e0f00c1b81c0c00204000039800c250042a04240f0f0035207140b10282ea1a49004102c0c0506004010001106101d000115401801590751880e0001000c42d52940d54070040c5000b58070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 747450908 1250 747449658 747449663
    0x902070302071508090c0f013608060906150409140d021605150d0612210c0308061002120a020f0715021005091002040b0306491e 57
    0x18241c10f400300e050b200300c0400307018018000042c41c0d44440c0e0000c0101b0703902c20b442000e040203581480c943c246104900341c903146880348000380308410700c0480b0385a110704260304103c14550200b4280100c040300002c48540c010000894200351041480008000e000d10714006484680b685218075844100403034045402c10355902100e1001c525440d8114841c4820311640d98032050000d54501075030550350051282401311800000c045071141046080141ca80340c0580b059020702c0c40550540100001404c0b00d449e150901e035120403070507500140925001007450307020781907410300607805500800c1200c441114034038005850350302e601c60007543c4104428010005100f000310016140c4040110015865400d40c050b258002200276020040c02016002255610540342c460815085510140000d402c050280a42c1c0341415420000c481c0c1d0358038080d0a0100101c0401090300b103071203101d007480c90803803007a1121140c446020b5499185c0020b9002d0b0030b8a903444120f05244007001542c003200e52 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 747452158 1250 747450908 747450929
    0x40c080f031e161a36030909010b070c090213030303020a0309080a030b150717070f02150414090610030902060d06030b06130e030a0e030a050703081b0a15020310090207030207 77
    0x544941094100c0080c1707401e0304200d4608200c8012100c000006100f03001400501202d2601750000040350311080c0c242e000312410100030840208110080c4040001814403c00550070711403d0002c010304103010f0310006080c90b070300080c0742001c1d030b0194010410168100c140c2984911141d0800b070068005040c0e0039204500004d020204840e041c1c082d01c0c43e0680151403a4280b0516900e03881e101d40c007412094a0410340c0314a83d500580da4440c80100a94400704420f031503d242140408254517400c401c188564603502c01c001450702c030f001d450800c110341c501d00440d07000c0c0d02d800811750900c100700424042600f040000f0080c00502610103005040c1540c00c0f0101d80c04001e04001229140c0401a00766002041a9040944200035240c14100000c00780da600c014941c0c0c031149002803652003150041000b15801b6030b041f0700c001395620030704100c0002d0610005c155440d442c440b40500741c8441e0302503001c000703d2660401c1141400140580141c119560241401d02070340c1d4030524408d452262 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 747453408 1250 747452158 747452161
    0x130326010f091b03230106031401061e030c140c01020903070b03011208070201110f0d030b0a06080109020d0e25050d020d030c02040b030a0605040c080f031e161a 71
    0xc0410b40b0079501240183c4040c2c0b80c0200751110214040d1441011380314002c03d4204880d00308076025030034103008040b43d0320000303218007010006004500741644500c041c040c40c0c2441c14002d5582c020710885190072490001030b1088503d005503940c0810400103903100c44d01180f200000c5005600400c8020004c400700c8440e50740d2600300072034030300c405d000f80f00501c0034029030b800c00500c0d00c1c0060306a107481414103d182c1e00c1200c0c421440c00700c4100b00d52065500204040010340e4042c03098840d1090156030440e8568100b41c00606003503070601c03401000d95400240e00f800180700c2c0e842980c00750701d005c090380c124107d030030450000c0644920340290202c4444000051524290002d083e0381d42d800b504d02070440c3c98503101603c1d030108070581070340c00903101c0002000e15070303092010624541c8a19000a0300303003002d040a0050304a02e03005142301d07a02c80d14902c6a149800010b0702e0611107404490b21060040c61400042e80c000c1000501c0d0100e01c00310703030300b080040100500302129101418a0600d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 747454658 1250 747453408 747453419
    0x30103051506010203040612020d0507050706060509130206090a05090c1909050109051909050112050c09070215070516030503072c15090604030308190b0108130326010f 74
    0x162070341625a140503078001c02081001c58042c550020010722801c0d001810004095407100590750210b0300100042c1c0001040d808200c028454407024050540d24100c2e40d1600810321039076620340da50043c0c850940403900e04826900c0c214840c0151a01030072074201420249040d0200f90480401c2c1491048520402c4040500c0340d003c01c806c40301d0503940c03400c6c007904c0d00303042c0010350301350300d07255003141d210302202007582c80030784c083d841c001d00305180e0003614203426080803420100d119200901c00d50440c0305210079141c0c0000d8802210b844e02c03049120300c1e111a90181d44030f01c0b8440307038081c1507217401c6a6403081c1600712000c1d521807400e89d110060b54144041d00c000d500102c2c0001364401e82e00b020800388503428404601e04403401c40340c0c240351a215420001900c2d60708594401c034000340d40c503010000303d0001401d0950220b800c5080c2806062001000649803100c024030400d08a40152451030905120720850701c0c240d9a540e0207000250403100b201c81040000f40180000c9480843c0001007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 747455908 1250 747454658 747454693
    0xc05070b01061e05030c120412091211060903213a020f0d090605060f09010308070f020f04090f0203061006090b0904090c080607080c041d09070801060b03010305 71
    0x1103038400d920740079030880410195450b0b04046d21208408030140810099010b0f4800c0880c0994003e180f403c0d881d98840e800108a10b419402c529803980c240e140c2c28000a40c04940113040c4101218003544600c115804240b4009001c0f03c88200e070060300d14080f19101258004001e118156200c2042a407869002104102c0e01d02d24803440c40d443d8000c051150140303d03409001c2c00d5108420191900140d541141c1c03c1d14800300d0b0944059642c1c00502016190507515800740703400a4a84a507250b00d103072600c4c0c2c040d0040440140a01d40f40000c180210350b9a031030214202c2000820401000d8094108140c440ca100b05089000c0e02c130326004580b0405803000c454084609c0340e60350074499400c0c1140000b40341c000c0b001094110383c403a2100c1d40000c2ca200c41040240004000503c0c85280c900742c000d14101d0301174200c1c034405008000502411030f5820103019105401003012107640c03140c1500a00e0140d481c1d004108075480c01e440860352099640065048a005904940884030301001202 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 747457158 1250 747455908 747455927
    0x3010f05010305040f030810051810091512061e05070f031104140d0b09060f010f0e070819060b0c0c0303030f0106140403080a0f030e0a03020c010c02040207060c05070b0106 76
    0x140180c1714442c0140002e0f1050714401e81c000c442c0c43c00f1440990780e4401041815074403004030034603c0c00800c00c001004000c1140704008003108031081c004070b00c141605450882d014010b80580c000391203408405e0004a0b0040c43c1c0c2152807440301400782080c12418801044203a4424001036001c082c0202c000740320340105030154001c0d0003554941403401c04004219000d68140c1307504131503140221008a05110800b40c418201c442c050049072418072002250f0190507005800240c0c11f400007801017a0640c449258042c0d04e0307041203580c80d203804803454600100c0949903085107080c000b000c55070302c0401c0060702d260b01d00c640c11509408112020541ca030702080700c2440c00c80b05202c0c010030516104452005c0740b01d0882d81301c1d901d803a40b691100c0d90b0a0303020f1100c0d00041000308030700710500c503030521038070341c481412038081c00c0041100d40d002915210961a802c1c100400a4060400d40d07645604803103e0a9220904010110005034040c1c01a08038000c1a5040c4400900002d0300601862099 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 747458408 1250 747457158 747457163
    0xb0f06090613090c0e190305071401050d0c020c040609060b0304020906120109111002010509070e0702010e07030b071e05070b070c050114090f1f020a02031e03010f0501030504 77
    0x50400851030180222a00300c0c4008046406070341c0e10001e40d91000d40309943c0007000558075403074070368411014400007070f908481d0b000c2e40c00e00d074640c108049140855800f09a44050162111454400c0d004880328000c8146004945107004000c0c040541c002620800000c030584083c05071542c0d84082c002141c500d48500c80040100308002001490300f52070181e0301100090241e18241160300d822421902c403108112400c0078241030302c04142c64041d07114a10040a84002d101c58a030a800e82a25201c40f44034000100f100d0201003074416000b0742000c0c120440c003c00301c07800e066881c00c000760b0812003912030300301080c6d240741171036442c0c1910095004103005c40c0d00c4e0740740307055050b80d01d008103080028051030400407c111442d00083d404c1c051000103a0303d40074080500d041c1a1040d5052801000b400036040d880440045c03165508a03c1c00034044409400050301d8049100c4168198071662066440304400106c2c07122a45170030001a5040e10720304100c481050784c881c0700541c100c500070340e400b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 747459658 1250 747458408 747458419
    0x29090a050d0203091309240e0c1507020405060f060c1b0d030815130603060b19050a051207091d0c0301020307140c16060f020f1504020108150d0c03060b0f 68
    0x845040c5070300d90300710f9075007184281741003000c0742a0140547d180c101000303c4034004079120821700020900400c03520409a0046a00d81c007802401041506544a0303c4002402a9282c0f00000c0c415a00c1240c0c0d03840d5440d014081c19600c038101c428a0781c5484294014040c01109013622a00c1400c0191514140030b90588031441141c480040080740580003a003860f5200d0701c0c0c201c0c00000c06d0400c1c05000c004510400010400307425403010407030032141c2c121680c442e11514100400030340d82e81c1d809004c01c0781c205865000d007020b60303001303076500340026074001c20300d9681031107403a92140f8903402c3c1443d500d1800d402030341e11308640300e0209401e03840140c039102c3c0020260341e08003d403001060010800078103104200d17403a91384c4d01e01040114144903804440030402c03030826080e07502d4050141300e241200035405042c4941d4440d01c45503c505015101a040140e910005540106801c00b10403400c080140380b40000c082d00c1c0b40c25070300d4441070300084411178101001e01d102c80c10018007401541100514 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 747460908 1250 747459658 747459679
    0x170726030705030c0d0207152d020f090a08300a140702030706051806040e040b270706170907090c0201020909011e05060f030429090a050d020309 64
    0x10102c40c59000a44201c441c0101002960580031040c0700520086120700d102c150313140c50164a040842e8021072050b04a180822041200b00300182259600da204131030f0b0058407460941d0b4140410700400d008075820402210300413403031a43c001250040101082521004201070400b0a800d80c070010581b030410700c030180484035106001d8040c0e82521496803e2070743c28842c5035000a460000f0640c0702c00003180c0c0014680c0b4001100804240b00c40d5020303100e4034642440d12032612010b03040203001802086003c004602c56481d007108555011510140c05681a0b400d410030036190180ca105101c04945050080048800c00301101072041e01c07888c01030700b019894080d00c0030103003411800b180c0c2107540c02c000c8140c160f510140c01d01e02034650501100303101c00c8000c403a1503422000e900010310030941400442c072429071410407030b0b5006520465080c0c3c00b03d00344400441c401100350100340c40302c005204114103603100180b401d540740c2c011412581c003007103955000e07070b00d0313210301c90030a030300301c4110b01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 747462158 1250 747460908 747460921
    0x506130515040f06090c0e010501020102070206030604021b030409051e060915010908010c082406040317040504020316031a030a02060c101d060a0b130f0917072603 72
    0x40701664440d0090140325540042c66880904035640d42d0800c03510760701070324001c0c0841c0c003003007034014050179083c0000c610740486500003455500000b40802d06c0b40b50005030401460521051000c50464034608030703a11551900d80c00c0024100484100401102d856410381640f5502e841c95070291a000d81300320300742e88418a0701445e070740203890100c1c144503100d0400101000244200340316040c090740c9480c924241b900c440d0f500640c0e50034040a001c11352000760803007580c1e41c200701e50171070b80c0c0038080b52000d00c04020403049034041c40d4005540680301008218140c01001451045a019550100030601e0261215070005446440158240d03002a40260050600000078102d1400d0071044942803410010050306440c441241202d400b100800554681e520400100e40c002c5c288407403e104240b40c42c004078014030b09013044980b201c3e460310050b10350f6030701e240d1040c00040d8100c0040030712070348840d000c401d0aa0003154202c0d0703210380b60100901092080b4190700303035507185080700130315549951 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 747463408 1250 747462158 747462193
    0xc0a0303140c0304120201151d090303040c1215020307051c0516120e010501080a031404121106311202090c2b050414190206030712110705061305 64
    0x103c41441c02e6646c1c81d884030015001c0c540e0b140e801072540410000414009e039403183c840c3c2d000030745602c2e19a881032052000003090201c820b402e413031030110031801c020341500302400e244a1000090049030b10000a0040b042c0e4441c00070500e030032400244504002d0100305440850300125005490080102c0e142400d0a124101e5001d10803540840070441d200c00300300540c21210b00723038024003142d48440d500000700341c2c00207000c1c1c406200d0708403060704080c0f5040300c5041e010003078a00105400d182c00000314440d0b6600096404000c100000c529600b0f035201802111800d101c0c4080c0d034401c3e0000d10004018050110300c51382d6580c05800c03540b043c1c403007450740321440e00440c0118030100740c0c04503000c000742290441c40c01c10300b001d0600440c90781030505023641d10080001341c210640d0070080c11007100c018204040b0140c181d050720825601d9640003c11a0b4000d046c42c020100d01d400c01408501c0c1e19402d1028003a0f9902907800c0d581c5644640210780e01007034000b0b05c0140290020003240790040c800c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 747464658 1250 747463408 747463433
    0x90b0c061b120a021b01110a030e0319080c04080d09140d0f0b040f02031212070e0d140c040c0224070c060c05160302030a0f080108071404020f0c0a0303140c0304 71
    0x200c145171042543e04e1001203007551498030361040360721000725141d016031394180900c42c43d42c03003442d000c1c52501a203000e902c00a907015000c4d0074184240c20020a141000302401c42d002001034805170307040d50004500080403c101d510610142c051241e186810074504802e000307602c2d6611a541102180c6c2c1c036610140c400070700900c10748040b5491142d0002586083c0550801858000071041c9e481c2a0f0141e8800104005410302081140070b807054a426250740d4143e0716160740010151a0000440e806c45142450804120f5001403d00c3e00c17080071290000741021914640d19043c42d540c020f4006104d4003040d0403902080003c240704642c90201710180c0c0618903e220030300c0c0081c584400a039810110f1038100e0400c400607400000c3c05000036038000c204020b2111a464502200c2d4540420744d52366134a28090a40142540c1070840b001e17540b20342c11500400c40d0f04010700d80b50301480f00d10945820030b454040e00070034240348207100c07059012641c0c0b910851a50070791904588440c0c58500c0541780e03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 747465908 1250 747464658 747464677
    0xe060406171005041e0f0204030f110f1c0c150c120c06020307080105180103120e1206010801140a0506060f09041503080d0606020604080a0f090b0c061b120a02 70
    0x140300c2e10101e125111070084046a85040e41010103040030452940f04031840e00c1003214a4902c1813009100190090000342180303a00000d012007010000300010359002600c81d01c40d5417100071665080c000752450508444120301816240050a68506201306150082c0c841500040c101001c0d490000300d2040000030424541e140c03a030485038480d500c96013240d10030303100c20700403c130103c004024514164240e4039084000244c01c070303415403455640c28001d040d40d406940502041c0492016070361240c800c860050316241d000c035500c0e5603444201d14000c1421540b41c094114841000034a41403031401028080c0e1070240000340741080228200c0c40b01d41001d02c0d200c0c2d00940b12041281e40420340d410b08000346004482481d40c0300c01f000c943c0c4040303034000c0d80080c040d174200f0000c10002c912240c1c2075691100590170500b07551222072000b120080c01d01d40024040d108c002c87d030110080700000c3d0f03181c4120b560010060209060409080240c003810b443c3c3c0c01180f060f81e0002d02070400d20380240070844c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 747467158 1250 747465908 747465931
    0x191e030c05060903070c050130091a040203010c0f0e041122061e051623061b09030a20030307050c03070b0f0316050f0703020a030e06040617 62
    0x52890740d60700c0c00c040e02551181029800401e000c000c1c4a0403608206c000c080900f804030b4210410841c564076140c6103860036008611070381180070b80000a8000b9100513038480080807600f1041e0000c0c981c2c0102c10b44080c0d01a44c40d0044000040b40100c54030280082a078445801600d40720342004007400a41d00d8030350116105001c1c004815108440c40040844460b6280024608010f0010188441c5585009807410104a12419640c2140880306501103804c0401d1407800c6030b00f009402c605404441030380100020002040c0b150002c503030980503c0c200140b40c1d080700401a001d0401d4020641640d501d50010341e03000d0001255540c0d01050044100b1000a241d0346001c002425038104010035070745034210700182c860030f01d42400610054000c12010354101186207861072010700004200740d2207400c0000400c40128001c0003550140c074990240c01d0780d1506e8070b18000b5102c104804084010a02580740d04001e4580141560195445a030314a041072180210280c1d5442d0081c10248265 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 747468408 1250 747467158 747467177
    0x4060605090c03040506090d0e040207020418030c060c0206041509030e031f05010503282d141203070315090f02030711010b100e010e0d030809191e03 66
    0x1034903004010352041c0d0210702d41035280c3c0b03001c1c14924280b04004103a0521a00681c0215903020380100b0f1850365000150340060312080710b840404c005000480a01004e100034404020406900c403103140543c52040c0000e00055001400980e602c50003500c1c002c1603c1a20305440c4070212096000800183c02850406080d8044c82c0120342084058a02c03486944040c055450306000f441c06268010a419801000034003458018848180c44003250b030904200c1c60203044051081840304694820606c03507982c0c901c00c558114100707261702010300c100c40c2c4407492079103c10400d0300404c0c80e42c6480c5214078442d01c0c0d03550310403046001301030341c001500a0503510745011480c440a4803e000007107100040069690401a00150030010707060685106681000301c1b40889840322001502040344600700101c480c600500140d8113110541c520355007003a10808141d06041d4008001806815200240e950010440851080e01102810090aa06594042d000d0706801c07070394058100c28068070300103040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 747469658 1250 747468408 747468419
    0x30801031502090a14120a0503121906080106140405060906060904180b0603010605061603030b040612060605090a09051221090708072c040809101808190803040606 72
    0x1001d00c030384c01c40c1602c1c600d41216607805d800c240322a40369854011004100090303032603880954a1044604401d402501c107004503824014200c43e6034501425400280055921119014020102489044501da400300303a00c00d09401c080c81094010600a480305020381e4070704c0284000e5500c950308d499003090b0740c2c0032407090691005009090041c031901d480081401c00c00109820341310241c02c210310481040008e11800d144100900f4907066141c140171402d401007800003802844164801c4620380d500030a0402008071583c071160030386104458880b1680c55100b0310404481c900e035802070240d40421044002c09076401d014008140808001c81105038100c020403200600646000d400317603110303031001d2182070401d0204401030144400c86031540c02c100c40388045114102c000c1900701c405408081024013400b030045500c502c1c0b001d408180484150707003005040d00105080700450140600c0041000e030400302d1010302c06121009180340301c90003502c2d80d8840307a10103402101c01550f41c0800050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 747470908 1250 747469658 747469669
    0x6130615180c02030d180b070e06070b04050a0213090c080d0c060209030106030206070b0417130e1008120901030b060a090e0a0f1503060518070b0a030e100509160303080103150209 79
    0x340102c6e880100c28552003a10700300b41d40c201c0c003900300400c0c42800c80a212058a8403816208426080b8004d001544c60380c1c00d00505140d19904081c4d041078129000c1d1800d80031701c0d0000a01103219040220110396035901c0c0070384a01c0718180c0d1200056400c00308401268035500a4040044020000201c2c607a81e540000c1d00303580720000c00c90304902100100000d001c90502ca00c0c15a08000e864585000601030310040c000d900741c041d039116410200c000c948000c0803c25104050081002220500d07400d00442a11070f4008041c1180040c0c00e104050f011414184251100340d816621011580340c02d00b844205003c0009010703504a61703447c40b140c003000300e480c0120101e0104000c043c030403076411030038864262900142405400300700141e050092081c0001c10340204c03071031407822079241c0902030011001340c110200300400c5e5214a2041140142160307120a003d0102c5204803400300400b09401401c80e03010b8440030300456401d000401c081800d40e00407040c0316003840c00052924115400160 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 747472158 1250 747470908 747470921
    0x20304030215070509090103151803030b040b06040506030406111306030207030e0d05100c0203070203012a0c1505060d06050901050406050109140610030b0306130615180c02030d 78
    0x9006900660b24145903801203844107030032000c0e5241081c6072154038000f080501d00c040c4001404404000b440e100f004440c2d0b444158280c094022518103010b29040c020041d01034110a1840742c0d01e0300485c904a441d049040320704840d00581910b09640da00e458800003440a0804005000d10070000030924510307c0c0001d0300a00b2054400588628842c20010700c0812440c9015002d00301160f20360021940018904600304660712001c5070b200401c6030203c2c00c60150290094166082c02c51044030306a450500d440d0308004500305882e0080996800c441c41c007411a40649902600a0513081d0a141600000e41c032000c081c2c00003844004503510001280c2045401d81401e9540e48280b100f00400c0340141c5004180da08000d00860ba00500140d00e4030401400480c07140307003100c0192543d5802500000c40181004040d80c8141c07410003003041031444161421914207190900c10a40190100702c00b40c1a11102d144050701040b0f07412004004040310300b0680203602c4203014a0744040034501540c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 747473408 1250 747472158 747472163
    0x215070503041d06010e12071205012f04030b040c05090901020a08090c030304050402031b0c030307020f0d0e011b14030c1b011704140102030103031e0c050d120609020304 75
    0x440e5664905501e20b1103410340c0c50790b2021111490340c03e1040a0b80e2200c014100c500c0111900340d0050000c0d44194981501684403015044210003000f040c88010340c0507503840c030045d65aa550405904002040342c4ce1303d02050036075003006000074404a200092080c0e071041c400d55080840300c1d20b480004144035000c0341e00b031000341e40000e598103000703130b00c023400c0358210480ca0000d0421840041c00203840b03020314007030540a10b60100015010403c1701c8000f022000c64203446550311300741011000d840b90700884d4034102600ca819040c40c00400c0000e150101070000303983d4100c04a481a004447d2082862090040d03a181011404045107412035180c0559030100000d41e0340c0c0c051309140303078100b419140c824440303440141412681030740c1142c1c1c4c2800b10100a088000d040d80c032454011036100601f6180d4038250702c080008810541c22401d107558208e9803064040c00c2e042040812117940481d240b008095030007c00590f034015001e07030055041140c20880c04525551111238040480c1c0048a05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 747474658 1250 747473408 747473413
    0x9090a05010305010b0d080415020a1205220807140d051e0c040203091e070b0301060c0b060906010903060c09030f0c060923010e061909090c0e0d08030402150705 71
    0x402c00c0140034403541e0014441038501240d0480940c807148010f0040b480390910302202031042045035807013407000c541d0301503000c0c0000840c20003010740100241c1060904600345000640a000c0c114210345002084880500082407814104401165503143c1403000c1b50300403000d850000002401404407403540703903011600c103901e02050243c4034074204251202c18021407040041c44112000172591000c0d2a48940c650345241d40c0c0c60b40e05501e0030000354010160f428020001281341548045c02e019207502440000070700341c07640010460b0a0506a55203804a10701e400100f0001c0e985404c840100001c1d4100242d20560307235200c1e4030304200442c508076140c0d0504001400026001040c05004c0c00e00c20b100c044595000c0c4042d405884800c00e4058140b09000204001c01d030340329000c840007100c41c018007101055502001801d484100d015101101d0b080541e092102d43c45901110001d400042103400c51814070713195000d5590020300305a8010113940301c00203c050100c4020b0521a10a800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 747475908 1250 747474658 747474661
    0x1031109131e020702030606041104031208010806010b28120608012c1504151a01090603050c161704081005010609030f12020114100614040b0412050309090a05 70
    0xb1a045079551080c0000da88900c107014074809628000340c140d60200d01074500060280a94030003400d01d0080b980001c0090702d600c0000300301170358070644150403a2010805c44c0c0041c0d0701c44c50f0341402400750140018404c0020350050b0448000601c4002480001e4244a0290266514998251052500300c034440e40c1d1a04444010710201501d03007190b0005038111000502410390146803070701b0386c9000000140c4036000128091240c400c001b20f041e414802c0301045485480400c4c81e40c80c1c6050850b182c04164a40000281035009008031489101d9225006142c0b149a0034180c88440c184001034851407404c07144011002d0408000304007401d8a81c00a150340c5008003012001d64405800a1040010300041007001412800c68000760580c04948401340d81d010b9141280144000708909403c801400d09012450301120442425a01303a9500d414001c4001d01000c105071055114243c100300d000c000800030803c1001c040318002c0d00c640c0c10f6a00e001618000210075030000c2c1d0340d00349000e80e40c20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 747477158 1250 747475908 747475931
    0x201140d15060507111e06030c090301181a0106080115020106030c1e080d0f0c050a330203222103140603010e12031b04090e0601050108040f020103110913 68
    0x40d0800008801161000169413540c02142140c500c03e40b2007074040c25008c000706241c0c1002406484960102030002c11a01450050301d8130940070010342a5820308844112031002100c0c0c0000c607060307650580700c1e031005920703003c000829110f0340800401123540c0c401000c0000395060961000600c12400c8122100414a841141c0d0010750382c03185450b50b100d10b80c103501143d00010411840c00711b23402c00481840941c00c0c0705003000f41040004203001940c400c89441c9030074a082011b00702000075400c41d82a071000a000c0128403082c3c440c1d540c450b0708403140c2c00e103a00b001c50442c46102e105e0320460307a06030900300310b8802032000c841101001c2070b00d8005055260099110543d0300c90402c90090000d42d00d50351441361100043c00000c0c0410030000b002603202c4c00c0801006444004000403980d4071799507824460000c025503007104519006203070000900b907100b08506e0307018032f0700601c405424401d558015070080c000011440c000300e100f8006103500759280358204000e11500d030000712f00c40701030381c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 747478408 1250 747477158 747477173
    0x10020c0411031605040806160915030603060b182a03071d0d020f040b0402041503020c070801051009150f23030102031e0903040302060f07030305010b070201140d15060507 75
    0x400f901002c0080070300007000001030014880e41c102c81400040004040003000868803d40190031103d030000f410341409504a60580c00a0100c034000d0004001c240c42800400c08410340c40f280396002d041da1407010ec1c01c0c46000d0100c07491900b5071107444160380341018004810a4008441803c081000c0c140c800c0c01040c810150400c1d00f95044401c3d00030040245e00050540c4d4014095500460780d50842c11450344a07a41110082c2000303442c4030f84090080b82d0b004000c4d41c001c12400429004504001482c150140200b41c041e142000d14403a00509112500c802041c1e003000c0002d044821070400222030050805c440b01a1001c050200880340c500b0024141204c0300e1036106000340c3c4100200b204c0e44d00100e0414143c2c8010481841032500c0d0544110300e5070044c1d0700b01a5028000040071005080c3d804001e1030074070301c00c2d1414401c680e40d904104446029400010303011841d00b507261000c0c850079900908071801020360018484d5a81d07e03d0710719031000768001c6000316500168503024403819 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 747479658 1250 747478408 747478441
    0x50d0f1106041509051e0a0c090b03030f0a03180309240e06070f06050a051605030105010e0603071806081e1603020c120304080706050f0403020c10020c041103 70
    0x224001c006504165641c1d2044102412031000b2440d6111403460400405011080000d43e040400000312404190780c01d4407030004043c1119010399858000891461a0003180d942c204020095402c185146a10304290b5001c0300c041c0f001c044d80c441d080c1c8004000c0c4904604814065940d151070203044c00641400105203107194464504c80042d0301c41c40710b82c45450025680c400b90b034050f03290f00c55841c0c50b06c0031001030700000703020318100401c028030103242d588003910a042c1c80c80b4013501809000e1040c1d5180c40300b8000c0d01e00044140001d044103090140041d900042c131440d0254042c00007081014140300b0542101000920710018003042c0301d0003101c55041d8040c440c00460240c10204184101a410302c0400e40a042e0081800700d0304181c140031011883c402c4050b4580d51749070514061940b648031007011600240341c0b41c081955182883c2c0080e104c2da605800520001510740c003080340d1140c0c21001e41046204954840700075449600a12007540081c0141513103034240400d103039010308403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 747480908 1250 747479658 747479687
    0x606060f08090a050a02100201020f03010b0307020c18070e060705190204060f050108132604050a09060608130206090418110d080706051b0708031902090a0b0c0a050d0f 74
    0x6070b02c49501260000c2154201703a80d0440e50000301d5442a102030f8013a000d0880d2100c035482d004000051010100402184130f104260309680302d0120a1003088120324610350185600d00e0820300040680380a107811040110f0300429107800c0c01b54a5903801d140c4100195032a10100d203d00e4000c00714200350060a0150400c1c85551891310b040c040001c02d02d0f00018841e41004503410800000d0000c0032884401d101080d00c407141810802c2001040c0e5a400742c8545401405003180000e10180b0b42c0c4142d2060703c5195035203940c240c584d0b10065200308000b207020ba90040b4100803010f801d940750b10071a003104074086070301ca0401d842c5090240210710f00003d11030080200392002c4001601313080849020316403001002900740c50342e1126545c45414405005007100000980809000034903029510516000d411010100030f01d0607100140d01440101a8000985010501c4020941c1c400783c082c2c0c09542044460000080e118940b0700030b210300107003011400d4064183d1000d64011083d007e05c20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 747482014 1106 747480908 747480913
    0x120f060803032d01050409330b0f1f020a02060a050301140d15020702010c080f09120d0c030309020f1810090e070b090105070606060f0809 61
    0x240195214043c944045848040b03084580c1c8401d52042040b0600c62084d929050074400a000c0400e02111044181c003140306401e41000c200703916404010455610030804140c20204440745415420b0081d104200c04202907210704440340c001d1103000d20380c1584134403012002c03402c104800d27100135072000c40003c1048000d580140954180c0e020031541001d4041d00004100c0040e5100f003004002c00945256443c86270f0550340039194050042c14910800101c41c2d40340500e0758000d040d10801c250010400044c1400c01011060603580300c1c00040815001c0660040c0c4031020741c040c001c04054403005004215224400107a0806e0405001b03140007000f00404803400c103904642e0400c400d505110001942c00c02400703020036040c19080038003d85810b000410765646d0140001c2e5060002c100850340024001c3d10420b0000c0556644000341c0d42881013000300303458400381000641d41d = true := by decide +kernel

theorem cover : BRFrame.Cov 747302158 747482014 := by
  have h0 := BRFrame.cov_init 747302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 747302158 ≤ n) (h2 : n < 747482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
