-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1465
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:07:22.807884+00:00
-- url     : https://prove2.me/submissions/205480f3-8fc3-43c2-8e0b-d9cf4ff54584

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 263309352 ≤ n < 263489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 263310602 1250 263309352 263309399
    0x60a140c0115170c09071704260406080c03040305040614040518010905090a020102190204150b0c0f010c0c0206070321050105150301080c010c0c08010e0109060b180406050a15 77
    0x1009906130a10031003180c122004404925034402024840071180c200c941e0180c881c5038000c160440c3c0c2a03243c4403190714043d0388464030340082820300c807160b0403c40f1282c10050a04610f811031a065034018841e126a0040004001c05a01c00c500d41c111100199805000010094603030258100c003c40786414092280820321410807000c140207810102e0307113078000f6030180d0141c04c800d6103234075540c501070104072803c0303070095502c80b02d0b0380d10f06441140a01c003516104e03000303654449122110760302e0505002903a08080c0d00d071164002040b600040010002a4107030340e5a0786940c01401d0640b010040e2200000c21030089202041c110011a40414180c810482d09120756a02c2c0c40c164800070b0009000b4180303240d2008240030655802091414809481949100e80c0903460b0a011070968030400400070300d81c0c2d15450a0020480c0a0259031250002560016054000380d131441c103403050003070000341210707540f400030544828194100300c4000e0070704454410704030340d6a00101d44c0c4030627420409a1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 263311852 1250 263310602 263310613
    0x2030a050703060e070f051818010e1e070e0114031f080318040b190b0a090905040506131415090601080102192d030209040b060a140c011517 62
    0x100c2084e0101d200c4e0043c403050359911080c903200401603030140d00c5850301c9040305c1e40c108800700071652000c28446000c80904849603a035450f0060b9400c0809010381031362000300c205c0c3c0b0721591003803400118aa00520038a04108144c1c110401600c0b00700b810611000d0001c1c0000410230b02c40e85401c00450241c1c102404681d0150740c9818080e1a4022240208003c900a0b1802c040368540b82d00001546440144006400b0008006c4444640300c6a032140c000c205000c034000942ea0740000c03445004203107010043c4400e01e0255100ca8664400608040710030760409940300030300011400328000801c01004803080310303000100318050300341c0440b10700b40c0511411002017030b0740c04180250360000c80c1c40c5032449200c8503142c00645240c1c5505484100500013489031040302800c40d01210303491043c40d1401073380d50200506100580300d07040e18413806414208480d80781168850340301849500f1071200f01c0e40f107c000b10450380c050f01041404a000c1d0900d4000460300b003642008000b1814880e40c1201d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 263313102 1250 263311852 263311859
    0x1802150702010e01020f49080106030b1f0921151814030706020301240903020102071403010b0607050c1804030f050315030f010f0b010801030b060609060d02030a05070306 75
    0x2aa00c01d1b0884c407076059500079524a41056507000385c1141b1030412002e1180040c8041842c0c9180304480e454541380040319161406249904089541c2c050f146a25061140d0100100402e903240b00369440070440300110041402c40501ca8070403c005841101490740e6508121007501480c1440ca15090f5041a041800340b02400000d104d500110464280510004180b5803200003401e01450b0119003140000c000420001d4407610007140030b00303604031040700780c18140c004604102180294150a00c190501e050000d40e800140d078400b01d07185070b051500903030555000319024051488200350400b074003258017002c12001040714007800c4002c6c0c1d030076a009040c40c15031507209030090790050b011802007400b594911388a41c00651344010000700e504802200d00d0042840c2038065032040000b65503c64516003058210b01a1301d0030148241313008000e82d41151034140d4020405803007948074400024103030b01c15032201c206482c4010440c0e20119201d01d004218000504400c41d007903070000b40740c1700303011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 263314352 1250 263313102 263313107
    0x903090501020106060323041a040c031101021506090c0403050601092703090311011e08010305060106050c0705130e060c070c0f030b06090a0e071806050301110a031802150702010e01 80
    0x102d10070706400461030381c201890a6000ca824005002601c8200c1112512a800c0e003c9c0ca00082c0110b00c45c1c4107000c5854914140001c0801560031518119001030304240b040620500d00303603030400c1007100c01800540300d520f040705151146500040490081c007000080c0070b1413503408003860402011101c6440c0d0035807072104003684040c101c02408548420301c203001260042034103034081441814103590443d0080c009040c80014a00c030b490019001c4801071080000030710503280100254240340303007000308282900b40c403100c443c01128026990702c14100c103a2401c03500281180c0105105544942c14182d40d0100654081403040e686020041000181c00441d103900b10210381d041091900a9100e071810043c01783d0016001d81c0030a616000a8042e4081c144090f40041c04a03280301065580070908440030b4a000354000e5100713034034120f6100200d61030102214404901803600107500d0708a01490358910301c0f2010040d40014901070054000340100c0000d001d034a00036240c4450420681004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 263315602 1250 263314352 263314361
    0xc0d110a05120318210f010b010f2102130b04060f0206011202040b030c041a01030e011401031b0e01091d06010f1503020f07060204260a03050a1209030905010201060603 74
    0x200320b01a0b1081002c840d80b561040215040b1440040c50001c0e80c0e0145da03010700c0041c4000c0d174902800d0300301403580350f00702a0034415001c81550a0070440030240c020740c0c010b0b00e60041074a102c80001c906180c901c81241190b41200d1039500490000c403422a140c80750709860346c100d0700503000402e02c1016241405400090b03120304032030f02420701030343d200d10550912014102c80d0301c9107a0188900d40c0d024800b9511350199002c907810015003004c1c4440242c000405440c41845110060703498a01191020f204510b4170034192a0040f20726880074914181910700d00c0d0441e400603100f10a001d0010840c1001a0800340824251000b40e40a84401e603441588a200038441c2c6075540c1c00340c2004101c000154900b50310648100d04005044c4490300550b01b101c1e80c0000350440301e8030b41c0064180720407102803001c1e640d1200c584c04040d154050080c51550307500f40803213001c2d0a01801007500c0e2181d038440c0d03180d8000d13a041c0280034800d6294614001d492070043d8054180554200600401c482d44030303119 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 263316852 1250 263315602 263315629
    0xc1a01080c0f0f044101060e030709050106020703210c021c0510090b07020f030a0507020a12030804061a06040b090103180809010f110d110c0d110a05 66
    0x192088055034420010102109818540c0007070041001060558691040341d40300c0c4550126040070f03003101c058612280d086520b00c007406850310110140781303d02e40b405c030505551160500d007901280c808002440c11400d503101d0f4054030b05140010500355804a081002c6a1244080e02c0080d0801a04110000c060070501000100b0021640340985400d0300110b180707005003206180320745411f8807407504040c6e40ca034421081d1a02d4401030780c1004010404030313a004e5010700c040d101100c0000d0795507459102d000115020040d000c5070a000b59a1000f03018001800e03600d404138060140e41c80c0203881424100e4007030324120324000b640088216000c4c0020246580100580d25207030030051a581e841c1c2124260b075040513a0781c06101440042c01180800d801c1c00b500c0f000d515010500c0c0010150300750394a9400401154082e0170070f59840014881d01005254200220f21305203601482d86048005103016038401000c00b048020301200300b0341001e6a03e400d60301e04160b140c4440c103104190b0340e00d04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 263318102 1250 263316852 263316869
    0x10603060b2b060219051c1104231002010902090117030a050d110a180603180f1103010203070c0b0112021008070e0d030f0e090c0a050f0c030a0c1a01 66
    0x1010210742c6108810703020509072081600604000070380e02c9814880d00c10940c0100402e1000400c242e020301d218220112290f060b01003031000808544503022140940c1c45070192842040200c030320204116146d951803820040c0c01038120f00078542c4002d018002a1f802640100c61590010801c1c40310504d0940072110120300452820b003035074200300d0b00355001e46400b29040350b841c5101001d040c45c4038000c00044100b944c8541e01e03030f01d50010740861040c0f039501810500d40f81009444c420025001d951080c144c1000c00d036410408503050400140d5200c0f4101c42d415440041040030454008030103403e064090414205d0580c0c9680c0e1034080300195820180d80301d20360740000381c0444d101b1600b607030340045980341010344140900042000004424011008500c1c4500205ca5207036101c9034071780700007000b128540c4060915180c4420544902000c00e001c001c0001005825441c40ca03080f5001400b82c00101d9560310200300700180000c80100782102c1045088000026004030808039034141d80079003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 263319352 1250 263318102 263318149
    0xe042a0b040b0711030a2f030601050d02010c02090c03011e180c0c0804030503070605090d0c14070b0304060605010e01020d02030d0c0c081207120e03070b0a061205010603060b 77
    0xc1d040b45240c0c01040007113030142400395500815440902503c0031480c800d691054100021800d032901d01e070302002d600c00400c464440c01003030b50b940c009209030458078142c83c032070034003201030004031070a510f50500603402172960018020104c3c074035402507040342c20b401440d040e00b01d80c42e07441c0b540480e014812280c410100950383c41500c0740651101d00289168141035042d0380540e61468069000341d8000d076400e400104400003401040e015075980904903034041c002c540740c201005400b0201c440c80251640e45180c0d06000302c2801041803134041d2203003061154803031801d8075146018160500896002a1401000d51404d5000144140715aa0590041d508203c11094000010480118910104a419440316002c10503150003801b02c21aa6884900f9501d003012000c1c2c2076944200c0b00d401100c0c6445000c141692000c803e5a2815500070100f06160b2140745804014003240c0c2c201d401c07507030b00900c40d8004002055000c903007164828030007480140010000c222007802d01e1854824103800c0c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 263320602 1250 263319352 263319359
    0x120a0b0103170405100206061021050c09030f0a1106070201050d11070605071707050a090605090402220f050414010506030a0e0303070c020a050604030305040501050705070e042a0b04 80
    0x18841080712806412880c60030169540f00003442d03119040c05d00d40150b00301c00700340306031411b00c001481c0b4030012500303180c07450030b0044240d41c22071482c010211507019900c1000c1070700b801450f8106d075190349000f0202c410b545040e031081910740d8401581100c200d41c3d19000d40d80142495420b07110207e03016110107050a2000303154202419030000106c000b07810400c0074000145051180c1c034080e038296074816001104082e81d01c9070041c07010b000d800c1403044c0bc0c090500d19507407118114023074480c24a4400d44030039080c0b01041c080d000f0080c07400030101040c03140c18a4210702c4408102203840e10440e0f5500165035500303000440d040603d00341290b0094500611070707410500300a50304201d801800080580d08030b42103070f066810035102c0f0f2001070300d210b501d4402e5262501040d03006d4001100d001d45010716555010703100744698070a01d4140003012640e0700030300000303004100040120240d40d000500d071a24010445a03001859a82c2803402070301c0403124031850105150546961091a034501400c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 263321852 1250 263320602 263320613
    0xd091e060f03060b0304080318070e0a02070203010e030d140106050a05070605070512011512050c09091803040b0406030c03020903120d201218190609080315120a0b0103 74
    0x510072040141529218006003030381ca490001c40c0b10318040c0144030340744d040c007404c0b0150b8941000000b0755282c2c09003505102c1e62502109a0b03400010780d44c40142c8d92100340c408240034000814000c0a90f010102d11582581403d4000744402c459012403e803080e83ca0f07501c2501c207805a0046200094002c0c0030342400961158031460b003100d824100a8104909200e200c41c05040c26049003924850003a8804d1a907500500031a6607543c0303d500c24401031074540781c2030070a4082d1100e42c1317120342003420124040d103071078400d0313115544640005e82e0f075210344817146951507074414440c00b40000c0c90300c48114900d5100c0c2c0700343d5001d4180140a000c112044204145103500000c08004c40c00341d440c182c4c61801b00c040101003020f04500303c201c0303480744010100c1d0000007070001c1440c04175070243c800e146402c10000c50301007892461f500310009070b072145041c960010640303090001c041c0d00c4000184489902034501c507002ca070300c0c00c86203a052040c031000201d8894054000040c050b8002c200148000341 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 263323102 1250 263321852 263321867
    0x914030c0115030317101e0501020105010605070201051206010c140f0c0d050a1104060906120c05060708030109180f050a050d09060e091801050103120801050f060a030903030e010c020d091e06 84
    0x341000b0301010741765240c1110b60000c55002c2e1300c7c8450714903110010040b9503020f02402e070060195040071401d00585400181061140040c15000c0c07821a90004a20344c0c02032800c09903051308000d209146a06101c2580d50b03500300d1800c1300308a0b00c240700007803d46140010829010781e90000140c100d101da41c3d982c400b0b0740e03500d00310002c1e4000e842e007002040000c4c0c98411540104200d501c1742c500b104080c140840d0705911500312a0280170f04001c10f00124504a0850341141c00d80c190000ba071f1081f07500262800741c00100004c0044e80c4115420042c083c00051100201e030186003983c9082d018090b00f0b8482008a220b4080868a40c02c0b0203200c0d45010680d4070341c0416016030700707100704a509405a0171107100340c004a030b03c041c4c0c40c0422502c49605c0390301c1c54054a030642d02e00b414160001700040c4580074900e000002c01d526442e10004040c03181d086512141c2600d8024043c00c0c824040194072040c0c1e1040020010b640c910000480785031500c03092b148d8008401c000d450301030904c6011250903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 263324352 1250 263323102 263323111
    0x200d03050c120a02012f0403081806070807060516020d0f0203040302130c0f030b1c1505040b0108010b240309120f04031509240914030c0115030317 65
    0x14059444942c0008000c4002080720119540c00080c41481e842c0044201d1041007500c000c8030345102280d61002035000d011502526041036045440302810900c081004006410741d98003c81d010884c001082203400c06403040501c0307000c05000c4c42da100e00d0283c84410081d0589001a80031840b036102445c003400c002d100303900103441a00c1c941a00d80d00443d40c0c441c21040070144956071000781012855204d0f40c0b81650b070314545424401680b61070005000001031034814002121109800c0c0200a0079030380d01041c1007400d181c180500d00e01400c0245c0d001c1024402c9600b19400c14a603a042440c120641528201968119039010071510b9030220740f03900b00402100700b520030054894001021140601400445011816580c90961400c000124441d400000d441070600c01c40c600003901c103040007913000000d5500f08174580c441e004104060322544101805a180041f500c00d004031020006150200c0c00d03000074455080000110342c0d0b0f204e11880090002451145c4031107803110300c5040950807 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 263325602 1250 263324352 263324377
    0x5061c0209062a010b0d05060114120d1205010f0e01030816020901090b03150108100b01090b0a03050103061a0603040605060a090513020102010c0206090c0f060d020f07200d0305 78
    0x4000308110040007075041e0071007811038100f000c903c0442c0385409004016620806481d40c0100340d0580e41c616503105018000c182840c11260039403501621800d070702e282160480d008a50020112280251a8591a0150b802c0580c05c00c0004101c141e4001ca0000440d10709007040c01c0103030b1860700c580b060f03074120848100a80c0140c0109001603914203040601a00300f0101c0010000102c4080610b4204054181c01d41c940c99080100700d00c500c00302d01c0c01c1e0701d12200030300072450400807070048804003002c2c2c101070720300e41020400003d80d075415031006040c0c0c0e01c94081000a100e17034240b20041e9140110481d940b12400300006000601c56801032604600c016219100c0c035070302e0751080810b42d00202d86c0710643c200c0624202043d5a4240242d4140d045107001402d210f003000070646403107540c2020002e004540c510000c518a4545500700c2d182d0350b061700c00c1151a00407503d080d64695200003000d039100e00e11070095510304070781c0c1001c00c0300d9078038001c1481034400c1c4950b41c252450341004410f00310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 263326852 1250 263325602 263325607
    0xa09090b10141e030108060a090309060c03110601081f0b1f11010f021c06051c0201090305060a05040c060e010905090421020309011205040b131e06140105061c020906 73
    0xa4140c07038003c0000401003a520071139203e43c1490400c85c5001801041d0b140254106284000882d0304000d203039055035014500b800c00c02c2454201640d150074080082407281c4a02800010340d003001080056400100c80d0b502080f0060400c030440503030303407010b102503405880308015811100040f000703842c0d805e0940c14064505801040d016086031000c00030286415000038100303c80c40c24101d0074410145208504002e050700b4400461216481201c60290341121070007000d05581c0900318940046a203e8100c54492030301c9038040001d01400d85e0b084400240030300700810481e0080320f1110100030181c4d20f02000c28640420044081c03800717082614400140300760300c003418074400328a43c03000344e00f03400035a0b0b034070020070004000b81c502c940c00c000001c0c50041031100045281290607001004c802e022081e20926080c07400c80d41452002c90b8000150840c4030300b08001240d00811003418113030541c440303141c0c0d8ce801445002c0c86404c1d50b80159480fa800041c003005c3d941d6024290104000c0d00d00c60 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 263328102 1250 263326852 263326867
    0x110f030d114309020c03130605070c0509090c04052d0f07030203180109050a0b06040c0e1504080d110105070807080414010b061804110415030c0c170a09090b1014 71
    0x101282d01c0030045c481150000204070703030810f080340c60000003031001e440c0c907620b806000d843d400b001003d2030091130721a085a9021804c5c216080000440c950401082044142040d17002a042c0050030b002c459544c40260f0711415129081054541c8158060640e04030959038805080340254030040141e0762400074405494030050091090b200810701c5907004086aa0351810240c04c440c0008080600c11804c01e01004030007548030488007160103050300c1114800f2000b01d45516240500e420032042da11910760760074080c1351312080711240a505400208042d4aa07050102e888100442d01280425140000700c4c00040c8405604000c4140c0e0320b00008569102c0c03400112561b000d905110450f80034401e81701c4083c500f62086221544150340440d00d060b16080342e1080500130701c5155400d1543c3d0343d40008409000f0141224055804050b5054203400c141003008a900842c082c04001407a000021481034850300c600410508000c04800340403405900c22200f1001c003000c400325400381402041c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 263329352 1250 263328102 263328119
    0x90d08041505041b17031c0905030307020a1502121306061724060306060111010213060f180605040b0a031e06080d1b110f030d1143 58
    0x83c0114414156201c52214011441c0b03030740200340e004840d003e101102509101c042c008121544050400e407440207241084580c1c10082c6500c9030b000c0c1035408000200aa101d5001c03885c5503400e0f01c04c0250107840908000031500724081d202c001d090102008002c19000c68000580303404a40c4150008070742e660f11036079691680216004558a075034041310902040c0070b02c4000d80101c3c18030710340c840c074440c0c6412400690b03241c1f00541040c0c1800364280402a041400f0f40444440c9440350308181c180d26500c2e17a0040115160060441c00982159011030580c0405114102103520940e5940c0c242414880b40072a40d0b403004c3c12440c2031650350445040002081078006820980c00c520019625140000990604041c409400e0401c14000e80403c4031100748900b0705c0c0c3c0389030003c0c80c03030085040d04000720780100b0351206117990501c00c0c3d5089a504685c0700302002c9441c0307025010b0340e42d0707045000d0f4080c0d41281042e1020310f094080c58000741e0400000403080c1c50350032444006142140e0340750b001e03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 263330602 1250 263329352 263329361
    0x90625052203030915110c010318080c06060a0e0601020601030605150405090601090509072d080109140106050402090d0206090109050a03060606021605012001061a12010e090d080415 80
    0x807408501101410410020903600309510724842d030401280510303400060a847d039084602507414980d550b00d400250903258103a80c0d00e4603600001c0c03030350740d10703000c18025684600844a1780c0c40380e1a40040861a54440c2030f00070b00420301a001032034540d007103980302c001800c0020000180060405881d91301c41d5968000c0c40d00039220040901010350400ca850410707100000c0c032012150303109920810510164070002c42c5000c03603a21000a40d85622200501c1d001e040340d11003005c540c00c0650003c00d22094059401d02c2c42408002007050b550f07a00c040c80141e00070b001d00258041d01d034441c1000903047c00c100401c030040c01403622a11080d1200d000841c00001600b05450903030740c40b0414451f0503010090911506e241c091203400262800000800a035041c4007449072400c03c112060301321400035000000a0021b01e051031008481161052031683c101c0c0c003002c0300c0380700030800008000c40c8c0401618000d00e0881d000c1d10900d01510b80945070b00c0000341c000c0b0b400248031034824642680c10f104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 263331852 1250 263330602 263330609
    0xc070e0114010201150303210203150103062102090a18030804150605130c121b2618030408060c0d1d060703110403060c080906250522 59
    0x4410294140315088258040075100715056a150540c89160703041d848010804a941c94501507400d0044c244a0744021100c0844d0112071a0000c42801980705500101d00b00c80c900a98080000356914881c2400d6046070721000d2003103449002c108405030030400e07110750b801700207883c010449481403504144540748044080e0006854141444104419030b01c41c0400b1081c2c0780c00910440e03080c04001480f841140c00c400844030742c2c07000044961030141200440203441144e0801012801081f543c21054103440c0300d000045c06c0c3c6945104003414180e2448003100c0003144100d842d41c440281c2c6903491050403480045110600000030303106010800107120301c0f5652110764031400446941c400765608244200320408200601540c00b07500041d2290340080d181c0b0303021840b10054031050205206540020704224104041e607646541c10060f140c4c0540d103507000b1140190b8440031000b5010400280d070b0055500c0c04c52140d400d1034401c1000e0070403d119014101240003210910101d107105991 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 263333102 1250 263331852 263331869
    0xe0103110406050c031201080a0314030105030615010c1a010611060906040f02010903080a170106020d0c150605090903031803030411040b060f07060903080c0a0215040309050a0905010f120203030304060c03020c07 93
    0x9e000301019849a07140500e002a1501386042d541050002611100000e02d02d90042c04079120f0450140c0c407c100b501d017101e410050700d40580c07001300e500442c4c1203400d01400e03003c242e0318074000c110204006103940c0f1680404001c1c03c0c0c0b5481e10303910a2400b000b41c20040c0e0411102000200118124800420081d02291a0801c8100c040f036007812200e541640200309540000180810b00d941000c002c040c2030f035011034910131480b40c6441642c001c2505411540c0c02c60340d41f1003007002c1d07070000000542c083c0d001740d80110300039803a568a1035590e10040345d00501c90741881580c44043d0401d500b200803c2c61004007054140070408007800956081444151061501ca049000078503070025109a00305c42e18516091030900c11002c042d50341c10361000e03400d6000591034005424140b09981101c05010f004158010b040d9840e00521302908003030094240b095003501e400568a0043ca079a0f20b03c0560181c05981541d440c2c0e1105001803c15100010605400b0044500f4603541032003268050003100b0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 263334352 1250 263333102 263333113
    0xf040f030302010f090503030619090e061f03020102030d0e07051513051c0b1e0903040e0702060403200a020a120506130507180207080a0c02010e0103110406050c03120108 75
    0x41c24001d094425a12034070440b503207000c0d08074001c204080101e0350b02401c01e0742c4440d5160940c0c0c017107200400300c0b030b402180c04600d0090031041c0c005021803600d000b5084170400c03040e1042d0720600c2082070183c83c4030080c00360703004110100003400150080200c26141c00c0507141d24954070400f060340040c803505081d11511000413049030310300c01c00400138045c00d400e4858048101c0c20130500c9030301035141040540600e1001000030b454840d042c0b03001c88034122551031645542058800956260800d000b04107100d651000000c10342480050540c0c400c0ea010307070790741c00d25025052103014106102155200e00c1d00505801c3c00140e220600800001e040941c0042c100a20a003081414020080d01009c115140c81032000081840041d19406441161144640300300090001a000303214240c0300070310482010440000d940d0304006c5686000e4000c0e251102a000e0440046084681c982d292100b01c4806100612006108101070408451801d01b160700e04214500e4502c1c40c52005d034404c5030b050b48a03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 263335602 1250 263334352 263334359
    0x110a12080105101106070e0a0306020a2a0201120c0e0d050607030e0303040f0b0c070c0f18050601200c040f02030711070b043c091d07030807080f040f 66
    0x5070001c511280031914200040c49a036600e802c5d11040040c0040e0208441811486004d585901d408802542d0182c4215a034090540300a04155424815000e07251118501c0010f410046814900442c0d4148d444076014540c10355030000500002038200204402d8020301c2c5241e40350046401d07103141c00f034002042a490b00310001003e8500c518010742d180e4106200744000200f12043c0c85500c650310039565082951a0307a58903045000740c40001d0140e01e441c800001e07190302c01006100580c0c50503000144604a4101a407043d5001507403401e0000b205a03401d4124000c405000346510810101030300c80b4140c0e141d002030141c400f00000c400c20f159000052208180d0440a00410b00080c2005400020300e095004c0900e80078030b10506044100700d441c0205120b072020900e070842d0101100c000e0207001d0f4070720303c000c2050085c0501102180307401c0529640303c4118503100400c2d2210002001d0550850b500d46540e0b8102d420111036040050140641800c401e80291018009810070704556078034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 263336852 1250 263335602 263335609
    0x216020316081504030311040b070b0106090605031503010204050607060b090630010906020a0c030e090603030a0c02062a060f160e0a05030d0c030905060901020d110a12080105 77
    0x102000d420504010040302003224500125003690f04000c4a000c50b041a681c509056001c3c0500c6484107040e1240082c004c51404101710107072003243c0c003945085010303a80b02d040503a010902d070302800740844c2041c0001840e42e441c0803942c4030f200002034009404c2c143d691020400c641c0009904a0301e40751035160440c154102059015486881110296852240005840c1c4012000142c09a440c540d1001e001101982500260034950340004115030322005560000e122503645030701140064218014a1480d182c003110f5a070240340020b02a502e4580d00103026079250f62480c03012a040001803141002c01000006500d100e592040385203000a11080070040c1070680003049202d41444044c14070103030100c182005040c200780c0e0704000d803041000e4030014030190000e0340042c1e898402e0044610450341d0000c45914064400d0700d41300409a180d80400a1070f000d5020000d0060f40944c4003482e000d40b0440c0aa060020060141d580e81d0403651070302c0e90b419031400081c101107030803003004205d40d08 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 263338102 1250 263336852 263336863
    0xc09030c0f1c1109010608090f010b01050d022104050303090601060219020f0d05060403052a0c012706170c030708010e0901061d0601030e0f03070f11030102160203 72
    0x10211054034081e10010005081c080500c88441059000e4000c944100058070b028000c0b4800c0042100000350b9560600404400341210340c654540681c0742d0413104030303070305004003044041d0503100c0380e0802202c212440e00035004200c01e0a01030b0203150070484210f0740191014001c0c1e0040e0701565030b80c5003058200386025010381c000c1c011540300790300b015440e0754084020541e080d811180c1031801043c0e40c0000d041e9221100300a00a40200c1092004143c0c100c00103001544130149038500b91615032950382c20f00c8004c0482003605400c03e00040d10250302c603020b442c101c451492100140c1d00740d414020111b03040d01d50050f030003142030060080485800b84400c980d1100035110898030b1860400401000c162040c481c203064503020001140c0d00342c1d401e412a40c05040218072400103041c010320040303e011070544005010a00e80640301da620710010403d400003482d07075801580740503a5552040c414490355002a14520100940001955005e000500080409201f007940d010319a004141c00c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 263339352 1250 263338102 263338123
    0x30b06060412060515130b010f020307030c082506020705100509030706050402130f0b090c03012105030d020c01090201030b03010203060109030f02041515090b04060903080a0c02090c0903 82
    0x302810300042258241011480c072403590b1041c40460103071a14900d03d24031682d030300c070100c0e84600d02c26030078089015035170b110600801090380d40f2003144407a52016a142d02c19030303038050001815094a080410107540c001c000e81d120781094800d140c88124031301e25082486a4044070b280341c00040d450b05124041102868000c1200d000700010308008001a40d03a1240500043c0019203820000d4155500d200196500500004e02400b004a503520900f000301081d40c00207106c0c1c02e0110100359200300c1282602d0684900d4164104c0c200024006070140c20300b13090713044600f84400c0090800900450000e4403140903a00000705000d51a0310014098484000841d0300070ba00c14410861a40c1c0d0028040c012690014800402c1c3c51007400800c0207011400040060f000c203002c00000c0a1104141140c00c44d1943da4500301403e46514138a1100d120300c0c0710708030001d881c42034103001082001c0020301c1d80076440d0900d00c4003031159030301149620714100c4550658410115000485045c140700300a041c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 263340602 1250 263339352 263339359
    0xd02180708090316020d170409020913020a05120c07050102070b0106020f1203060d11120a0b0907030506010b0a0c0506010e0a0606090f030b090a05060c13060e180702030f070804030b06 81
    0x421032029000e4a40d01201c100107403003841c90900b42828040b142e101e20300da600b1120940762381c45840c0d14969000c3e502100c3e005001e080b9081610031640c1841c42583d441c0396041d070302d0718030b000289800c0c0303441d41d031000c0e100d00ea9414007000500300044092004120307442c8030f030524020329807412501a0500510b002d0861054101d1088016402d004208030713980304d88101c680400310840f07810f003015005024542180c00964411258620407400560121018843c0745040410395074202196252007071840001c0c803507030001c0700501590504501418a400051a090500c2e03483ca485d2a46890310a82c0000089048101401514001070091401400d124103200da04c0901c0c1042034441c1c40210b1202805115840000c21401e034018490005c1c034980060440709107003041c0201007419841032500007003d88848100241140c092041d00110890003000700c2c4611082240383d41c00300000400c11011800b00b002200351111b0b184c4081e200043c09040500c0d1618154501031102c881c028003050310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 263341852 1250 263340602 263340607
    0xa080a121b0b010608090a0501110403051e070603110715061815090509120706050619080a06090305130303210612170418140f0105060a05090d021807080903 69
    0x440c04800081e03044030071500d1304145c540d4a142180307041c00020440240b20f5420b000800d010003102102401c1a40d008100780c4c4c8000501045200c400900720038600c08642003c081040040d00030b034005140c010b80682428940b2005c1e0307403040c902c0002450307500109a80d4010a2282c5c1041e484042c81c0c0c8464020b0810000c4941c03a1258210100741c42991000703508c0b480041d5404038203002904000c4002d0101c20f80700d00d60f902c0c040c0003911048072a81c1c0100003d5334800700304003554480d8007c6a004c2d802404014400d82c40b81400341c02000d50980500001b000410000d8040d40940302c019800307961768082041481f02c800e00305000507444450b44504001d01880500b2001c90b41d0120030f640000001040f29062109020391b0185520000101c0700d205292140410641c00580010403241900095a81d0328506103440300000e01486401040c184800f10b10b0341d024200500c5040002081c40e20341d078200740d0001c0c505c00781d9100c00b180014004028043c49603005110710ba007003e501e42c044c50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 263343102 1250 263341852 263341907
    0x2120c0310120206040905010303050c010510050618010903020901060c030305060d050705060c150a020711100906030b040609050112050d0903150f1401090b1203091309020a080a12 79
    0x80c00e1082402203030a20312400300300400b1503880f04e00301e90083c55040c409003c02e607503a09020b070082c0c200300c03404a860b508044c00207440c4c130310354480c481c10350b0750013041c7c64100011120032284000060803018140b05902e40302001594a01c01e0745070003803003c0d80d80c0000c003007841c0c50010282c2d030019042c3d0707029110034588032000800118000342921019103046440380f408000301460711000f20720350780203550201c0030b20117141c00310703001817440c540240c90407401242e40794103001e14aa0802c0107140043e01200e020300400c0d00c280c210341070742d0400910100d5450f413114650000c503142030303007c0e1175048800900501084414406000c4510460621002503071841e00d44928a007035481040c14041d0f503960301c200786044e8a03800820703c544c0020303508085684807850400144200000c0c203121300d58810056803075040c000101c49510341c0c040c041786108912110001c0c068a140d0750202d80c40400072a0204081500300101c1c0e0f9400c0c000c4202050105031b02e40c1c080d11002038840719171149080c02c075690 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 263344352 1250 263343102 263343121
    0x3020405060702120a0b04060902093405041701020a140a0509010513030b162a020d0303060b0d0207020405060f0d034a0102010204030330090602120c03 67
    0x1281c0d82c9806940c1c00c01d900d0290500b003130404040800003044c1c0c10b1088240000d00800b40c0c0000b0010b4401e0b2051003191300c0381d0b142e6519280d030a810341010b0414a0b040c0e140011381d0501781e19480900c0303080603400c05448104421a54003504840c1581e607501240741040039501c001003140843d502c0311800e207070880c1420003c10724400e18406070b051000c009076800d006010b00c6d40c02d400440d00100c041000b4107144003106c010020702980c00c8001100c0700021303010080818401c2080200380841d1240d0480e0380d90030b0080f050728201080c0c0c24103603134100005038145201d0040a1a11750411300580c0c036121441004101c0d603004d80468080c054400410140351603400c1410905500341c201109411a210026681a40401503034000340095500c0400c2c0d20281d0006030090f508100000795804590000480c00c0380110311015001500460480c031031005801e200e890240d800f038204800055104620900f40d0306010011180c4550000d204020b88490591007034002c10810a804d143d420b001d00e41d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 263345602 1250 263344352 263344357
    0xa05010807080c07120f0e041505011b0501050906041401020901121a06180307080a080f030a0e0601060f2c10090302040c020109120c0b070e0409051e07060302040506 73
    0x110014000501c010070f110101c034209a4070000d0388204d03090380384018010000e107809501c4d00c0e000c01107850030b10485518a801d01817032080165500c1500003051801004480610081c10444e03002040700d1000302c0865401e0003224440c0018900828103414545854040d01d800d019104030281d205002c0e03448103a0348810510f5201c1d80c1c0c01c10110303011204d0520800c1c3e040300085c0d27095102000044060084e00800c8010b442110114151042c2035a100d0380140c664158a8005100314000c01c505400c0c080900b0207180c010446040010391007450101031450030703030283c00c0000860306504c060003606610410390f40d118480300045000201240b0004100701400f41007140c4203030050a24500c1c4584a00200340065400a0040c0a056804d0801074024070000c00290f41e0001020305846100b07000d1035601440c2d65110741c01144540d55034200b1500c0e030b0040d5003103d5100e502c1e0320f03600003c900d00300000703038000c207880c024180002c0c40e0749403c0d85082c01d40c0d40408203050040c003081016588000c203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 263346852 1250 263345602 263345611
    0x30f011805071b050f010f15140a0303030c0513080304030c0b1303060b040b03161a0a0f030c1b140607020705030309060306010338010c11040908270a050a050108 71
    0x120b40c0d034860081d107460b504005c070811000925629280f03003c000f100c42500103032142c0501c2004d00350f0349070302c841c18410b400012000c9140c11541159080002a100707030712200d500701c80392a1060a00d484443c0c3c0327030101c0d500e030741c41001150f001040500500030381c442e405000704400c0450701c2c5845440000b1110201840c800030b0a65070f940c011030700e15521590849000c8030300c01010381341d04400d85489a82d04c0480350044510380307440c403030040084030303440022521502c02035191540001d903014000c8000d4243c01885d10200001c04258510040e41c4208100040e8418540c00e1541420b102c5e000349071000040040b400c55000780420410707a01c011003202c401e00415030300c8039034955400b030040e4064121481e002c0c46185a104292111400003807020040f0388070030500030140706200700110f40d0203c2d000009011030107a803c060071940f609500c02802540b281c00742d030b410101c1510040003d0324180b06a4003140320000400002c615200b810b510184c001100c1c03540328613051100080c07403d40000c0c0f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 263348102 1250 263346852 263346887
    0xa050a1707050d11010f020c071706091509100c02060402030d030506010e1324060e01030b0a05090a1b1d0306040f0b0907270f05040213091403030f01180507 69
    0x7134100052400a40080824802d41c28041d50744050040d100e5945090f51b100b0707e040005010200d014560f0081090b9004140c407000070940b142410003100c5000704040c049881600c69001c150314042c1c0180110042c081154000e0302e55440c1c1070040c5410f15211054003420545850100100781ea00030a52198001c1c0940300741c504a900682d5550044c80c00109880102d00700c5400810042008a0342d4001e0b11000e40d2030f500c0b92090f0000540568444d0520b09501013400001403001d800d0803a14940d0101c1a494003040303102c038190400c061030f1100d00000e400034a0444ca0854100918054a003072080141c0c0245158606510742e0b01c1402164000104103005032000f041c01c0039420040b0102070207911580c4100041c0c484240e58030500d0701c016422036141442c0594100310130501c1078522585c1c01604200780e009a58203107000802c00c00344101d0b5006480740700d20810741420805148540b40c1050303a0344195061941d40408440e110000c0b0004a0500301041625a8030011500c00c244020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 263349352 1250 263348102 263348117
    0x50922030329011b03020313030c061101050f070c030203070c0f050f030a0807080c070807060f0e030c0f0f060f070c050405091603020126101e0803120c0403050a050a1707050d 77
    0x246002c80c01c62003250010b8821658180e03010090003500b4ac81c00c82250401c0d10345030820a41144071900b03030740040720501c1c000b8800d007002856050044030303090780c003501c82e02c1660724286a69a43c1d00c4240c0540d040240300200320481800142031444e03440e4a034180481c0284600758666441d01254400c24100800b000c41c046681944503070300308606c4016048950940d0b04a94407071100900030301d0380c41c07a0003001404d41c2200040c507080200e0240e0013904040c0c544402c1800341000c1c04201d076030142101c2e422040030454034104180460280246520544032000045e2a1108200980d0009000c009098201030805200fa1040260a100b101e42c282404941032902070281152036003042d010482c44640324041041084003802440c081e00c5601121942c400504102c2054107a5a030085d080964410880515520a01e003115640113500d0768115180a40b02d0342e400d41010000401181c0d154060070b00201002032010741e4510380f02d0725894080c24800651901a0f54501d901846014030000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 263350602 1250 263349352 263349407
    0x90f0e0a06230106020a030201050105091509040309050d05010207050609060f04060f0b090c12070207180e0118050a0309120b0f0a1104270203010f05092203032901 72
    0x21002c6400031020800b002099540c2e581c200603480c2d20b04400c0440c019440c010002c03035185007070000280a820694080c000c40d9048805010714044040c02c00e0303062281650002840303035200105261014440c60006d03031076600b075140031458000040c01d541c20a0304001c040100175800c802d19980e2007030700400042007807240010001d0003892124601d58204003071100b007103400844800101050b180a039003c0702140c2c2c40510481e211260342c040c005039021508440c030100364054100000c03d0b0051000000e4200301c20000c1c11564140d8103003120141c00c1956110103042c0c002041d072004010103041c0300c1280429a540014641e0f00410082d50800c1c0280812103682c016800060400701d5110720783d50326903c44000c03400c455441e00e001c20202061070080c4422800d540261b81c12074140381411189282008108012903c0c02081c5010001440102c020f9415013440c00408450082c0c4000480c00100c1d0400c0c41462494a820780c090382e11040302c40050f0342c0c4019a03c2d6210019203005407a10340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 263351852 1250 263350602 263350631
    0x70303060b030c031608090d0c0302120a11060109060b04030f061d030c1216060506120102040b0a0924080a1404111801231302030907090f0e0a06 64
    0x10035410030050041c010007080348100700c2c1030003140034048440003401c0082c0c50f1001111054411246c40060750810001c0003d0903000d40080d9070550701c2401070750b00000c115025035026420030080c0700c0c0043ca2188007403504020a0010502500050400307004040c00d10090074000d1045100040030b094900b205141408643d42c0f00e16050009601450f10312088415501d50780d8201700488140c2d030107604e140c1c9042c1d0101c0002c4507122055490700000341344030303919032000400300104026081101d6600800100400b84001c0016040c41101e41341c032040400802004c80c1050b4014001807200d24800107444030501c600344000b003030245411501c6655902c00c03000980860810303500c01140703620a0008004031030508280c83c482c247c800300b2107002c0210301c100d4158800e1040700f170f10035040c4280d80341002c8401d1000d5211003010344000503090b0030000000c00c0740e00403209080c8503040720f1001c2c0031080c0640580210502d00c1c0744148081104201d1594880020540040205543e4040000f0220f03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 263353102 1250 263351852 263351861
    0x9090c0d080c0f0c03060c070f080705010207080c060103030206010f030305030a050604060b0403140c090f13110a091a0102030c030414041401150e150304030509011e020708160b030c070303 83
    0x1050310b0103644110001e00315242d03840c11180201071184c0655000920b078140040103564245400030111654000c090310740a120740d115044c01d031102c0d5006c010640100d146500200403003030315100107040c079600d903080090a00e001a006101c91000780c00042011079803020580c0d0b08007102641c000b85039107880000400502c0254401c2203004400f007800411301200714282c02c030030030b08042030301d0302103110070f007040300c8003808540715111240ca0300081210414100800d641c154413880f1385410b0000494000b41c1c00e20b400c0e034800c0030100d4039440000703205445030000122100302800114142188004140d13141d01842c060811042d083d8980000c20b41d40f036400000c118000c25030b4000e815611003c006000241441c0f1480105004041c2061941807464501e8800090005114216201c50764101d48903408060801e04200c0c41c8681e08441c52010b414800700c44102d03800400c00301c1d18204001e4100106c0d2820341e55189030024040050058101c200c80d801180300c80e40301d980d0070161400390000c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 263354352 1250 263353102 263353117
    0x80f06040b0909070e010e04030507120201060f0b030103060f0903020705041104050d2604120303021b0f01020a020f060f07053105041a0120010207050114040201080609090c0d08 78
    0x101002c824021603032804610742c010768042a9592810743e0b00c440d69240401c806a4000f40007400800031100420f408146000350f0075010320020a046680703180608002c400b03600900c4030741d40008010003c00002c0d2086080d00083c0070b030103010f09600e5403006034880c6403d10455000702e8503071106c40c99003c80101101c0280100900c00e909100a904258000d41000d081c2e90845030701f17200c1401410300c003090655049614281298200c801281c2e0118060f4101c0c40c4503040c0710501d050206d84000b810320441000c5450b00c00010381711030103080005c5c0340c003004031040300040d048817050040c010513945c581c6030f0110507030078440c2c1e840c00c01b803003061185440942e03402c0d594803920800c01400c640000944013200c00c1100c05000513528640107001c0c0c0303a00303207481c1c6010a09880e50120b10086180031900003406510005040544d1078072401e0a403840b8044051030264440d00b017200f1507800c48040d41e042681900c4110345d524040242c144e6a000d40428544507020154588041010f80300444140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 263355602 1250 263354352 263354359
    0x60c090909111c080301090c2f06010611120f070812090d1e180902040e0604060806071227050c040e0c0303040b18060a0903060c0203030403080f06040b 67
    0x80d5005410a6102d28440300c0515100c0e43e51145070101d00003d0700d080410041d048482c01e841d691a20709500010144480c412060003a280c0d03920781047c000700d45003030301c0c118104440340b14500d000044a0804505820007000d1208404c42000080340c00200010014044480c05a0b90800181014550f02071401d00030038503903001941d04240003d88201d540908140360483c2c0c1d0084940d40c043c2da41020900403200407016140840f84000d1044000000f110281c0304200304940c0c540c0318800036644150099200d5014030740500005003018442c5000400040029087c0c03428010b000400d91030751806800351440e03e80c403c084140c3e20901d00410521401541c4448088081c54125125003000214510583c5401610b0b8900300300030031020140c04004000d10324050502c0724808454000707980e4a03044131829400071300281c0311100205101c0541d42c03a0010507918500d060015241e401d050300c01190418810f01001035081030b4202c0c2c00070400c144102e41da648440c0817500910200040607071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 263356852 1250 263355602 263355611
    0x515031c03020313170c0c040c0c030f12020c070816080c0607031b0b0105031510061809022802010204030f03080c070b04030815010e0303070222020406020c010e01031404060c0909 79
    0x417600c02c8002c0c45021682819910820814400c20003110000300b026800310310000400c0d000644201c29110700b40303e40e82800140404513a503200100c1c0c001440641003544501340c28040d103007040103070000c0801e040c00030300720513410079410b1a1691342c03455a20340104400300c0e100c0304060203000401040d02c03190f01b99013481c00310741c01d00c411002000e1240c10b00a0007100d61a8a03034011000340c00d403040450143e0720103800c0ca0074204880c131a01c1c50391001c00884030114045200b040c140014824400014007000681d00c06280c1c4a40350245d80b00d02006581c030400c010000503494140c10031383d40d505401c01441c259078181c46560b05200780c0310001d1200003501c00f008105900180f0050140f00207079503e01c400104000155048007503026095803661040c41404014a003400041c1c0e0001c2241c007500d0f402c11403400c0c0400076078100340c21000160b0041448407120356403011107680361380c07000d2030300303012146142c002c524400e28080e10260006440314040341c40a03000b02000001854076410410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 263358102 1250 263356852 263356883
    0xf1104051315090e0601031106341a0609010501051201060c0807060203090109030e03010e0a020910030b10050102010f050c07030c060b030d0903140114190b060a030515031c03020313 80
    0x3d4071517200740000c0f20040c0307411070029a10704209084c3c41c56141d254420a00c03089428121008260f0b4000050341840d24840c0000c0000c1c8078240007013440c11561110240c2403c28004100390346005810542c1000020301c010683c9002040c038440c1180c00504101d501d0501d241414840351040b11000303010700b4000024814601815804080d0090203a511038100c40780c210101400d80d4044809450301d64011600704d0701518111140b6a00032071007810a198040d034a0352a10400c00c021204140c075007514003010402c0b542c0a0081030f100c00b0070040200807a1511901d54041400740c024041d0030420b469890341c0404c8034a034041f5442c41401021110300c01c400c82d10080041c041408200c50000700d050b04d09501801c1401f07107110003919001614155540d44400f192004002400c5c001c0440d140d1162407035a496103402400c2080643d07070302080900d0f0000f0424600250918000d00070743c42807503165080c21102c8580c0d10120100d150141c1d6070b40340c00300d21481440c002c800c064241001256000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 263359352 1250 263358102 263358131
    0x2109030a1e12020f060601141c06090e0f10060e0705160501060f090f02030c04120809130c030e07050a050d0c080d030e0607031806020d1805010f110405131509 70
    0x1303808201c022143d441d130380e14004581c2a104282289881c400900180c2c0c4e003c00c1500c100f800c00c880c0e080d000251140c0d078842c4401034807890984400e084d00b1855213803448e0b030001d10030f842050304084c3d010300c02c3c6ca1900b180f8685032000142098200100491100b118680c9582c001c4400d940003002402401d49070b0040d40110440e0748580466149481641c1c84d14031414000c0d2031040011090306400d0501d010081402030400c0031702200c0d400410004a0044d40d52441200d0400f2110540000c01441300709c0060101c4819125a1000d940310400400c0700396950442c150a6a400740d6049450020300e00e09082241590f81140704180179040701d142009500d03901c0b05070840703488000c5170510b8440200039011207408606050612150740707624030104441c0d03001800e02481d003c3c000103050320861501c141c69500d00c0c004485c1079440e41846040003806004a202d6010f244510321f1416242c00f00041c104408072625940c1182c0f40c0c04482000507034418100c0040c010760301c003407000d1801103060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 263360602 1250 263359352 263359363
    0x7030810180209030a0c060315050d080318101a0a0e04120f021009150c0516083901060f0b03060d050f0a050d030c050301140f212109030a1e1202 64
    0x727a600040c10424001400e15140f84c45c1c90a941d0014111465519011400203100d00345507401019403088800203441a00c0368802c503501003c0000c4041c00d01d41d0900100300d00d44489034405034100c8400024007011554070321990244100a05261092105c4104141c3c00c045501c3d14034410540307804150b000344401d03460305083ca840c00721420421001d441e2010344040c041c402444008448040c80d90001a96a000802261214100c0050481c10405100240d00c070500c3d015808695108612520790400f4021003020781410740a10909906049201c40d260000411240c41045060b5900c0f051040600ca42e035800c5038a14207a031010303003050034802d5a40d00701540350000680f8044008000341c2c0300d030043e203040e0f40700c00810710f0000c41907d0400c2407070345450b85110345c08061050224001070207200c6d2501460508809803407080401180e003207401901041c03803c49081c0c108014000d075a001708040301d90711762041d00c1010500c1c030090103a911001c00e1800034481400f2800074086903400203078 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 263361852 1250 263360602 263360621
    0x5060f1503190614041703100906061d030304060e150708030103080a1101050609041202010b0603090106140a0303050417150703020403050f0a080d0b0d0c090207030810180209030a0c0603 82
    0x6042c003180e40c404034851900c0c038003105e0140c0020548080204c400ca44000110f820000007005074031000e859401d98422200c003035100101040c003c2d038511500b0b111044600d201d0b20001c4014505091900d00c0c003620102003005800e1241030b4a000d101e000350711150950703665540080b07000ba20307581c41c1e02d0020901c0c0e01c100003000c0480c10038032181488420500906118110240c40d580d401c0d29241d071001c01c07010301d58041300155500d840310b843d05510742c840176602c50503032a0004540b451808142501101510400c0c5001c2c864100050000caa00042198202c6190324603480705580d10491160600076013036901880d640c00c100504c29003d07819006802542d00602c01c1e41c10152800c1140c0d0303076030021050000d000e50b0741401645600c0e1016801f038ad0a043c405013409201c42034070750b01c4100010183c0c00c00100e0301d6010841d200ad01d6032120038a60f00c08562221000b546042051110b803c8001d400c250308d400d500061000c04586060200b005d4169108440346501038035864058041c0000c0321 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 263363102 1250 263361852 263361863
    0xb13060612051501061d01110a12111605040b060909161107120305091203031315140402062b09051e120304030e090a0b090a1415010207030203060108010c0305070c05060f150319 78
    0x240c8580c143c400403030118806da000c84180c1c00cd840c6081c05000140940c8280540d02480500446401e07480b006543d034070400030359038404c4481a8041c000342c4003007081c0005c00001d0303004000c10b00c4031108141500a44a4040c103040d40c49455220016500c0d940220100c01140004001d001c2418400c0c0d641101c218416040d4210400d2420f84450840e050100001e24442d0700b140440c015082050041811009909424214080121284130700050341115004115610114a820700800b03000c09110f40709400c0d101888aa0540e00055440c00004011a0030320341c0003011a041501400f071404019001070606449441c010510070010001101154020350708180010103101c01480b80d65040a20810400d06c9501c4096001c80761400b00f08000d419403090240100140ea410403051f4000c01d158000415024401c1c1c00c02001e982000e00740d00b003449100758000c0700091000c20100d60207641154180b0307032542c9581414140e074003694103081d014000d41e00b500e44411002e100100304a400350 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 263364352 1250 263363102 263363117
    0xf0603020c011b17100807080c03010b01030c050f0a0504050901060f0f091a031b0c0304090b03070e0c03190f020d15030b040b13060612051501061d01110a12 69
    0x414940d07240c000c2e0800b451002032028a1340001c070300504030809800601c200b607400e00c40f58582e11020310301003058221000c194005125411070f49024001c100e0111005c1c6018000d103031491401402c6402030030b07402100300300c0c003040041a182c41001540c009002c014615015943d54a001a1585002445100000b40003403494032402e4010001d400840308034001110144a00300e08101b03142d0800b404842019000707403001003100e0428805480c1034540c40c0055652030b441e0160030812590010f508a001307800000d000c121015080e810207620000c91450103550340d076004842e4108003601080461410301e041c010b11984101e03540945030f44a200c11080018100100d03000001549501c40104808440c4001900080a020320a50411490b106020041e038080da904000d80305950460341c0002001a09103090000800800030001980c042030356195040000007040e14091100000301d00308042480b00c1580d11411a08503100b0603042030303840c2c00d20700d40742254400022148040014080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 263365602 1250 263364352 263364371
    0x2150307080a0605090c0d06030204020403080c190203030a030911090f180c0d030c030c1a16080402030607031509020f3609062d010201320a060f0603020c01 69
    0x3d100305420358074002d1603030925035503030001034050350700016076400c0c9240c0303c2000000503180e50018001940c07040c01074949400d01d07009018035141d1310642c054030f00c681114000016841c04030456003080b001c0c2c6070206100850b4100301000b04002000a60030507120002c0244c44410201128080d480680078001d0f52090300850075528950009901d52040040c5482030003e8029480c800749584282403c141003c456112800f5181e1200600da0840c03460601308103c0c445240450003851149080442c043e0a0a4010030303a01ca000520000c14181e0318440c8024000721750030003c0c01090001400c5d9903503004da480214064014403001035112004104468400c48110341c0014450070901c0e0710b400001d10f84e0b04100e4401c1014103001e8000d0000b6484081ca014054901c8005d09218054005400810000242107030401d29030b811607103552607801c000682860000c503840b0540300131078100544903900b0501c004c10155102400c94010a000040d801c2e4054000d465041c0207a8000c2014014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 263366852 1250 263365602 263365621
    0x60b090105030d0207171e0c01080609010308030a0b040209060a0e0319020d1b09021207020d0e03070501080a020f131517010612090506070201021201080304062a0215030708 76
    0x3c0419501015030000b62044c4010020100d007004024054811209034407041c1d04ca0000911481540e0403103a04128600c44981d41c0000d0820780149040d00c50340c0941d0b1540d01d409000d400050002d401da180c032080ba1109550343d80d0152a415400100401e6903038040a0024141c04804403145c0c3c000d02030341e105000c0c1ca800d6030200c0d2460540203070400402040c1652500d04010710420030783c20400c00d0850206252110b41f01500f048074450500c292903003010700c000fa1820780f08003421410440028400d9800c1d403800326140c2c089a030203080640d000d8640c41c00b400080c1c010a00c0b1200c4048011452492002c0c9900c684401c8900c011401d03100c020104c50211944000d20162125840f9000300421901d880340064a03a07011169400251002240e9a684d00388082660a60f0050b900854800981c0125070711142c014078143c00118606850002d01501c02c201c000d400b002c800c42480f1107003016a91404248601035030061030715400c190b4146002a141d0415680c41d000071341d5100009080c1030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 263368102 1250 263366852 263366863
    0x210901020702061614070609090e07080304120203071e06090b030601021902120105070801090f0e0706080c130605120f040c030b060111011415090714070816060b09010503 75
    0x40d0094030749484c048141020791403011030311004585d21410000b840701100c1c01400448040c025981e103a800091819078040f007605c805c2c403124030840d0001c80301040106000003c80f42195111407112405405d50300001782441411b5000d0b4001d100240341c0741500352800c075441c20942e8000d440c0c84034129190300072255180411140140076900000c1ea0400070540d02680e00142407000303181c0ba4036681d13011a180e084d00d00c2900d012000c10300d03080051204825502400f0706541404d2002c104c02c1a40c1103246544038500d2240d901030004007000704080c002102c0403107e20745030441c4621755040d900c54004013583c0c408401701c0009a10200400c0e503041e0391001c00ca005640144605010900f103440e0300c4107258026150505003c9402c002000c100c00030300a0650b8064060340c0000d00349003040540c040607403481455032107407030150100600150010071686140184008203030320340b40c803483c01110398807400e58a03808030034007608040b00300300c41d903000740d042040141c8030301100d82d03680d00515a0341e8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 263369352 1250 263368102 263368117
    0x240e031308061027020a02100518061b04031b0305010b0f0306060120070602150f160806010302090909010b011709070b0f09090903030a0c02030414010f0201060b21090102 75
    0x1c0c2c450f41c4082048a8480000052081c02100515201244050043d0032a88804070020258000b86408a0303080c00d10300c2550380c011090004641c2c0611180c00080d00c0e45002000440003407001c2d461301440d484034906403009103074002000000e0318600c40303030044256044d1100f211a503081907031032000d40c06c22080207080104080d00a01c9251150f0005413001001a8a0050214000341c86200004000c02c413103801403159030007500c4056981d03c1d2030a80c6640050410904210050a001d8400480101d8401001c0c0b140740042650321401c0041340a4842c0d207101681c042504000d00110305810f51100c02c4080b401d88601698819441802819080c11a60300728141c2004004104945060005088124550309410325103140301002036803030f03407050301e2480745c40e4404400c006500705540708460078112103000560078a854100c5039a541080c0c101c050741002607195454003114000d4000001600c4982101a00e030201d0b01500707001455818501102c00b0b0000001c1500c401040c8200d4403175 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 263370602 1250 263369352 263369371
    0x4090b0a140f031002040f09060509130308040f0b01180509010e07120204060f0905040510141501031d03090a050108041203090c0e0106020a020f01170103240e03130806 74
    0x1607854450030009103800200c5a581c0501965840d850707604002e1000b00090f11145008848140c00c0904c0300e000c80e411a089180101108024030030035003900490040b01580c1071900055603034991130117400c8a502d0503001000341145900100c1c500f03602c951602e207001c860b040108525030703030044c1c101e02340e800c18407120ba6203410001041c410610350740e907543c014a0010f40003103021b40c3d6034440d00719002d581e0f80c407541e10f01c1da0740c00512003084010b00c10500c4000c024442800080840404030140403c05409d040480c403103031408840c2e40e40603800292500c01c00d01194a011020000c585031a648010300d0710b8891031520b500440c0c2c96001e0441c807401a90840c81e101142c9809071401e03002045558004e480101c0103580000d102114080c030386000c1c00096014156030092441444030700000744403401c5c140b2540300ba0074102703000c80c1c440c0e042c112600721134108031003c0b14036142d440d0300401d20900c4a03200e00b005061a804c410000040c0540822615000c9403e0b5403683c00503111141074424241c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 263371852 1250 263370602 263370629
    0x30c0305250e030a0f060209012d030902010e0405040609020a06050c15070504031e0c0909150b04060f240504050a060c02060d02030f1509070c2a060504090b0a 70
    0x90541c0308403100c03404004050102c0344c0c1000380da00d80010004074144203e034490f4001901ca541c5590060f900544120201039500d8036500030715030440c15540048240040580e9000e2510075a03108582c001c8560501400c1000342d803c10342026409405068016400350841041c00110248140e081700c00c5280c100c0042c20000240040c1400c0c0c9010240511080200902c008000702c1c100c005040032111800410481000035072400041000c92548101c01c0107103400304810102d8501101080d010804100000c1c80d0302c4100d000400402007a08030240364001500d000c120b84c2d0b210380014070607003c05960301194000d8410110ba8030b22490149580080100f5000c01580d13021703038000d4450318801001e040c14070f941801000120380080300e200f03d540402c0000e21111041d20214200259001d981c0341c401442d09280103014145003001c02803011506600328114003e040c0d242031103d0903004942680320360b841c4802403e0742c200380a003418042c50001ca0041502e0010060b804527443c0098400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 263373102 1250 263371852 263371921
    0xa121803031d09010608220809062d0a08090703051906110a0302030601110d09060c110301020a0806031c020c01210603150c03020f0306041d0d030c0305 67
    0x150024840e0040d0140429498040c1001d96507007a40c542c06070201b561001018034040703003c148142071050704410065403e16402012484101c200d990a08068418a640c1c6c940d90551842c485020f0000703a425440d101041001407039407030000e00d290503003541d8040b015280c2907034013520780510340300042c096805050600094003004940071503090107801c0009070b000c0c050050172002d901c09800b8100007640002085a50341e0050701c1c580000324401d00030001d400005401030b0141c0024000d60040c00340c40c2c5e03200d00c10007a080807400d441100240080d503c41d2441031028110210988401e40300c0d0040d542c1c051104000810321412080c2294000e001d180514401904d41801500e03a0480c031440c0200c5004190b0760310300a000c0194481c500100a100440f0800c0c402c46550340f890f0800c06004100004042c8070440a981d000f023800c540010322022019910954121064101d40c4c46016840d0019180f0b034055220070042e83c0350762000c0c003403513648038041c04442404400c01c4200d102c0003500c1c40c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 263374352 1250 263373102 263373107
    0x30d051b0d0e270a0902060712080f09011a0603090118080d05010518060405070903021c02031605090109020c011e050f10080a11210106080c0904120807020316050a12180303 76
    0x170b503d100e0003d0000d83ca04540d0f5264040214200c0409001045002c411b000f203107604501c590f580100000005c20401c0040307c4002c0b90301c07105441d154402d16020000c10203640d803c0d48941034114a110220285d4041403410b0310142c2c216541000c4464540000024103003003501d14112400c980004001e465a50102008018803016105904005150318080010b032256001011074048c0ca40360340c9010060740c0704051400d003015500e401012000c0e601008141c0b02c071168503065880c061405a00c1e801c404180c0c0c1d005143d00d0712000c139410403107044450013000d194042801807040094442980e519442c41e00d0036180107100d000c150350300c03043d0340b1310101c0c1c0e1131b0801d51400230005000301103410311b82e51032410030144070256040a96580404001a80c4100300b604940301d401e0300d6106052070039444038510701103e0035041c01486445000035015038400d0007103582164901c1c0001180c00b007039080c5607a07103042203d001c550b407800350840d003904580140d00729000c084030704c0c04040025003103503401c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 263375602 1250 263374352 263374361
    0x1107030516020402030705280f08092103010f0906030804050607060914010c02010614033403030914090c031602070e070c0203060c09030d051b0d0e270a 67
    0x3528070075a0700101e0840141d94500046003e60610380d0f64645444c07181041180c2a0001d0942d0707031400030703419801c1e10500c0e00024003c10703100701e41c1450385040d0303560308145060030b070001d0180a03074042e4030172590100c0d10400059030594506480380300e14103803140900c100311540740c00042c00d040802d001c100003918000008046861103800c02180c0308250f039880b01c15155a62084a002c0d944400107a00c1c003550903c03a13400185800321654401000c44404a900e41d031007602d181e56213020340220b0205036580812002090f040d16140c1c0314141c0e5490400a0104100b4041c040c581c00002c002d9584501c1d006c6035071801100700f07243d103501c0d50b114054241c550b41c0ca120303098405c5d4014004001202502c0d0100f0903c00c07030b07494030f84081404481c4101800c142004000c01d103181310511012025440000301e0100b00030300f505156546040021100744100d00040001c000b92046403107100501e43c0c422007203840018296611240800b19801ea0761400c624501d4155224801d5400920b108003141c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 263376852 1250 263375602 263375617
    0xa0201020c0d05030a1a06190c0f03021014100b0d0b0a09020903070b04061d0a081606031503020102120d1410031707020306060d0302030c2b0311070305 67
    0x103162200700115141400c5540042d1804544080208a0803040c1c46c00385035802003c8201480200e460f0b0400203005004030a0214480304d04024400c2405000b03840c0b848845403c444070340d5065a0924001399507a410880e244059400e025400440c1440c034981d0368052440090444402c0d42030a11038451a084805400300150b1140304190003a01c8481c9240003400b400130700560713a40b001c0400e0520b0810b059000111600d410001001030944c44490414500e40060300c00000c145014000fa0f101080d40c4c0004155000e2001c402c5520468042c45000b01d44160310148041c1c081459003060060355444080e0150b00f103110708040c0b1103081e00c02043e440c13a0315a00007400808a803500c1260f403070110381c0202248000001413041c0005500380350b004082a501c5a4a804040c1e0701003502c0c2c1c1d501a1869015070420100c000405000f0700c02e03130b80042d10040c200c8043c403440c810a14149070a60100c86582c3c01040b404020b101e03c203005102140c402d09c542c0301d240c03030340542d02150103511810 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 263378102 1250 263376852 263376857
    0x317031302131e020c0c1215090a0b010e0403090f05010c0f14010c05040e0a02040f03200306090106031103060c04061409040603080901030f2f190305160c11060a 71
    0x1d80c0722461400702e00c0e0f00310004003c00010780b140c1800f1442490012400303209813061660101603240c0c8240050000340480030b00502c0c59840d1a45802c09251040018000b42484e03200c0303002089080e164020140b04502903610350800c03a070350304449480b4a020303014681c0003d0316851210007041007200703100e452b41d10a1a540c0c644522404049086507009880c1800044001900f000403c80b59160160801d10700e0004503e020300d800100c011000061000078074011040401036261601c0e1410010300100150560300f4034a00316407035900a26040c00106c40d0040c0e000041c001d141000980d03a482440c0e0060554682420700c0c40c01e480e1000400482115040c0c108010121503c49010351802540300e1110300b034a426a420014040e100c80e0032008040c203103040140643c0c0340101c0034068108484200c0f00c0c20a0302058141205031041d5a24000390000c07542c0500e1460340d150b44100e103d03080c3c01c541d054490751000c83c101c130802c3c0300f00c0c0060610384c1c00490700302c4d85181100080c040f503802030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 263379352 1250 263378102 263378111
    0x30910020a061b080a05060609040c03150b0d0e0114040b1308071220120f070b010f2402060a23190f0902090f07090806010b04031703130213 62
    0x550b50401940c40c54015140070f06008140025a0754100c0100c9400040d81c16040c03101d40740480202c1d031b0714040c3d850800e125507200c00480c08114081d0340030207243c4180100c416500b648858510b074056012401c0551036510700303009011201c0061080d08060714920808800a131500d8640c028280c0018140714200300d0b64860500008052100038824284104601d42454020704c1c00501010748408910030220300c0811104070701080030504440c07041d00c444040f0388030717884100303815010301400b82c00801110b503880000c40c0003115400a202201e43d41c1c5040c4600d408a21106811080c21020110160b840f140c04501c00f00c00d0b030380299101a05464060620008107580301c001c1400a881c03121400c4080041c94407144014050b05c40026a95138060080c0312481c0e011551000001303000000241e80b00c00803400c410304c10f0400b1001402c800c401c5400e40c1d610b40c0c6401e0903543c040c0c441156003241032190028804015420340388525212046000000300503000d12040c601601c01e41c820481e641c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 263380602 1250 263379352 263379373
    0x2090a02120103031e110a200a08010905280803060301021908061f0c030509030c040c080906070c11131508010902010210050c0a11010e010c0e0f09060303091002 71
    0x550820600960103640e48a0340034080c00307401742d520a10802d5a00802104c21854038400303400003807070505940e1211294460b4062030b04080e281c50551070032280d010030039850000f018981500055495070154041d2035000030180c14105001c41110000d178440f403042d1191101146900026560240c0c01800142c0b61043e0b20340300903584003a9480394400301781c5150900c06641403519007007490041180c1c0c001034642075140c2c00b4158144052005042240001d100b00084e03c1c00d0116081c103150140c01803012648e0f410010780704440454000d002803080c18000740c89644928007003d400c41c0c00101440c40301d4a010140f00c804801821340c20711a41d120010310407100601040c94005001d00000091100c04610009040450b08880d80035410f04080a00840e0003114080702c0007032038079050401e8000f64541c216030141451031405903083d46011403c4094641018080400345c808071109400c100c41401048480764007942c05c50f07010b6205014204650500d6540d15020b44030600485410108 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 263381852 1250 263380602 263380627
    0x6010b0a020f01050f0a0506010206011a0703110d0309170a09060c06090212011d0a0b1302030a050307060b12010e100510051c020f010203030103110f0423150102010b060702090a02 79
    0x3410365440505c22407000400c034490641d441160b030010f10900c081e140c0c07545051141c07000b85010a55400074140001a007004040c01940f540808800c180f090743c644002d1b851002e0020400385101b42c41030200181c0882e0300c11245004c03500340449a4841e120100c0c20010111070f408042e550071035500303954000d804096540e410a20184201c0000046624501c500d4130041c2481d00303820b04100da0307001902a40000d020100c4150b804050385103208134102d45400060301e41701866801610354000016200103021203a00850706118040d64094030000c3c07401da03201d088805603500c081044c2c1040714210100031840c5c1140f13030003040071203064428503100c50000300003003d500e500484100f000c003103140450604501c400030f046400d0010310300310b6145484080c051a0b010302d02d01d2140a0b501558038191b9500d6008102c80d209500000044001c504c030040c0300f1203025504508410b020b02c46601c0325602c14040d12095080241856040886a500340414018060400300940340c00b4000581c2121 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 263383102 1250 263381852 263381861
    0x50418020f07050c1302070201200123070f0e0108070e01020c100c060501050d0b04030e360c0c030901050d023a020a0801121b120201030f020c06010b0a020f01 70
    0x1d0243e4040c000c3c0d03446800c208050814113849076000540140840005030383c0203481d900700c030010b14105903007815038441442e0040280c07030364501020100745050311105900500302446491280c640030000b20140c0c2091740e405040388034050008896100007043e04d4072400740c85180c1c3c20706004440c00040c0c9030300010080c00307122015000040300d0510b0001844001c1c0111401040b09403809802c0b030b02e440d15640b10302c0c40010009824082403816121454450303241e90b44c0d9000e82850100000500c01a0000c0802010307508800340407030400203d21440c0010040350420b015031002180360404040054039560445900140710302d5007446405d000f50808800c4a80016040c07040da070210a0100c4d60700b61245c1d060700842032041c030500280814a03007190340181035658101d01010840143e192400c19801507602904186a181c0400903406500c5001410b0240c402d882c144072030202c0d055190120f00031042d0014040d80000c0c01000100d2901005204109107881503a40c14202c5044035801d48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 263384352 1250 263383102 263383117
    0xf06010c05070314030c07090603020f010f170f091e0d0e0102070b0406090e100b03041e060c030506010f030b0904030c020a090e030a1d0f2b0807050706020d050418020f 74
    0x717400008000c06002d400748204400740242c8442000014199004a4003002c1440300281c184034480c8040e5170050f008a401c0250003102c0f500b8500c1626080909144c1103105a9180c1d00c1403141c140e03103c164081c0806804d200c40400c90047c000b00260300703411074110030703400402030640c045d070f85010410b8003c40d8010400b9001980702c090b07001e4a0100013019441009003001716402101905000700d0340700b00110b03600305400501e08042c00110071030f070b0500444088001082589041595070125400d604414800d80c13098880302c01c548001c100039010b580000d49080c3d40301d2111030000c0c000074020709155840a0004d49000e585030b40781c0701828202c1e80b485004910941c8003090000c201584030030405140d81c2607042003801e0305080d401056550350a988058807030800080070344c0c58600404444401e80703801c3c140019a240b11400c2c020007a40c800ba206458a004601020800500008654900c480b1070781c0ea851904d440d10f400d54480000c001440e013020b5808010500000100d00082d25a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 263385602 1250 263384352 263384393
    0x504051804110603160302030c160c050a05010903020a170313060e090705070b0a09060e0a0b01090605030307020a060507030509360903160f1704030b0f0f06010c050703 74
    0x8070306041c1042c0310b404008050a80c8074410410402203501c080710030382000702030350f03082c05a2251203510880c000e601816240151703804044903aa0284114088072004039541520401c40c600c1c1c80f031004603074000c0c40d800040d4000c0c40320142000f846a400c141100074081c0c1c2d205490500105503d800f2401d0302c3c550103000007410400d08440c09290100c5025040f80352400c10502e0102541d50700d06003150000e2011318500e5a0340c46080904c4890741005415442c81019100c12a0551074980345020084c010341d0320f450725241c030209046c1400803c03110101e400400b207000451130410300f00c415902400c0210204407092161100e2030703d44114001a03401c40070300380c40240c03100030318014080c58440000064202041d0901400d600040220703130301ca00003a030200c0c44d0600d05007451a060000803500420080300c41c40f1400c0941001030160040d2441029071442d961644110a184080240ca401d1000001800801c50350348c061200b540a40b445901a2018103580c1c2d140c81c010341503402d007030158 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 263386852 1250 263385602 263385649
    0x50f060d020904151505030402090a0c020c03060c120907050312181f030b0f010806210f060702100209060a0c1410020307030623091911070b0c0a1e050405 68
    0x20401d112181c40d60170800c1490041e0071441c0680000320802d40252402c074500d075480303001000d05403080c13040c034403402000f600f01d03045404e010803609940c0d80030300310040c0300c0d02d510800311701d10810118803503040b20002401040d40c13030000301904441c1d5000d200d103421200c4000814000549404074400030040c0c01e0b516403600741c1030002c0f014003034418a49840d0320031049000300d102d03240e822660040d08200e080c0c1c0d46c0702c103111000200b00f0007407140c4588a18180f04103480380c1d000c60400510144540b41643c250350105541034408001d9000d816866944600f050000407160392207034540410f20b9015500c91500f0110190f80181014604840210000c1c0c000040000c3c0c1d5401d40100b600400c0340b13096a21448800c0c60f072805e00703012000c000d036204030446e202091901d0311002106007205038510080106040350000400c0759407152104803a20951080043c03c503c429200341d40eaa90f20b952600d061f03c02c822696070b81c2d4100941200000e10074284000700c0c158488400200700484030f601d1140c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 263388102 1250 263386852 263386859
    0xb1f0303090e130203060403030203060f0d050706110f0303010614040b0d0920130207061409150c0406051911031c0608070b070809010c120f080105030304050f060d02090415 76
    0x40d68800c000f000d407421059002c2890700140c900045040d446505494016141e1f00e406000030404c600426200c1d074806803a0900f0301c1031203004030b002d4080382c096844550104400d1090a42c03100c180010000e0580c2050004000d86802200309030500000b506205181644030042410b03a82c003c403a9840040c1d5450141d80100141660b1182030545801e11480a03102540000740c008100c050188801035008036024003009029089102c1746525080e0b0034059107070038040d543d030381c080d560f08294080c408280812903030508403084a05580c4143e480602c0d0008080c81c8000c403881c1280300d02c080000c1c800d0044c000302403e1004d04100c86418511240c0307040e112081e1410754006410640c05900008020040d81440760111038402c0c0d44666203946030b40172600140c1d040142104013600c00000302d0b044005a55000a80e00340d425040d403035032446a6202e9003810398a0040703005680e045440c0d02c0c141d107030030300e44040034000403040f000d00989040408004607003070350650600c1c0803886480300c90a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 263389352 1250 263388102 263388119
    0x70602090109080f0307060b18042906010903021926010b12030406120f02040b12070906021207110604030812010e13150209040c1d03190b1f030309 65
    0x48000e00703d26005140014000c00308075100d12071805d0040016981e0b030100d1300582c4900e460b41e1422038000c11087e80c94501800c226400880c500d80c9125078054030860111b0442c00c554405014401c107a5a803d0404d08503401d01c02c0c002503040f11028000c003000710008030440154800b400c1d007411150000c04080542000d42d00303580c4185000340c4164103c00d4205009500042030341d088807000d1070b2040c09880031682103002441d03624100307001c1e00e000003030100c0e1029501004101001c00c42030780d4100c0d50348001084401c084140079200c016004032801e15000600c4101420f80d05004402600c04500344c4d0b00041d115500541c8101d55084e004101105045a0506c040d401012079040105151a00d0001d03405030300c60901b0300500c0020108211708c0d0b20421503050f181c070403030042e004001c40361445c2c00c0a451200c920f04010300e11703d1100048116820081205c40e102200c07410007140d0303020300e0758400d0488080180f1400ea59418540d800d02000b100c1400580214040d440e01c2d030010381000c0c40b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 263390602 1250 263389352 263389367
    0x327031205163b120601030308060a05060702090105010f09051c03030c020d0f18033002011a040b0d05070603050f01050108070f0f0909090606180b0a030f0c05060706020901 76
    0x16510f500e50300c0e40b500c80712076241d148a901541c1c1c00e80901c0c0410066400010b500b00600c10550045200d010004010542c0080c02d03a030252008440030355903a1b41e203004002c03491280d010000e4211110400400095000700c061113011002410244422511440450844007043c4c000c4040c40303003101000b80a160f05807040184c0b0805602c00351020741c48025029003201801881c110810007203440d0740a00c00344030002c04d0080c603405204480051024900f21f41902c002c02181d440c080020410a080c842c014424802c9202da07181884a4103144007007004010240b03021159088a150b1042200040d02401a00d014140715140007459007054840c106038400143c008c1414031403c5401c0c041c002c0e40059800941c039807240707840800c0141c01c40040303030301030001e40c00009c101d81000c020300100240e68101c0c2c01528480740350b80c1c005030001c204002c02e6074100700c10b03187c000000c24410310200e0b84041c00404d403180070b416088080f55032400400c03125448200c0a0b0b40d030540c00300c2c2c081d800e0f40c3c1c0140c1c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 263391852 1250 263390602 263390627
    0xa03031d1908070206130612140106090b07050a021809010b0d170c01060e010b091e0d0206030c0405030d080109150e010b0c010b04020d0506010f032703120516 70
    0x809445540036661100c09820a01c040c0064001264041c210b50750001103400c54048004844600c0341c2d80c450140c207103400f1200700341070340d801c0440c030b40b400d0311000b800c543c12212141c0d40e0f4541c3c14a0300c02c500d60705038422a016940c500522120a000d40c1398060001c8034151450020085860f080035005e0031035100c0d6801034410910754150101180c1980340517502c8030306094020b5a1540700250007401098540d2007200070052380000000c5100068010b081c01c2c5806407500f854a00403218400503c4125030130066020410111400150900d200a554019007401d80a8a4140c81d980064078210165080000040e9003100500c0903846d94003540214903844034421248c00d00704802000410b10501503548a03920105556054910941061130890005001107550b4140b0050000250204441c5180484d003d0001c1181940c86445500170103d00b0300421003428081881021031242540d01c242c04001c100e400070303090204240305c0e150013060600441c1224040380305024103801c01c00917 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 263393102 1250 263391852 263391911
    0xb0f010b03010506030412020a140717060f010b0a0527040f0c0e010806011716181208030403030b12010b030111070c03060c050f0307080105040510030f0b180a0303 72
    0x100081d0b00c414081c0e0303800980c00748022145070360410040341340c609c0400006e460588412100080c0c3d02020032a04180d81020b40002648a01d1070500c941e6041300341c44035614031034001c004000076401c01c40035262030f0581e440c0c0b0a103001c0c15511207423a44503817101c1401d01c0100006c0144200c1c03a0034071030b030510f80c20211401c0c040c400030150090b1140f0000030b1058140601180014442d03889a40342c40c655052505409201d420240b0308074404038100890300e8045a070800320902c0c03d0b9a04d8070848100e580d103a024601c2c4803065034900030784e80c001401c201c003456240c03d4440704c80d030344802d103100740000d82100000e940c030140000c245c2542e109050428529604024410200d03074980791090540ea00318002080300801694102c44902c5180606040d0480c080140000e499010b41e03c28100d0310b0890b010f1000e0740714003020b1800d110262100504582a40c135071a0001030445051719800490602076004440181c0045801e00500c0300c0c0880c0003a5660060f002c0341121001a1020084500c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 263394352 1250 263393102 263393107
    0x30f03060a0614030f061906050702040501090e060a021312080c160f050d0c0801230c2a12042c0108071a09212e0b010c06090b0f010b 59
    0x10883c0c22030710000c0c00c800040300c4020f00185040d11000c00315481d8400b0b10159000703290762084c000744107410910b401c92285040400010f003000c0c16028001c610311010b4060b10003a00c841e0780c840300943c40440d542403a010300d81e0002400d20341040110442c5800744410503940c540243d0000d0422840c4100f920861207200c000380106068a624817050f40c50540b00080302c42c1580c203054010b014180c0c406d100d40d40c28564844107480701290f034402100040300b148071154580c0c03055207800303004117000b0904560419203502200c000c0c03109030705050340501e4140c9104060300340792401e56a200390070014084454101448030b01e4400420344540405054810800354103003032a150301c540d164403507400c0c244803200c00211880002d0040300c507448801880305403901d16000c42045d0089006015014a001c1d400f0318443c0d01064480c842030140c2d00161603401d80a0308841c15008155450340c283c100044801e0080018400f4030030b45004c1c500a80d02001c0910303013806030420904058001c0e040c100703410b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 263395602 1250 263394352 263394377
    0x606060e012c0d031103280c03020303060405041e0302060114010503091510090207110405060609030606210105040b010f21081c09030908100e0c0f12030f03060a06 72
    0x404401c03607114600b00e41c061040f1519040c00c0302c1d13100b0a003152210b00c1c0000518400c4000a441108500d503082065003102c2c1504240251342030200c251018000d81c104100003449880e041d803145500500c1035040c21030815006208003c008a0100c007140540c0c07084005104014100140c100e9111003440d04034a1490300320720715911042c44282500c5d09800e8000802e20b03410007200404060700c82002c0454545600d400c206007030952821405004a2030940807880c2410b00000b1035002e8000580100b5003500e03080107110980d4203980014007001400030b00206525028040c07240105e0042c40710915950502c40b00f14001c410302e9005201c5800b0300c4620302c0010201c0000e100240d9000b644968070303015040b042100344031410f0710503081c0078504001001010341004001c0152041c0c58200c1d600d00310304517030101c12602d042120307028076031065940e80d56920308000141c1940302e0140c21038035100c40000c5020315640080e0307178003e0310f86400300c2000b0300750514618000c010f1501c3d00d40f98076400385 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 263396852 1250 263395602 263395667
    0x71406130506090c0a0302150c030c01020a0305060904020d140705100e040c051905030912040602010e01060b1303021e0415080c0303030c0a0f14030109021210051c0303090606060e01 80
    0xca480f000307000e075407188c20809110b403213402550b0032002c400040c1e079a591410007182e07000354091202c0f003002ca403500340821602d08007250801d110369406410745400c0d254580395544850213219080e002c034401d104012a86480750440c45080140684940546141c58010401a00c42d040192000c014050151056802007002c00e0b60241e1103074180a03559031965564907080c42c00d05080001403e4000400042065056209000d0030f003110000308190380d26480e48019a02c204281d8842e14400036500748098581001031404030800400300b010101c0c00c01003c45c00b9103400c01c5400d030b2900e0f86079404004081052011500c1101b040b0301552440c54007071161640c1c4c3c002c185400c002c018403080f04260b00d40c02450840b90741248034031056240c0d80d41c0c2c00f03140080c0d0310034814036803012445000302c2ea0744034500c160030741907030760050201d158003600c001020b24507a124101501003644512450001c24414840c803809407090765103401c030b04801e02001618081c0c041000410361621883c80d2122241c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 263398102 1250 263396852 263396869
    0x1140306060d1703010b0c06071e11070e0109020901170408071e0c031b05030f0d140f070503091c0308070e0607080408030307030e06011505071406130506090c 70
    0x203804030b410400079180c0341003e144580084040c1c0c018040000000f14070556480050080c0100003c21282e09584442d070803a8079080000003010910005440560414021088082d010f010070003200c4e60f0f1030381c038125030300004c1d400e0b40003140247d8001511215540e104440b18000f4400101d000c0352030405942e074000ca441003401c050980404000748078043c1c8590f03400700048076000700c412031084da01c03410f009230030010031100c0500400c0d42180000f41424046134042da540701c0e100c045c0c009421000c0c000d480b441c1c0450360105021104200f51407004c000103002e0140300d40550011031300c64424100f0301070369007080c2c074104400b40741420010340080da00500856002c1000d10340f655500c880300010551034001c46d8401807240d0f0001c14080b40d00070000000c0c500c80c090325541481903012011480e41c40e94000c3c01010001c0d901000d0440fa054050002040b01522035100d0541c141c0342c3d040008d0400001f0b4410460481210021800b4044100b244a030884144801b03016001039250000c2c003941c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 263399352 1250 263398102 263398111
    0x4030c02130219090504180b040b09070314010c0906030915110d0f051509160e22022206020c010e03030c011b1d100c020f0402160b01140306 62
    0x1444040e0708440900c549805558408040b405046411106924040c0501d1410701079039004038900803041081201400b904151070b07400c028144182c3d11a40c56000c0415801400c5485a20038803800100007240c1c2e0180f18500e40140e00009880150a40c0c0140341c00c0c4c86070f2000303041604044095000c95007445611601e400c002d44000b5041e00ca1501490150007985100450940340010b140d20109064008074880c3e044180040c2c604002c40c400c006600d001030311030505115480501500e400e00402003007803400c00061000c03414048024480c000340700c1d07a40a201c1140c0d004921100a41d40c001c031410f4250700d906480d425080c4c00d1520081d551500090321a04120f0050140903807500d090080f0350b208140c800084c0b005428100715612198a15000140050407202e84c41c40740395160103601d81150320003403854140d01c0c1d40040444d04014201070a9030302c213011548804071a0785610080100680c2d00b80f0600c01d800c00d03801c1841c0a550141c0c4921102c1020f803440325915500440c515502 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 263400602 1250 263399352 263399359
    0x80d020706090204021603030609050408040509070e0907030209030f0a11010e0402070b0702011d0102040501080c030621070807080a05060c0319052401021b2205040c0f050904030c02 80
    0x1101990306048002d000a9000030750400c0c400100083c03540f81004460700e403540641c6052208645e200c00e007900311181141d001e04520020311090040b442c00c074030720039042041803511076154590600055041802a207515000c43d40c0000e4118189c14240009040540c0e40e074044d00e14000d41d9150f9185112034200001c0c1040140b80c2000059503d5030b05407860f00707400c20180d80c1c4600c0c0202c0041e0003402910100814180504d03181c400c000014022901502c02c107959001241d01d8111380b407800c9801c0a0311860380005043d007800000d1059440c2d1444486500b0024000d103450180c0580c00c1150300c0d0040b0b02250030030900b840c041600041c2c051b811444003002d0f00d5581c2e03226075a002c00e0803110412a46800c1c18082440f00d00b404cd6189082494020344180c40741032085d10041e81c3d80e0380a030340c1c80e45461228298400182c94410195114203030000c0d031411801c451100440704071102100c08071143d18044409000e00804038103050042c1c6002d88446c0b2039800d1603100a0301e00840c1240c024070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 263401852 1250 263400602 263400607
    0x803030c25020307090c051c0b090c0316081503151009060e010e090c030303090309010306050a03020d0b1906180e010b03030f0d0b060301120516180b0a1a0414030604080d02 76
    0x186c14400c10840341100c0f031b20080c84e22405680340c2000d000d00300d40c840441c8036234000400300e1103407003840045034000d400d42100b03056a0110458182da00403c0100040c4810015812020351030b1030a028261007c1d19140ba5480c19150000f031070f0310b508440d500031014051411a0034084012a1007020b81514884e800c1c8890544e40c5c0500d403483d100c8508a01a0140404014400c241c84008050110044241c07018403480e5114030078085c250704513210203036000480c420600045101f21080c0c6403c0fa400c0c0e908041c040086020900c283c500c660301404800c180d0300078000f5549403c0c46011340360b0082200030f03c601e105200002c0d58a0151001d00205160700003200c0c0301401690f441040700300009000c0c02e459607590b4001a40d00040d02c241a00c1500030200e030340000315070310400c00040da20354a80b90152260f05403a40d400070140ca800c4141c0103074034010081094120108440b50302c041034508240d4407400c2c803099110a04a00110380c1c0254005028000010b814505850803981e00f04070068 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 263403102 1250 263401852 263401871
    0x504090e030409021201080106050636060a0e010e030102040e01030b09101b18060807050903070509040501020a170c0f032806080f0a0b1f0803030c2502030709 70
    0x14218415503103d02c140604c00900305541d10074070003030503040300d03488002080400d03902e0050003c94030070410b001c0704010f818800341000034060b0480050b006801003187c0e48981d0f101c4007080d0705a001545c0c110204002804000c01d940e80071418a4101c05c0680003981000c0c41d02600ba100404180001030000501e200083d5040601300030482d10000080f1081c0481613480301d104400066010102c8005aa680103d81222101082d2074040320710075628206c842d038804208540c15041154426454000c500c2c3c0080c071030707446a240e2409180204001030b5103100801001d4406203900314000e100085003c01c0003c0001700c0000e41e2032903000410859913039583ca1702c0d0304103080c1042003020100800c82d0b0701d2210034682a03000d1001e452000c4102c803026031100c009203a40b074440320b200400294840f000110031141812200d07942c2d130403030110281000d0700d0355980d90844e001210104100080441c1c3d0f00c003103d210455140c1ea122040c070442404007001e03008070740c981445006007000240c0711140c60 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 263404352 1250 263403102 263403131
    0x6010516060203040605060a0b1c0b01020106170d1806080103030309021206071e1407020607080702100e03011d030711010219030c0606050f0105040303030902030a1a04031e050409 79
    0x21101150702075000c668900d0240b03802801000c041c0d4030719002d10300c901c0f40484e4a102e00e82c11124141c1540601502000102040602402003a03600030b0455407a9500021714002c400c01c000026034514014043c1d503210f070744c4010000c0101d03010450404038090b108016254100460030305503509850040b40345071190001c03c15130b003000b004503081e41c0b081d42c04000131280e000b050812100c1656a840c4030382d0b68a418100e410b522504002d00300c2d00002c22444c4014600784005060151265001609001268001464205202140c6000300e030000301c8840180c9405e200c1c055a4041249904000d07540459460703540c0c0c02110b10061401c2146940861141c1c02003140c00f5a82d0064070110b40404401d1500400c3c0d220600d100b02c4800b070034a00040703528502038500100d03000044c1d41d03860401c1d00d1900d0460150424000980e058040d8100c00004568484866540701103144081c20b901e080603d1700a1181661441c0e10140d10b080f407100b8660164010125801c070b80d8003290214640142c141c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 263405602 1250 263404352 263404387
    0x120c02071d1e070305090c10020705011101060308040807030c0b030f0f1506040915080c030c060d18030c02010e010e0f040f020d02030a0504050712030f030f180804090c050403050303060105 83
    0x2c900125020010480c03180c1d8140c200510079141d070403c2d60000075841052103540c100882070180035810078001032003a940b0490b000c0759156100000405c1c038958075180c118090344107400080345500181030910a2241521001000b403130b00300001e074074600e401081c4030181c05028150603890310811004c40d9a008039941c4d40035428034002c04007584c1c0d03540c0d11581e50060100003800311200b817a02d0342c002902080030400940490300600900900c0b2407a60400c101d81c2d224022901e0915071304c401034a1000031120000d40d05500c651120f0000001e80c0c000034141404081e221810402981041c00c03058981002c03803000d0307200c1644c011500ea800c9801e03032000f900904518041052001c4204003034071107990003613402039020706d00ba11420b030f0302e60800b09070780149450003030040f42d030701c00c10b000204e4030035071003080807101104001445040000c25000424000003040c0e440c45d2001c50b0500c9818594801c3d0400b410703072410080d18251850780d90715181e010088c140c0b0f050200101d4080e2400752201203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 263406852 1250 263405602 263405641
    0x312070509040f020f1e190203040905090607020d0e0123070605010e070806100e0d05010603060e030c1207030504180501180b01021509071203120c02071d 68
    0x1405018980900010010340100100340d01ca541010704584441c07045108580e8405541040c5a203003030004d044849040c4d04080c00e00c00c018004110181d1480d03580b42a085010038540d02450f604c92a042c0c1000540741c000c0e241c80031607003000c01401f041d5600001c0301c000c054001d04011150400c100010707901c20302c68000000d80e101c6600001c00c4400b4a00c001044524803030401000683d0703e8000801d8280c0c011103a81d00072405442c0403400d245091240705000034014a4074601c1c1400900104040c400c400303100f120185e4484906008100c2140100c541c084803040055007040c5230840c1041d41d860803500d20380d50f001c01c00105001418440c0045030080d00c8000341c50b811020800440c400145801d10540e08840030905003001640b006005404020318164001c04005640e00100f401d408406841c6071060301c2802c030001a44168194480403280c0240c5601c2142d004013404002a82d8603049183c0464002400500881900404c42c503100076082100188d80c0d5200b42d07522501484401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 263408102 1250 263406852 263406877
    0x90c01081009020a0c120c03170c0d180b0601021207030c08040b1614060f061002070905090c010201240b0d150b0910090f230a06110706022d03 63
    0xa0051071041e04404070340c0d030b140c2c46108002c2951b413034007038104c6010100010090001da800e802e0f1085050441d048142c00440041055190048184049044420000055121214600a100c2440102c442a6034061003e0014042544040006482a101c0d144000307051061503142e160500c4001d8055801421626026a58900703410001c039502400401040b50301d04d14114070710702110804600940070340c0981c1c01440194982d40b04103e43d1861032001201107100c1c1100008030003005004060144070020050f100310364140d40020700b59a500c0000314002c030720400c3c140b0042075100301d41c0800c5803100c2804503201c0c1c0c8444202c0d80034140c2c10152845403034004102150800c640c00040100000450f0982c0780c0406030402034540d070780e603480303100c1150300911020400d0f00c0303c56000d0345240d046003188201c80030040c00060405180d0350020f40c0000c500f80e0b0034a079004c0d02084940c0181c40c2f00e0000b0482e6040c800400c28508408a0007240c2420306c10070b81500d1a5810815507811501c40f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 263409352 1250 263408102 263408107
    0xf03030203041505090105091516030302090f0409080a031814010203100501030504230c09010806010e0711032215030f06050a060203040e1005060c06011508090c0108100902 76
    0x2820000d659811901411603015070418100b07529a01400840b00d02e0001078441c1e60910f07605004000c41207107886600c510140c0100000305410398060841100603129450050700c42d0381c020244511440802507140c007841c503000c002800b20750120b0503580071041520b0045640031a45403010120250014010303c00b80f81c100100d1101d00b03042d00914451f5001d8800c9c25400c40c3e5440044080d2041600e000c1e004240702e09601d29104401e84440c00c501da1030108a030000c560240c0030a81c408403d031300c80109500444018400040808a2290081079616001e21909100c03a0300907200d208060307842c2c843c20a8100a14140b45406410000403c090b02e0502164640480090301800c01d00e42240051850284042510315140c84084141d0b98598001d50030b1a00300903215030180b001501034010701114076000502542d96a000f440c0601000b0040c120b6545008151802ca180011486040c4a504000c00031000400180520920300074600b9135030380e450b50407100c41c82e140306030000c89070503000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 263410602 1250 263409352 263409359
    0x2030703150c1704110d08040b070f020f030d1d0420030a0c0206090a0b0c070203010207140111090f040c120c0c020109150e09090712060603030e150d02070503040f 72
    0x5035201c0c80a4014903210040300c3c030b0078001c00c6008408100c0700200039084940f80e41d90741e42072811001c1700d110300c40c4d42d07040c0c90280c68403488002c40d0010b480440301586c9001000c403c6040c4184c40074400f983c150024100c1100d103080143c0802401c1c2c840c50500c03520059044055038a5800c0344004c50210f002480310340444042c0301740294400c0b82d200c0220341c20019500402480004c0840c400c04005010f0316039400640d03a007103a03d0102800ba001140d0040c402c1d280565401e06c014100d4620034101c44007120001e1080909540f00080d0350110803009100340c01141d1150340710715106c2d51085a0000e241004400152502ea040c254803903600c41c40c101c0b000c1d80081d0484003c55885000340c980c2c14920340d1f03455000702004101c15418000440c035003180855800c104071040d81090060080d45c0c590368841c10b0004200340403210580b03000362584801c0040c140c001140550000040da00d01c2074500c0039240340181f91162841ca000999800995401401400e00903074006c1e1201041500604e0356 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 263411852 1250 263410602 263410643
    0x3032a0301091a0102060412030c1106070f0f0306081902041415010e040e071401090b270316150e03030706061e030c05010f11010f0e0d05090603040b0402030703 71
    0x207084542100f118000801440c070760001030320510860340030813090115031415004030042d04540402105008070600c01c442400070503c56188a551a82c0c0d45084030a100b040080c0307210b907500d01d11000c0c145040c500303002c042d0300801d10701d229a007888104140c120b01d03840450010502800b20305807070320810342031007812001040d0201200401b40c3c2c40c504684070800400040700d02814003d0903d5126140030840180b01c40c3c0c05d000003003c14148550a03550701c18020500780c0c4025041520075154210b0a18243c5079000707490701480003038008081484080488802961460003022000c507401241010424401c0c0c03500a10180c010741900d45650491401c0009880030b80074010242c0da4039884450341c048501d0750300c0c007100d4101c040c841ca80351030400196403024a44425a041004a9070071002d1800240107200716035000582c001001402d000880e07050441040c0702a0400604205101c1983c1d1948280e80d00150400e8408010307444501c002403419810b40e100412a000c0424071880c02613 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 263413102 1250 263411852 263411861
    0xc02070f080a0f1119170706120f021209030306040c05040e0414011514090f13030804030201020909070c020901050105042706081617010b01090b0a0903140f0f01050903032a030109 79
    0xd86c074204814000c10314212031a1100d1082c054600040c10410304903a02d00401e40041c4242c203842840186004c01c1c0c2ca186403480701c07007102c2103c5603910000034410780342828800c0c4800c0080c545880e90620303051030f00c8504084030180c0b000c2c003025041140305c0d100f00002c1d80308200d407420300403929040700c0d0356140e5580c00710340300c02a0500c00c1c5030060010781000310383e03103902c3e100d050f6200c43c4294440c0960303000d8481c2c5070040c006070119035003400a06c51540710f50745201c0c0101d003561940d800c00c0c14503104122030340d0320503000300b8104801800100450860030200e0300c1862148525072b91280b00c6480d010004061070341c0701c55000d20800d443c1600c0c10058056400550fa13403a20010901d4602400b000c2c240c0c0e10983c059800980844000c001150401d0080c00300c1600700e2828000381656500e9549403003400000994113030b0440a1001a00c1600700030354500201003c00a00103441c01a10064503408000d2294031454984c400c5a2840d041403050b4000840d0a01140c3d0f0301c03940c58140e001c0040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 263414352 1250 263413102 263413109
    0x1050a1e12050c032203030908070609050f0f061303020c030703080903070602011a090403030f060e0a140105150f0c0f03070c0506090a090e0307050a060c02070f080a0f1119 76
    0xa00c1e220200d54041c948901303c911640070a03800080c0540062516000188104400e030101991021504c0015112030024501280950400702e03261905090003420503042c1d0344c81f40c5180c1d00652114261000c04140954001035101c900385880485042c160306003a001c5d80c80a6141c004d103e400300421420b24041d01180c4016421202c51580300d4800fa800c1324010540400035818009504a40d80390030200d10394400e1017889d02040050704c02201d1030540c1c6842c1c00c806440300500341040507441580c440c4107a162241504819954905404107500034802030104040f41800184040300781181004c641c900d5240d201202c02102004801c5a03c9800a00d0212448015928005924900030054170000b96000703101d0000a468003500100030300c845503101c5070502061244e000894010300111a0060040101060f20362100074002d0800ca0107802800103e50101810310040e60000f68485069600945142c100341050904070941902c20511561003080982010030303100103845400c044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 263415602 1250 263414352 263414387
    0xc08070e1e062d03010b12061c03080403020c0a0b0405040c031401060e01080109020a050d09030207050d08030f09060405120a022b0906141608090301150305060f0c030601050a1e 78
    0xb040031814040790604c02803040088000e0140014100566412200c6400030750013402614600c4403c007412001582455050300444d00f00410041410f4040c810800c8640382111040c00103400c001b550103d5018038050f25000e159600901d00516020b9400407841910508144401e036a40b100010001c1c050002aa40001c51420000403aa0714038003d40341806010740700c85042c4103841d02501c0c0244a80030040c3c04502c6515400209511398804694003580a00311395a036030716001002007001c401c00791603e513540d4010000c010103d0703000b06003848031828600704160b6030040c44108916180d00c12948000c092130000c5244180e054003003c408030000d00e03445095209075140026192003160100e407401001013000899943c603004889041b00174401c030b00300390401600c800480d00b15800701c2c40c0c18441141901c6c0a20900404000720340d408081c00c00c20b41013516066042940a001c09031040d070602c48085400c903102405100e003007840c041d0f6070100790f02241c841c4500030107840407010603541 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 263416852 1250 263415602 263415667
    0x806070318150c090302091801230403051606020f030106020105060409030917100507080414010605030a08030604140411040b011103070f0c0f08030a030c08070e1e06 73
    0x30000000360354901070540024201c8902207090300c1c0c140103040d20300191010415194800700c01640d134444014091742c04820311500300d8014039103041c00c50362400003025a4440d40040315a91441d030391061035006a01d031a0840d100c50380301101c504c003151a808010071050000c51000001d03000100a14100ca1466000340100e40b03944050204403419a81c010700015a81030b42403041e84001c0c003407003103440e081101300c400e200100301c0060308030f0307405658000001320040306000c1440041c03c1000407400307012000b080f00718640800655102d5061800038103284010000600c1650395500c0040c24040221014040c0e01d01880d101103081100510148110710b0801514038552041507403840c501c42c008011480c000d880d031651400010050400c403401000102e000c12219203910306c1170001c1014500071911034824000180c1640c1100c82c8450402440038104031036150b01807074640c0202d4050741c2002d4a65002ca015540b000c8044083d180c12190006070502c181e020001d07643c1d01110803a10700d0a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 263418102 1250 263416852 263416871
    0x220c09180b011209020d0303110708180a0503030408070e060406030209040b06040e1513020402160c08060a1118060f1303020a0b072d120203031801060f090905010b060408060703 78
    0x20803284c54200203900a00441e020b207000a010b58401000041941517480c2019031a0361119196404885c0442460400203822440e40c2440c14840e00a840d04401071030a0a040001032030340c8043d20310841001d5003c5074003041c03158031140d000401850b0050498480c62400d420305407146602178079014000d13440e205241c2d809060110303500741910525210000c103034860703401e1903115240d1140d0690740b0590130030841d280021401d140d035404034072809080700d41920b842541400c001c40140072100d01400c02040c4401d04a4040c22140950340030345c2004181c01c000c1c40421124003a50449a10306803000503041501562071040000b141d202301c60108000d51110046101070064010007040c0d801021040902400610b200c1c5a112040c005890802845915144103218100c0240750143e000042131011042e898000404181c090b00024813401d0714110702c1540c90071003031080c00b00030b6540d040140100301083d080f1040c81ca4004160703a48803a21511300580b81c840580d4001c000c03034582003030361 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 263419352 1250 263418102 263418137
    0x20706030b06120406110a020d03050709030b06090a060305010c030f110a0912050309030d08061c05030f07031101092a050109091e1407020705220c09180b01 69
    0x18907000009041581800f8620700101034244029104852407910b6403c00ea903040642400340c807004050368014262003c1000b00a011240d0251000302001290082400800c801440f19074111006440e604555a0b80002d44002058580c100904650034200c03500c420642c03540000070400c105803800c01000e41c440484105034480d0540840105805e19400c220820001000b107481500a1058a141a1010000a0805071026414808500844c06102c45428441031b00d4080042c0c848059400e010746071100f41c0c4d40c0c010003c5070249580005086400c0501c150f01389070180d00104000d00c02160705103001e845100e0050003035038580c844690120031011190b18124205c44040e112200742c1030602e08044003501103030314102804620210185601c3c513031031050107580c04440c04200d109044ca000002d0400249500451141c120740c0002100944038484504003112603002c00200146461801c0c1e5500e18140d01c18403051220300c03002041041136411000c41007009a0380c0c0114101e40c0c0054 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 263420602 1250 263419352 263419361
    0x3020d142b2c120a1403030714070b04080901050c010905060a1b0509010e0f06030f0411060a080f0702070b0d05011508090c040e1218100318030305060f0409030f02070603 75
    0x88808480203600b0300c800504008040005190100003590f0244441d51a03540e01818240010301203030303000200300603000d40d00200d601310300a00346800134a4041d00d85c440307043c901800b90000d40201c0e0b0001d0025820380c010790407038042c04213820090044280b103040131901c0360801ca960310180c81c14100c886101e01b440042e40c800da4ac0094859501f0f045023807004564440000c948a90414441515003500e541d415000d544540c480752481150740c0b82034038003041ca04035210201e9020b41d1041c481c80c111070fa0001e038080c1c0e01200171404034909580d0003404a107860100d500c1400700600c001101c034180071154010b5816500c240541030140c0328040c004440399a01240d5491194100d41000152840c1c02e80084c280385040700104c41d81d8561851241d8550b5100070003402c04e03080b9003001ea2150342032a0741c1002083c0264181000100725550642c0c00441c440b50b001000c041d601c400044066443c91207600e60b08801400c200007000ea1450042c1c03400710002c0d103400142c80740c41800501e0603c80d003c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 263421852 1250 263420602 263420657
    0x180406030b13030c0b0a020d201b01110a0f0207060806210c030303070903261b0f030307030203010306050f10180605030a08040e010e0103020d142b 65
    0x103412010ba0b0341c0001c100103150340c02011010813107042d59060100302c150661900400c0f080d103005999004415801003103d8401d010003206a0780d0501d040712911445058800c503001c10354079401c4020304018800d0042c0442010341840340d0010504000300d561100051600c0c0310755408840300030340c9550301900c9a901c01c0b288c05510801200e03c03d0000208002d881240e603000d02c0c12203050114140000e81140c00031900f54001404480d0b0030414451101421800e01090300081070112000441c1013080e44119191104241120012a0313442c0c201000703001807100002080c2c070745038203100c80020007075802880140c6d01076080c600440c03100800015914090240c4030001d504c030a10700340b10354401c101d8840d0400c402c5c44e035504c400a01c0d505c0c01d1183e4908540f0680c4516900c07400c04400d4041220180c1152524500c000018001603d071030304440410343d00142c03030f0329481142c411500d10702a4500301c56109500b10807180c1c1d40350003294405203440c43c846c2d12512001c8920030f0000c41404020003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 263423102 1250 263421852 263421863
    0x121b0305070b070206071a0601020d05040e13021306030602091002152d10061707141c0914010501050402180f06040302061306031107080a1206091118040603 69
    0x941048180c188800504030a1310141c0480e0410031151543d083c12494138101e41c00d080c1c500c40400c020756a0600400e081003003075040182c1460308001d0404103010000f4034541c01c0b49942c0100005540da50354044e14240c0c1440300900035251a031902c00301940040d02c1460282c144142c40351011400404c44404200b49000740710f03600c2d0f031080360403010560540b05061f01c0036413a2000c83c0e101d49004406501c610a42e61001e0b0b0418500b40c8002e0a040ca01c41c2c500c0d0104862005010006034402103050041710700b13195980e16a0300070344034000c094541e60b0a1215043c51301e804602001059520f00100181d800020001a80d030b48017840242d21510481100c241440400e101c414640141c0e0b5884422005d00220300740340c1c495012403120340c4007902c4080c544223080d800b04007441e0f0601503549056a84089281046456600d090250141c003610320184040c1145c06280305045a0041e80241408001840303880030804501441e81e1121400d900030700c101e0ba0350340703040b810a40540c0003240d0303000303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 263424352 1250 263423102 263423113
    0x90603050106050d0b0411040e01180b060d1a070905041b08090111070206070f0f03050301230d111f0c17090a15210b031e03030109020c070f121b0305 66
    0x6071f03143c0240050803103415038415628100945480c00c03d10500c0984101c84248440c1407640782440d403560040201401d22401070300c08030100051040e240b2440e40498044032500d00d45541606a59020f11508040d03002803500c803000c502280d001c05850000d001f1502c400840d1b0b00c615010350300341c81003407c0c80c0742e409804018560040c10208018600140144844418a6081c1e912010100015441500040c50200041c0303c038669900c08076901044501c100c3d050194500c3c04581c00d16007047d80507041440101081d1403a443d0359103c01c490711300b039050120400d01260ba0103800310300d100380c051351020320280302481d910500504032071103003c0c01040c00d05c0c410b140003885001c00307005d6641c04007040381007103001d6014a051000d81d1030341c409410340454203039841e0003030614100140b203902c2c14040380518000707160307440401103e05580f4661401341c5c1d1940e10000c0300b441c10b0f01d00e901c0700455600c240c0b400504004502001e00000b8890003404c886e2080b48200051200c0d800e00026003680c100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 263425602 1250 263424352 263424361
    0x30b03010908071a070e0d030203220f060e0f12010b120304060e0102070b0403021c080d061701020a080f15030723010519030f1e0f0b010c030c110415090603050106050d0b 75
    0x2c51507c83c1d1688680f0480e8542151042c2d0102000703200300054007441450f403400c0c82000c0820030700c20050f001a10307055000e007a2a100140b903004524074218000c10811400e0105803a00303401c10070380a00040d04181c0d40c9509113030b2013503a0307901501c5074100007a14060660032941c0301180c180c0071541c0c412082c0b401d0030309680801c2103850a070401200d1102480c458480020702d880c000d008134a02c030020006005240175400070740c510003075140d021542d20400607a081d5540005005410000a88161104d9030740e42c0500d2003444450360001e075141c454800001104503114681d451440e4a21103024110758100c80151210700425802d03c2081d0364110001e41c00b54402d0340180450311707170620080390240c03ca1122105912041c02c00e542d55a80f50814281510003038000d00b0344941d000e01e000052100d04e600c00a01141c03079010300400120080400c0b51050b59203070071002c40801040d440706c800c203685a03509030050031140b00c2203c0035420240b000800c1c3c40d0040c03002c5916604100c10003c0c40c0e44 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 263426852 1250 263425602 263425609
    0x19060609090c021603030c05010f02040e0a1d0a0b01050a0e0f04030f0e040c03051006110c040f0b03010e070f06020a03050d0f1401080307141b0907030b03010908071a070e 75
    0x4802c140b0000c52080c407010400c941c40d007101d21070080d4000d0315050030741e01050030490b00b035841c01c007a28401c05004200810180d1b1503044007aa1000300041c00040c03c603004806200c0b4202d102d14046401d01c07400c420a0300340940030b5181d0b41240c9040382d842c803100f40e45440fa541e203e10304030307010400110354100007404039008101e04444191585805124145032400060440303d00703e04110010b03980d032007004001d4140380c241e800a0541d41c20203004103045950990f0b81d07000c0581e440ba009503161601e00c8402c0340c0c2500529a0508010000d005214020129503035500d404c0c814440c004025240008520317001041c0790f16801d8151344e0341450903698001000140640342c80308011150b842c82c500b00514010380c0c550b0301914550020b103550b00c10701d050a140e0b5000c0529a001907800214020b0086200c04140c0700e0444810785400070300740d490398404d03030003000a10003058055013400c00c14030400c0414401460b0f41849001410300a41c816800c410544004881c004007150014603441075525 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 263428102 1250 263426852 263426861
    0x913020105130503030307080403170411010e0402120408130b03070c0209041e0503130504060e0f0709090504031e0c0b1909060e03042117030a020d141906060909 71
    0x148200e040090543d21030120345564011241c5200080300c003000d00003010303030218803941710300036214060703402d804c00e51204911441c12105240c10300140c105414419210b82d01994040c10f03940c100200701d86014200700310745510102c0800500d406144000c54503168500507a40104007950715080005855800d200b0500c40140c82503d8140300a10000c3e0071802014082405c14840c44c040d58032401019007103002c020b050740100c0e00c140c0c00c00f45d051283c40070141025521001c03105d030804450310b4004098502d2042e58001400941c00c010400043c980c100040f5001001c89808880e8800f0b40001d00300ca6506c0300403001440c3c0d00c2000d011601c622030f10a00900340d41c0c1e92042c0015501c20a90b2641e0880c1c1140340b8103803460708003250802001000e40d4404010b68003040220b0810030080e070380c44c0c070701c0d0325044184c1001c21000301c0850642503169040d5041000b0320581084070501d00034130001640000c503890031343c942c01c0000100d1a20294041e2500321000d07600c1e801c03070186c10100d8000c06070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 263429352 1250 263428102 263428117
    0x105070f0f0c0801020d09061a031b0d0210030c180503031b010b030f0a0209010b03010b0f0c0a02090a1a1c1515030f120f0507080705070308030c0d05060913020105 72
    0x148001000403da11800703100038940c540e009038000400c2d00c154680328007600c00d40320341240181d2507200c0c0b405440d03c010400303104040544014030285003000c000030758081d0943c01c0180d0020751031741d201c903041030b010307400b110100495403075a20b00c03d14504158180091540600ca415400c00c1c00716400380b842040d002c02c82101ea903800030800b01007200109281c2417000041009962001c060441541803040c07070580905142c0312043d1079581442209121446098518040000f0008000070150000d00c220b42d8410b030f0040c214101e40c00c0203100700c0e0141c011070b1147c509107007044415000c01e18144581106005c15040f81840480790780d180d641c5ea100380b601c02241c02c035841d21021103691070351300e0140c00510310610702c0d440d0143d810300b40110101c40c5c425040c1e0900c0503010381810070303a421005450301d2603070104005a8842c071528100e81440440c1c4e03c000c040c184c0100901004c102038030301400644071100000c110076234480d1b042081c9000c0a8800c59120304446c4400400f40d4401c40c01407c0c036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 263430602 1250 263429352 263429363
    0x9130b180c0a0908060f01030f1734030801060e010302040e1e09010203060d11031e1f06030b0109050c040e070201090c1d01062102030c04030507050105070f0f 70
    0x4000401610309505401c03640c6002044002507a4050903400200c0b082c0070740340101c0100300070314000c260341003a11410300000d0000c070041580c0d1010025820390701440f4084440351305484042214180c080c103940a04464800d0003081c0300144170003c900050b44441f60559525401d80e4a408420740718511203001c058105a0204804106152414809809441240e542089002d0380075420340000c980617041c01c1e20b69004005001003a654504403105164129480c0710003c000d0400080c0f4085d664545a00144401925054402c101150a150190000c16481c40d00281030f0f89035421070740305010040407a61a44018406403000c0ea006036480440e2901c1681707440e07101c07080c0702c1c0340b000122040750042c0e440b40b420303030200300c0250b401d4002002030b008103416500d050f100369901d00c10140944000c20001004040245240030000060301603241800c41d039a050903044c07a0055130040c081030f1554401c401001415521a804484086800101c02c106e00c0c2003070741c0c4042d442041203005448 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 263431852 1250 263430602 263430619
    0x5070e060a050303040f141c03030f021b06060102070f1a0d09080304110a0b03070818031312020306010b0a120902031609020d050601050a02102403030c0308060609130b 74
    0x54a0b1401c00c0180041c0c0b03140b141b0303899201d2501c6e9040701d1040401070300e14010111070589154194400d00306451280d8907080101e44500000d1846d8000d014a468841c983c00c92403100c001b4495020600a02540c020f909444815885648150300e4010510400140e5039240c07034542d0341c05904ea8043c00b12269011004608209961180d00c2280c20588007035030146410b0f13146c100c9038540f0319041001004040b03160360951501c80d4010300035000c0240411807500c0c0c0041c041c04209030500c111402d202d891280e01e0300040d2115020203900800c41d10484c0030b482600d0000c10801d2405040c0c0300e844005a5903000070399144082c0300003800d00d860040b40c0502c038074200383c040000c0d1a00070030081e00085400584501000240000b541c2c40901028140720003000043d030901d501003100018071080742004244800040c407007485281c0e001c0302c00d0000900842e404030400d607000b80c000f12801d0007aa5542c0c442d880c1e0100704240c511410007080c0d40084030780f8400e000301c54a50001151180e00600010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 263433102 1250 263431852 263431859
    0x315040f05060c190c0b04061d060903040e0c04080703140a120309030f030c081b0d02030906161b0b0a0f060609152f030c1c081305070e060a 62
    0x14504102a41c1c008007581c80030910303520711940201004e411500918080825808580f241c1c0c22819015001424203a01e4510641280c100b420b13040c0141d442650485100389000f029860b1650001e018100d0400f460030082070200048070246d90a072803100e409049628a1561075291b0f4400d01001641607001d11308005000ca004182a01f03110f440c2c0e41c83c0450b0001851074018008007008950300d051601c0c25800041a80c1e00200d0550b00202002c00902260407000400b1414011665503441c094000401c02c03041340d0010070302c0e5010701002d0700c0000c2510340400c1d050700c502d15103c01040003091400100c40c042a24120180d4010358001e030000340282d9000c1082d002e03541641c0080c4046283d81d03804020008501d455600385461610705003481c114500c0201c1080300030381ba4101a00406000d0500300f070001841102c40308d0754140d040340c10a1340a1070000b000420b9000640d40840d20310000038030b50300e1030341e4191810250f0001c007501031b00d41801145410380e100503001d540c10404410010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 263434352 1250 263433102 263433113
    0x40902150a020109021003091716050f07030b011703030708100806040b01050901060906020601090b181f0603051608070e060a212007021c081b0105060315040f 70
    0x1081e0558495001040c0020741380140700600307030000500000c041c9019441d41c081250343c007008071400c07420741d01182d46800d818448a40000d80c1031019006016280c181c0700070150019400d402c592191210840982e0307602e54030305010301911062940c41c0c1082000842051040e00881d0380100c3c009821071685856000781d5103850301c1114100d03071080501c00103005500d00640007600404161822940791403c1044c025101c0006100e1004501d07104e40000b685c5640d1a89d140d051440c03181208555480d000b40e4001054210b80100903030b48400038404a41144030b4014588548901c0003260107540818200b01c6581b600107000a00300605140b0004090b500d1400500400c145035031130b803407032510919403050003155003c0844c010915241e620503a0b14900032a40c90140d00e1301d0050764460b0410700114503035440500044d03003a070244c04184420040300038080c0854280c8001948550440788140c90700702c1d0710589c4c40c00d030f05902c00c00e0b041690f11811220903500c184112000e040e0405107030f41d207 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 263435602 1250 263434352 263434357
    0x708070204020714010b031209030a081c020f0d0606050307090302010e1915080610021f020f07061a03060103020906040c0e06211006230c0d050901020c18010504090215 74
    0x1301400799460361510609407400300301080803900e008100724034103000718000036503504860000512201c0c002c6042c800034484220901c200c001d080000f59911640001c0c10b05e5142d00080c03420710803918002020903010b1040342903a2040c0e02940726401c0380780c115001901c8a401c0b542c038003540320100450b1801213040a61543c0028064441c0340d095004040501501851000b00000d014003e903800341c4142a90000d902080e58404000b00d42e0110b40068000e00039200e41e455128100d000050b1080800c00342d5804290b1201d10700414210302e40144c4200b584804080c400a90b1069443c4089051b5240a03804041080c0c054181001e100a00a0225071240c00603130b2204042000005840039a162400c4290362043d4003c5400c01d41c0303801d2201c041d0203180d0603061258818010400c942d28803030b805084400c03607880d50382120340c03039204000e00031710552003002428014000c1c460b078000b0314204020410700d60385500c0d03103d100aa00700801c2c00002c100343d4205036401060700d4442084850003100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 263436852 1250 263435602 263435633
    0x705150c0a0c0f081f020c0f010c020a0c06032009010c020d06050609010503070305060c09040e1f0b0607020607110406030b09010e01290f010e12070905090d020307080702040207 78
    0xc0c03034000324a488480c0c000b040c05644007040701d8010103082c0c504139200c00b401801408204c2c8006031541f01c0c5401240c03814112411001c941d62824602c0002540c0000300d08041500c51596001d20b41d40318101107056650b42c151080d00318070303a00030000644c0c4001c0060304c205031041c50302800c000701e15000240a000c41880030b4500d180e852040c4016414042c03600ba015141c25001080c1448c95036581720354a100c001d00c07800039138801040310083c5980d00d412500c10364030302c8411103075070b103400b8410f030610380403074151441e122443c00d048074005042ca1001d0303ea0140c2c00510403810f0000b60b40b9201d50020300180c800350300c40c1d0354003408000078080c8600039000384001000000c038800c0440315103084508600c100c074004055030b417079014140c00b5078480420500c070690318289191112001030311844481501103610607245200b42c01559400101e040c101c841d030302014081900c607100205e8460205002002c0141c100b0031000c03012501e040010a0380174800340c0014545442a2100f60b003e481109 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 263438102 1250 263436852 263436863
    0x6101b03121a10080f0414030405060304080a02060a11042607060f0207141309050106150215010b041a0c07030821100e0711010e01050a15090207050705150c0a 70
    0x3040500d050903d420700c08074400107401c00c0401401d04400e117007001034000b08020091082d1800b4182d030b0080a0007581e00801c0003801043d102d0410f4605080703540c21050003c4010f1091100050b503121070740c0540c03139004200040e0603160509244041c003030041c00c4108c0303104000c42c3c60b040b00643d040411124004100d0741c0d4403018080350404009003488651342c441801c120300751203103d0b110750768559221402c41c0c07061070000d5034001c60b15200f800b40a460b8031001c80550301111004100383c000c20100c004501cac4080408080e0307207403800d0901901403401034000e4180a00d010140e001010f800604420701410b00710342075156039603240445988620756509840e10340303a4894010b00e00b9211020b400500020306100c565003800c60111480600402c20020040350321515a0303010f500b175210024aa40c0e1100034410742c50318006d10009007000315115000c020400100045544061080d500c00507880300140205910f094204a80d044219180e622070740c4040110212800d010003d4412961186 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 263439352 1250 263438102 263438141
    0x1002210408160602100f15180609050903030609060a0b0a031509050603101e09061a0d1a150907091415070204091e0b0f06101b0312 58
    0x5210141000d500750440742d060282c030841072005540200f08185290742c80c2c0c41c0082c49401c10840300300500483d88004411030300815001c02c11803840c03000e041c051000007402307101890365601643c00300d4804451000844d04103101040f482c0c03074050b16040c0c1160b401010004401d0319051000f8840d40440056004655240c405081c06254040707440300600c83c0101c00c011510700a00440e4171220b000502003105036460324074158411114001604c2c2c661561401c00c05141c0d07624040e002000d0072030084c1d0480c4c0060010759501c3c5014505984110750011000400902003513400c11440409810240c0d26004040d05c2d080d19101c03419014030079941c0b503913040c0c040ea28081a6561020000118501034000d40801d803101400140c00c49590960503540010042601e05107410b0f03500c0700008a450800402c0b42c0d00302480820510319020b12000b030812012034845004008400000701906c2010070001002c0403142d400c208031166030a4002e05107120201c1d00d100c03644007200c0700f600a01d61480c40b407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 263440602 1250 263439352 263439359
    0x509030c0f0102060f1b0703110f06010303050f0a030902040207050c0f090c120901180c031208190b031204090911060a050405101e05040626010510022104 68
    0x30481a400354005940662051000d40c0c0000d40303d860060030f0384503d007107000120320012248800d048148510310880c41c0c8400651500415081c2d1140d0080c040e4440d183c08050751140c0411503070b040b40e84c50f440742841c02c4c0d684091510590005462042490b564141d00000350301c0c0c0d400100031540c4940068044030308000100301d24440e200501e980a108010200064109010100d03540340800f6000514030395100c0c924036026161180c00e1840d01112412890204240644030f9400d59214180c810444110240304039185402103c0c241100101c00703040390300800309680000760121024090340c410b03115034603520320f065000d40d02c49610030365250342010030320005c14881c592400c0100c48140c9001c0303c8940041460250740280d0388103254240d099210540100b20300000c0c0da02070136011850304880c02001c0d201c0d4106203d5800403540061302c2d118080d51105a411458072444003500103a42044d09201186803464000e40175071140e400d950ba00844000942d500f144c001c070340c0b0565600d05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 263441852 1250 263440602 263440609
    0xf09060c030c050a0507290417031e0c0d060e06150f0a0305060a090c030209010e01020a0b0a0c170c07021c03020606060a051908070f0207080a0209090703080a0509 72
    0x8840d08182003600c0c0c51a60902d8940c007070220307201d0426070314109851b40c00d24282610f4507101c03803921602c07030740171801c91050405901010f02e124a0140451000c131400504006645100c11135003414110700c0e420301101c1d6070001402260304071040c0e0750000d080c41c040510030b4040703070b031150007403175142e2a500d042000318500300c074951000c0c00e40260440d0074440c1500700d580c5503008002c5024185038030313403000a4040d02d900700060018114940107100740c2c0c80016020b0025032107200e0b0940040c1a401e03800c050f46d40002484500540e115a0030341407643d42d402d2410090201100f034400300140e0315044519403042c000c18034092020314280d17660342c0c40700f4030402c010007820384240c0c088802c0041c03000c4080f07038010490395030050041e101680d844861202c02c96440c0305803001200161603059401040c2544442c401e403185000e03840e20444030710354000680e03440869204048103644200d061710010700b41047c030702d5001724401d011215026100d9540c1c3c143d036048020010000703040071803003840525 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 263443102 1250 263441852 263441861
    0x60b0402070b0a0209014401180b03070815060915090c160803070c14011506030e03091018053a050105100501020f010b010503070f0509040f0906 64
    0x55048404600e42511503031031070503541c001081012040d40c08921030849034000c0c1c12643d801003146a840d00c0300c403907103031502d4041050900d40d00f84203c0c0426200062102c01854207068507000351710303403181501d61070720300f401b4104c802c8026805001e121400588101d00300303c3d05c1c8440f80400c0c1d254007149004030a100009100804854001d0200c540201d90380e216015000c0d0001c01420113603aa614a40100e250750042e60034006080380c0000042018440e4420850340f2081c4c800c2072042d11f50301811031001c2c00c4e01c0981c21045421105080100903440c002c3d4080310f200c101350700580341446081c400140340307281002000d4011690700201607104403001207030304c40600f104a40b00c1104140c01d02ca4100c0c441c0550780383c2d602c0311100340c191844072060302161104041d80b044c02800340f854a0001580000c40600c985400340c824050400c010a40c10b01445000c071006a50f101d0440d65016000c885030800f03501e0032000c0c40300800440d841c079100c80c00340141c4485c400c1e2022414105521b005070071507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 263444352 1250 263443102 263443121
    0xa080309010c021011040608130b010e06130504151a060a020601180603050c0112020c0f0304080c01020606030d08040c0315231005120111030a050f0709060219030908010e070306 78
    0x3c1c51700c40c5400455000405860a480e0781d0301e007480b926524000525074501d034504025004420b4400006402d62034061400e01c1010251415220503103110a00000c0e07602c02c0c0c80083c0400d0860140811441e2103504c000f80d190500a0996030030810ad201042c2154044403244005800550060103000c0303040c41d904000844e41007080041c00e00d1a2106038032400c0c0e800d07440e4100003100704100c06110380e540640b1018107400d8143c8060a009040b842d0b540d50107886191564040d4441a0441c2e60021803194410440940603006080280404482041c4010021070ba4440c03900408004658410400a00c81c842c00300001759a815410007850000c1e20381c440b0f8007001c4074003020001c5002e1056140c0d03048030300955464940342600111180500500040c4107510300c4040104000c07040c00350802809200740741806e00058548010846540e5032600076038001d0307403140e4058240c558855280f440094041d150480000d40c903011349501303440313191001c0841c0b60b02c01c0c1c03018402d10500c0e11400307508 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 263445602 1250 263444352 263444383
    0x60e060105031f02130302040e0d180810020c0f0f0c1306030302030a300603150e0303010e070504030c0303051c051b090a05030102031f06140304020d050a080309010c02 74
    0x40b480c004090b40c1403074105254512042d07801041d05d000100d0800c03403450107180d0007030050002040200046544607204210a000103c0441c500c5c408c001340e480742c40d010780b4103000103420350690000b01d80019502c6440d282000f80700304003000103410800d0214160240524000d00000036141d0100019a20ac024130030901a240c43c0c82040000c2d000011140c1c00038041c103020074a02c01c0c0c501c80e030100e000481d401d0a00c902d0303030324002039424038130394850000c0e00e100c0c1840401d2000c100400300121800004030600c1688100018850250120307800d80d4080e070720303181c400d00c0c3c40d4485e07442d19800c000756841280810008a00a103403107010000e0017542c84410b10007000313246046004c031361290f610810b039640c5c40740000030721040340d8440c03801d440d024103c00780007550389041000d9056003000d00c0601010184044280100b0900c2c491044860b061030303492515421a10744e0340070014090502c5070116024850038880b4000149400080c0d41300d964131000001d000c9030b010f40c0203030416241c00398481e030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 263446852 1250 263445602 263445613
    0x9110307030f1802091332011103010b03040c180207051b1e030321090708010506030c040b061603080a060e0402031908040807030f020a050f0a0e06130504060e06010503 74
    0x42c003a001d8080c1241076012200c40c0179545552030041602a03003031002a08408804c810030030718140162010040c1c081301043c0160fa5034001003078034200e4414501d000c7d40108100010881d40d884403000c3d5420034000c80c4080401681e6041904003015400c1007110120740108444062042c1808200d8016109815440d030800642e00056144903c2e08403074200c510040e1103802d119141002511401c1c410b0010a0142141f1704210481104084a15000f1403140c1200131803054018002d050003508080c00500c03e400f41e030300800010300300704803226801000c10301003240400c440e410540015400f98031490075a0500c001c5020598105401c040401900388040c44010b880006182407401810890743e0103100b0607207041034152242e94400e060500c80c5040120512443d10508008544204c8050410556910903c903074492542ca289902543d031160800c2030b041100f440aa11070b82c000d20080150503023401240c120ba905880907500d03103999030300c142c024074820801503002d820101d0081a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 263448102 1250 263446852 263446871
    0xf0f01051e160f051303260f0423060313110613030f0602070b04080a02011505030303070c0c0b0a1706060412060f1d0303240a050d080409110307030f 66
    0xd0710804070640d0b80304000b61620350075005842501900e882000391400c1c526081d42d42e060808020704c1540610b0080102e04200710b100800c01d50031210070002c141c14080c1428941500c0001409512803095141854500c1049081e81e483c00194407032081c075007941d100e000060404401d5030755100c0c107060040400700030000c8049404031082c012a80d03c83c418902c041214504940a4060f000c0020612490702d01030204221507000980411401070b8003c129030b40c520b6201c031814490354031400d0382540040002c101000d1007280c91a00d400c0c0240e041113082607680030b200409034010100d4900045401e00d8010002088891207500218103c588c00e08050801c44107840c20035134110000d003500d0f591420101240640e800500107400380030b81d0a040088440e1480ea00c07070b40102c4001c2900c104a00c40746000e10452011500303010070281c00001c1c2e05080400f400040c2d01c01c0d050135a1400c10030710002075940c080d801810415504006c1d440d46909111501506442000321400b01d03813418a010344 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 263449352 1250 263448102 263448121
    0x218030f0c060319020c03120f130b04030201091506090e160b070f02090106050a02010c11030409022a010603021c020d060b0414041202070501021c110f0f01051e 71
    0x5580d00d408440710366880c2c50300013410307010303180304840210f825001044000c0074000c04030141030081c030035041140d200d550380704d0842c9106c50100e034813500241031941c2c0c03100400d003e51100b47e4028424000041c401c940f54803007032000038501c0c80590006489142c1803113011824051811482d02039401001d030070451840440d1110100d005592041401152a800b40010004d4456401d40c015107241c0c01541c40b0700005050b1b50142488901560070008040921486140005190100c82d80514201420506084041c0d4440c180016030051050740c02c10124920381500c0d02240031880000920780d155105118140f034580032102c45520f002000000582c4a08041814241c0c1c400b07000100d5140e2000001c00500c0681c4d4150b113404010802c00c010401c21440a1810003a076402f2103503900d5032900126900c1410042403000c40d2402c015807000c0c0d83c054028000e0745403061054605600c1002c120340d2401010707024945050f9103d100f4050f90303a030f030342c41134110010500d8004444d525100402c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 263450602 1250 263449352 263449363
    0xe12071509050316141512040309211b1e0806070206100b0901050408030723070513020c0a150603120c031704031b0f05010b030d12050709050907030218030f 69
    0x203945d400d1654900f218056501c05030341c00103001c0303211a003544520040009003c00002101c0c1100030840240011400700c14000d0240c281c5252101550201c205a0361303411000c031000180120249010800030881041e81d8460300d500741803c44052012900d07240010745811005031003081550016410b003c19010303552146070588202d41000c61383c907104200101c580c0d22450344004450700010502104200021302840030440006440302c0590313807141d02480d10f0f9080ba102d100c0e4000c20030001c0c00700e0301c43d40ba000313001d80a4501c4207a96038025540c0b60140700c141102c2c00e03d400c844e5104000d004101c0482ca070b0041040c3c41d03103480c1c05002a16680a02900c1c10000c5121884062000240405209000d141c101501004071800d0071000b505d032200d4640303801c3c0300c111200d5080402c8001c06042c001501584c018942d6a400d0941c90994602802130002a0041040044009011915444844206000b04900d5500613910f40b800c039503030109030390610313002031003500300c480c1103407061100150 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 263451852 1250 263450602 263450609
    0x203060a090506130302150901020d0606140a14070206040303180f1409100918170304020105090d0305070b040c090b010c05030f1606060e1009020304050604030e12071509050316 78
    0x28913444840303032800c00307924107440040303500f841c1c40c0c502003005107802c01900604048212024140201515080182c440191110304144044400d2100700f840c42d21035034611500ca09018007552412080e03401140013940103801c241c010418072034407042500030001d210002440c90207600d0b0348003414410000181210010110f124444103004220322041e41c440030001041405010409131040a440c1c40d00368000c2a01038660001140c107016142c14144100d9204a905944062070304014908000f551711150b4002d45c2001020321480c4001404200c101e4062400342401100f004c0c50300000e14251201c07010741604000d04105020300280300003058910b0308009800b4075894560b4503800c01c80200c440d180150a180c10001c00268000780000c0742c84c0643e29041c040e000c1c42c7e485052801c141e01c0300b0b640040880d400321000801080c424158602640002418440c403136000b0151240343c081a034104d441c5c0040a505010002500407054000500e410340c0603242c1e07460030b6251506230032018030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 263453102 1250 263451852 263451871
    0x120e03120c0d050403080711031804021b03040303031508031809061203040e04061b020a06050601050d09060b010f020a03021504050a020901060305060a0515090f060c0102070f0203060a090506 84
    0x304840940d21429075103000b00458040080e4501800c00074141141551600e0118003003070035880000801104a54280e90f9140b058179281803400180002540003150322904a0b088500c06090b4810500041009500964011590070385001d0301929400e07181d4803100d0306910404c11002244010394011140d11011698041e05aa039100420218810003031400d041e07000000c1d001c01d03165842440c0900903802002c080000340030400b403044c1d00170381032400000981d0024511200041c101d402c0a9440030043c5040b80c20f010b00c9060310302c19030308240801c603400ba4407800968281e59021555290080c2347d07200501080c0300e2a14040d481c4d4441900c0280c560300301d2800201400400c20443c59126070241c080c41041d80e640e0300c01070060005a6510b849807602c184002003518043e00c030800742041b01c040c11441c10f1100d404200290385a03d09198000c003080c404c0810801c000e1014003c0240514900e03525200c1904c109400d0074801030982a0b600d00d0101c0b82c8020074800521543d00c82000e6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 263454352 1250 263453102 263453137
    0x604020f0420030411010309030504120c170a03080f01050f0d06020405090c0c0c062b06090f09020102060a230a151d09150a02160f0f03120e03 63
    0x1201280282c0041d2542181c4035006012052006039584000c44c410f900400c89015064400e070011003c1c0c4460b8000a000204d040c4000d118500a041d0714105041c440c000301c0608958800d0742c080700c440d4415851880d5000308800381d0502d5080404940c1c048010401d0703814560500001403410380b540c0d091701d405400358110714800c00c1032960403900a000028171070714032440d000500720000d80c0701402200180c0101c00d42a880c508040081e90589002a0700c00f80c4e4170700e84450fa503001220f0b00d170460000c054603254000b1f102801485400711404120788081000e280600000e49041400b40010015515100060901803c1412003040115000c0801485500c0340141c1c42c0103440c0388641110b00c18038101c40060104030038101c010381e0340b14140c2d00392610b40d03c02c4921519a082003102841000402e03000450104256005101c0c00052504144a4801a0b101c1e00440c3d088160112244d01c03400c084001031641203044501520f0b4499011b1207440c035240d900c0f903243e0291445030307000c07000729 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 263455602 1250 263454352 263454379
    0xe010915050c0303011e091118240c1b130903051209030d0c020105040201021b0a0f0312090b0a0c020d03050705060406200a02120c070e01060809070504020705060402 73
    0x440449100701c0041d4200c980305d5031204018803500100703441c0100b80c003148240014919005006103440319951031132203400e00f10f82c0d5001c0c0104891194006070300c008428018010300c2807141e090b04418803040011512600d00d003c0003494588680740180720307544890349500b07003907840c85202164403041900102d124903240c0780549032405440c600b101c2c0d17408030200300815010000f001d80304124010303105000e20010b1440680c2201c2090750061b0040c0c0108210710242c542441c0d444041c004041c2440034640c0d5a1101c00e803003003c05030022160442d00f00803104178142c0c0035400c0c40203002542e161380d20f45144000007400c10000d49600070f00503400c21190364149070240d0282c1c1d0701e144c0c01509407180b41c034191605030020032000114210241170418510141080601582c003810b100350000d00120030181400c0710140c00414000c00c041c8611076000c070300604414a101c1c02441c15442d0900d050400303290702d0303090081640100d4003070351040c030000c00400c5002500c150442d4060341c00d00b81d22243c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 263456852 1250 263455602 263455607
    0x1109060a03060f150e01090506090f0f03250608060904030809011107060507082a09030c030703140d050304110f030a020a06020c0f030c010512090109021c050d0e010915 74
    0x4042d480315030301c0c400f0b4410000b00c507001d451812900c0550740e80c0b400c00035496030f00103641c000f074903002e05500058184000204e504145440048640005200c9200c400399203000925200c00003219007101c02c02c0300b0140c1071070841d541207080a045141883c04480c582040441c1c011800140b001d000c1000020102e01c10036429484160760000101c0520303070b43c03602805c00d24064141500c006000619030307030015403c1c10746081414440d0329010071a603000080302403d50384a030018503400e039050003001c0b02410983d4040151600551281c00381500d0350300c00f00690741c01d03c0e0034040d0460900100300200300004a130b03070a1442d5564800c039100d2034400461030200e0300d003400c030400094108851040100d0b499800195000019a08440305014400101c05140e152511004400d0114600f801050740b03500c2c101c0740690748051807000002e0030034421780005001c50084c1c41c400002102349043c50b401c1c000c050100c0d4401009030b09084c0700d0401754a0000b4480351040c4108038500b5682402041020b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 263458102 1250 263456852 263456861
    0x10c0606030209040f03080708060102100b04020d0f061a070201020c010f0c0501060806090106093e070f030e1f0e0409050304091d150f06040207020603070e040509011109060a03 78
    0x640180003ca1546000d151000c22000d0b922000e9011507644000107403010300c14a0100d20590703041c0d0207041501c0c04404003c2c0600052404558007076003d2128101000c4544103152209030203110206241e440d200164904c6009102e600e20511020000c2c0005130340c00080d0303d60844401e1915901460340e030901160b4944038034100070200e5080032400242c10713100164080c054440b1000801c0504d9071070300090101c0d100301c06024035001343d003080004000402d500103203504403040300c0702c3d803400e400c0511101c4580c0200300c102d130544944d2450301c003403651028801c1c0c140e02055621a032114000c404520780180074440007401c020503040c1c0d07054075841e541c0040362030f998004212600c0d90380301d580c0c580c0a4040da06e001c081000820118100c003400c0081e00c600c22246244242819890f49801000c03a88030041106411540800841c070050b1500e000441c0300b8410380ea51015030120701c00410003a1000030780001e0306681001c0b40ca4400d03c2c0300d076049825502c411107a43e0b40d188844d050907400351 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 263459352 1250 263458102 263458109
    0x1107270603120306030507120b010e06010504120807110103050105030c040c0212070b060310021306030c0203071a06090c0301060203121008060c120f070806040b010e1504050a080a11010c0606 84
    0x6002d24820401c02038041e0804010350388a181511001510740241e01402012031102805c01051080100080306081000356085841850150310340f98a500c460203244001d04021161042c00040701010720560004140d8a80c1007464180441d52421000030790b0381405d00070343c85c0701d69911076501c2d8070707117008120f580545e0720003108042e216121414981741100003120881d02034091215003031140e191034070803101c240e45030b48031302c0b58580d00f021401c03402014607482c0e000c2075110421401c07010031484800032950910034162081d03a4901759050010014024000d4180c042d401e00c01800030a80100582d00c40c401030404001f07c3d0fa49860308843e0811260740300e0850303405030100f071203000d25101000b8810700301e0200c091070141d201c50000b505910b4040300d840e40000c2c6800302240c1da502c2c0c280c200720140481490410900e07078403000020925000400841c1c1403040003e410015400e208240c0c070020000c00700a803206506640712005902c0d0030500c0241002a0a1745043c00c211407903000e00b014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 263460602 1250 263459352 263459363
    0x8120409020d1d0106060801050f060712020c04050c04051c0503090d060b10110607090302030c011413090605040b031903080907030507151e02100c0509040906020a1107270603 77
    0x40e20f42242c14000c1085000304000203164500104442c2000b00785088800c0c1c000e490f2510305429600c0c2c0501444808019200710f010b10900c0304240d43e01c07805164090100005d2081c1d8451810040044043c25110503245161590000070040381c000b10644840440070f0381c008140707100d145030803030007401c803019415409035904245074011a0300c11f2440000b1000c1b00b04460081c0c940382426241d111480c403000354103600154600c5515445500700641580755200424107014500c10603120448141c0c001c403051690303413103040001d86450f00074890907880c20307006030560303c183c0a0140b80b1148004030140174411080041103044804000c410025a0400c0c00c0d0703001c040d16064454144c2c2c0030f02031031b140092a0f0351420403513441c40c5010b2032400f003c140c00400070683e05101c40ca024000442d54007041c07000910900c0016200c44c001c15060620407000140e031142d40c02d0000e49100c00321003885200340d0200c20248191818500015968101d020305030441444c00710381c0350301078002038000505 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 263461852 1250 263460602 263460641
    0x2f010815010e130b1009030803010b0d0b03010c1805101b0c05060f0909061815060c0d05070b011a03010909020402250b06030105090c0402070c0302090c040303020708120409020d 78
    0xc0f144030343c040090640121629100b00460309001c4a8172045404081e1441c03000300f00401040c41e08800515005902507004103000780f002000a0071542114840004100d00f11540d07051600103411107006404111607040c003035a45404010001042c0c03011035610107601c8850740040c020821012801040014405560760b0324280d8502c41541144005070301505120020868501c0c0199100501001c01c04001030f8130b03500c0c0e000e0706100d8580120801d410000801132034080c42000d010022100e0260745410341d45201c01d14001103400b405038030000119002c202e482040500d1042100c0c1198440390020a0780320503400054001e100e44000301c01c000c41c4245060318051101d2400c0c0007800d000f0458480700d07544000905007616400c40b40300400e9080380c0848000f5182507805080c0480c01054000401038995000c60840c12040c0c6050f13007500d50100301081050ba040280030041c1c11014054640440001141e400342e0059004450445030040b41150601ba110341c01b2628020010401c0003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 263463102 1250 263461852 263461879
    0x16020d03050c0c011b0e0109030b0402091018060e060d0203210d0606090302100c08041a0705030309030306090a0608070501110c03060a062d0b07140a2f010815010e 72
    0xc11401d0202144e40860b074030000c4c6c900198003900d81301040f82e03001720b400401c0c0d41e22a400c00040c0c940c0204940c113600c20b0315001042c6804d1240c1c0008600d0112500080c00904054180000e05001061079110310a038008000050320041240d01d02d2000701c95803541030a4190040c5506c0c0d0140d4100740da40c52345020f80008810b50f100c210402201d00075211150f1500c5c00f10170845030564074010207000354508000c20002c1416044400e103e060422220500300090755803501d0075644251a0801b082d071022083c404c2c2441c0074104142c1011190b1410400c4610f0304d2901350f1992a00e22803141400303141c180d85110060140410680801d0003010744010b458940c0b602d8006020300d003c4d0940408030f00d00a03000030380007064488107900301c21005c4001d02d850602050a1640080c00840d401344141c401060354090401c0b1501c0340922035600c42412900503401c01200004100308000c5074090289130080d40c2e40c001c00c005410401062400c00b43c07980b0140181c5d1502030150800782c00501c2c44045c60b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 263464352 1250 263463102 263463131
    0xa080a02010b1f020d080903040803030901050609012301050d06030204090c060f0212040317040e01090204080d0e010f030504020f0604030b01033c0f080f0c010516020d03050c0c01 79
    0x1a91084809000f9402041005003c000307041c1100800760b4016004484858020070503180e219104030112407415845080e03e9040d6001940da1000c240e441c0c10902c022451718140040c050280e856100e907110f4a01032600382c40300c0c0900700081c140900010300d050000c1c8150490b41c092b5401800a10910b9142c0c40c103070f14142c420344514000150100d104440240c40428400c00769030f0194440c070b040500350741747c0d880b034504007103240496001c0400c8001001070b10107046500800c80c02900503116172402c4001801c21501405c51010014980c020b024281c3c4c001c51000d002500a2400080658492000c2121958400030243c0c0c058000b1400104000104646074180c0e845090809a0b42280441c0407142000b654882c0444554039141e0004021700c074000c04c03103800d00484514292910b1500c4480040d030044a842100d040006590380c480700d400d01a8641040900f200c40206070341c1100025120004d03108030f2000c05888902044000705400c041d600d4000b4084003c114010300c1e04080c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 263465602 1250 263464352 263464361
    0xf0602060402090c0a091404061505031b031b03040f0c140a0801060b030637051017010915030206030a051b091809100e0f1018140a080a0201 62
    0x103d21469002000400d5407403042c0507511450090344551810301e04110841480708201c20009800c5540c0b1100098503550000c03101030b1041c102e403182c95590512044489030300994600100001100b00b0500c00e040490081c0c1d000450210060030362261a1840e00d2a4031518a035005080c10503202030200d0101040c0c2902e68030200c085840180ca0b65507015028280c40e184d00c036808401e041440014054103002c00b490120180c03444a140e40c85c10011194078000345828610101c0c62a54803052006092010045080f03900c0b6090900f0301c0982080e4070003d2117014059000382e43e446030716414010b4000078829000d19401001651241782043c80100100011101181c8c5412070601c07140c6001820021500c1d03201010b000c03541455043c80c490000700001a0080d0624070032802103903d1803681740704038005d031042c0e04060b20340c410410743c50f5480c1000c20b0401c180310720301e0162a08801462031214101d46503014001e0b03e201d034281c10400d030403d003040002618800c0005203100310309906521 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 263466852 1250 263465602 263465611
    0x40f0f0c0509010306051c060b03030d050c0316050306031e07050d08091903170a210c09170304030f0201090e100317070816080d0609200f04060e0a0f060206 69
    0x28204a6290340310208070000040105032411041f4441645001c1030780d6400200d440840981140e00d440c0d100800001202c2d812500000d00070008014062107040c84d099114880f0024540315095082c04800a5100c2804d030810241181c9003500a001c00792050114000403c002001440001154200f01d0603590152280d2846204a6030b103a070018080e004851041d40d03000702c95094603c8141880c09600d9100c0c40c407010034400b0480414040b04024400070703130001480480491100c164031000b03072200c1d440c0c2d007042889050745052442000b40000c10344040307a0b0000208104500580010b0b99607180540248a41122203000c1100c0c6010030340b4400100e81c840c400034403400542c260341801d107008052004000440070812615004641002c440c0350f035000c0d9245515042004c0003040c101c030104d0b480f6603807250311598203e803d1a01720380c49120309221656124038102c1200952840303486103004640070b0106000d48034240d9160f00e0003071303c0034040303100040c41c80544419006e03652b82e500300d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 263468102 1250 263466852 263466857
    0xa02030d05040b0a03020306040902040203070c060e0c031f1407091a0703140304050705060310140303031308031b0a031413050601090209041404030c030809011505040f0f0c050901 79
    0x1464418464400c40442e81190741100080d8101540e40303c0480c040d41c405841b50ba8099210018000035030344920046001d6105501c40c403041c4101031074184141c07403410f0307012061a000386d40400350079200814800010032540301158018184144814001c000c810b510b5103d90411108219075907420620035400c0d42d07401001d003804400710991b80f1280d0321508400400286842d04000000b09440c006190024070800c00c0e907520707648403801720b1000c1e0400c580c040006446000c040202885040c02c07035a62a1040d03026500c1c5150490250300380b0b1011540040001d040040000c43da46400441c084604c009940c55503a904070011008014140900c0c1040403240c65101140030941c0d0210004213040e8014003402c120ba10b006462002900140c00c2e0039041501c0c0c406144840c03445080c001e200d01d01c69219081c01e01440d003801442ca40000340700c0c50b42c45c1c0c03510001a841c01041d00c0c6200491740e0840300414600300c6001100c000e000103000c000340343c0f030a0161740e07080b00e0741000181000762001ea = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 263469352 1250 263468102 263468113
    0x8010806010807080a03051602030d1e020a1a07110d0203130b191101060b041d130f1205071b05040513080904090809060a030c0e09011d0613020c0a0203 67
    0x82d0001d548440ca644200701c4564000003452001034026405403801d610708140d06403200170140c000c00d040401d039094840c009500321200c0c819900c04260f000c0c5034195a84000c0445a00558400d000c40f50600c80c840300818080f000205d0f001d21946001c4e030041000070035211003031440310002e0750760b03040104c0c6118034503a05100407a000e042c80040d0b41c2060800210f90300007115104040d80c200f450320f00c58042c81d5403902d50101d21346c540e0100900c000d0000790300f411050030784e201c0022150f03c80541148402101032001c400820440301c1440e15075500600107401c02491000700340c51a00c50601d0003030600c11030070700c00f01c1f403034a0100c0302e1821220240c9040c80b403592198080c82000e01449001400c0c0e22007400482c2c550f08182d805450075900c24012140b41031074240001d0030342d400a00001002075202c0300540350540d840200341e40214025290384500c1c0d4180181800309030780305015404030011030030001d03034195644a900030720034221100c11981c51140b021043e444400a100503406031140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 263470602 1250 263469352 263469359
    0x2090901120b040b10080321100b07111f0509010f020f1b0609041104030c120206070303020d14010801090c080d09051207031205210105100e0109030c060801080601 72
    0x1181c1c0e001c0c81650740000020190b58807640e821050800140c00d080d040180c62001191001c0d040000b0401045022103a016400403c6c0700d00321414801400c01d8150700d1100b00802c01c2804ca84141e582c1c440e842807a0a1000681e1001325090581c00c850b074502000401d80424038440e000001040c0030f030700c00e9031140f180c003110403402c0c0c0e600d0382e0304061202250b000300200020b0b07403031200d81024125802442c1918101407100041d040c0c0c1e00c07401da521008000010200100400c07074201c14018441c3e10381c01c003a0703020750303400040f900e00810102806158000418400300c1030982c1c03001001e903240b0994a0081d50710340720514002e103c031120455a8907c40c500116600c0000503410448520650310794090b10b042405018018969024036907030361003818400300000320a8000d80c4001382ca15580c4949558006135404000c80c5150034040401c586080140166100d041d64603180c0d1845052074840342e03003c0320040b201c0c48800d500240c01d01041c1032011072216802041c46040f00c0b1684212000e590700c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 263471852 1250 263470602 263470619
    0x60a060806070e300d08090f2b1b05070602070602061311010c0822090207020a0306180501020301030b01080c030f150c1b0705031b0d02090606190302090901 69
    0xf0010758691107540c1d0761a0341088910404030785414403820b0044001810b00742002854682c00c0e01c41203000c0703810541080110309017084800d00544a000003030514541e180420b1b0a043c48a2900c00003401c41341c031503c034070360b40500e042a51034005102c089141a8903030070100d44034481070083e400103015458001903064800a421406403c00d030f00041009462956000306800001d0440c45c1440700d002d41400124a0200240c045140f2502001c0c44545242c00490604101c980040700401d205200100240e180c429000d01501da2105001900c80341e4400305048040400e40300800035800040040100982d0110303039030407141c950003291401300c031390b0080584680403144008401e03401414201d0034030300000030319a003000c5510781c55443e000b0359803102c0c42501554880440b05920060b0100030700e0500300082c9020756a4503071752840c5804000001032040b0700c45000a07100d50400400305139141e0b160703070468035000810881032004500004001e0080d400ca01002c51041400100000718200c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 263473102 1250 263471852 263471867
    0x7061e0905010b040c09050f1c0b0604140f04140c06070302030c0c010806130519020a080610030e030d0f060b0c0a06060503030708030c13030c08070f090b0d021e03060a06080607 78
    0x500306d0703c449070b00e64100010300440d0000d4408640d40074403202c5405203850031103013030310251074014070100d032030381c5890001d100a45401d440319503090f06022041144075103180036032513001540080c40c0d8186404000096180040010005a20000c0060194101a000001007132034644e968161094000580b006440320981218229004107041414585182c803a600c10340e8409280a07225141c034241543c10022a00800b50800c0414030210074070002e881d1903140c5c86280c80181c9800d11200e89104150303502c9026004054a44513129214102c00100310f0300071502401507036680d5605c80d6403c4034241d0f45c17068001c00c103559540c0fa04102003154140801240d240c603030801d05607441c6441e24190200103030721a0303000e19907488007000088001200d0034640e80061503141d0080c0f000500b00b40c0e07025040345881d400059031500d00405802d4984444111403200ca8040b0340702141440131000850019641d00c0d58240c0c54020401000004040d5a0040e4183c0e04094119952555030100c2a01c000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 263474352 1250 263473102 263473121
    0xc090b0f071b050d1202010f0f020c0f0c0604140a0b0a0201020a0f0f08010e040f0501150812040305190206070b07020d11011509020d020c190b090706050a0507061e0905010b04 77
    0x1013410250307102080c02c6000703541007111588000201c400030041602e0446400382d04000c90326800003050915907504220348210144d031f0744081e1482c41d03100d0000802510480c07107051403005201c2042c10b2191b49404d107034001052140029170361103084900c001c0c000d40c00010001d01003140b001d403280019114200f10700c414146610b9440a0340d0070302c52115400b50000340101c4401407004142d000090080c0030b84d50705011001c0e0228034070303030911041c02c0c28004c41010407034084105010410100c0c3c0001514080e60fa80c010014200c00101d0021a1750f80c4500c0c100038203450003110602103820381c005640390000c00f540d941e80d2800b4064150060036506201444a001000328000740010340d10303079004142a03020b041c401846c0c048905800350a25100c0e411700c501c1c00c28000000001c2c0001000041e611182501c0540b0a4504005d4041c000b80218200a030400c07901240c0c240403c06103603c008101000d503440c4160302c11550f00340f0300c0076181e07a8808030303225420516001514201400768001c078 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 263475602 1250 263474352 263474359
    0x1806050711030315040b1809010b06160210032a02070501030204080d0818010c09030c080607080f090c0a080c010f0305060f01030b040b3a030f030c090b0f071b05 71
    0x20350704e400064000035440000e0a5034003d40e034860303000d041d0f40c81802c40704001c460207820088503d04444c4c00c0782101d0b03098001030b020349001c0100c01800007131442e00741c010301e60464112220014040c0124000c0884114285100051002000769100c01409410084d4500d9085802d21900c44004406a000381d00c42d03001142d21040810444900901d038459109240e1440c3c001c0601400400d02d096032180d170408804100003d00c24030030700003207007040805003046000400041c101070100406c0c007040240440088a0a400411264401803000880b1482c1c01020784403d5a187c401054917440c20400c0540070411004451080314004c1c000d0034800c000042030850f0900e048001174024101c50300c40c1c117034010f64500508502c1da5845154002e10201502c402e802100741c021583d00c1001150f680c0f403c80c9040891720800283d005481400708001442d01003441c203801d8400f170711044055000030900c0074000c903941076a8400c41001d0842c56002d0741e5081c0b0500c010002400c000e000500400b0741 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 263476852 1250 263475602 263475607
    0x150409020d12300609090506040206131d010612062304060b040b130b030c031506162012030922051005090708060904140a0204180605071103 62
    0x314441d240c2d80351003044103041c20f1042e2400c0d194826640742c6a5014488000310014020070440c0061150b1009008a000204602400ba4803000c3d81c0b400c0052000b84502c10002e0315090701002c0f1800400208103109900080c500d2000c0e01104000b4240101d0000507002c40801004040c9401108200c4482c840d41220031031a690340c95a44140114109420a844610000d9401e642c0c0340204005c03c4160441d540720a60101c5014100c900ea51001e85842000c0c810b101401d141e00c0102c80e08031809a4905040c800300303601080c140d00843c1d408010084680e0180307814004405886c2d0503041180800b0303045024a40100319a0402040d18a501a4000e1024000174200b90032444c011829900f491582103820765190300a90704200d80080800000780010081c0f4180300408641007019070400c5042454034201082c6030080041001e007110a03250140d0929603014403920941a80103841400041c545641010103800303016000c5408a02c0c1c13000040b9614812196440d180c44100082d40c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 263478102 1250 263476852 263476879
    0x1a10050108150d0b090d0c051906090501020c010f05060a0b0f031312020c031204060509040b0604091406030618151e0108151803120a0f050f15040902 66
    0x45040070010160100302101014030842d66582d4019485101d00c07640b6800c1c2c045c981114101c4c00d20380350082d280288645141070600150021078140c24803e50052441c0e240000b0342003000241c03ca2000152031944000782c01000700c201900995800e110b0341074248134540351003042c01010300741c40c0700305845d88805001c0020600305000c019074008205442440c07098039140c44014528101055000160707203c65440d1a050400740f080099000007421628103162030328401500510451619510860b5144001e10342c5665000036a030280120007401c0190210b41242c0812407081601c10700d00c80d2043c0c00c001942c40b80001c6034203e80c0800f80c8060b100b0900341c00381c1d100d007024010300551902a10546002030010340480854000c050f01d4000b408107440d80f07a4801640d49000d04206000b040741541c03502641800801c984154501c0e800412040da9500f00c03900041000000522038241000248611824000912401003e405c00303c2c0c02e0224550702040120741c003469000790045036881241 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 263479352 1250 263478102 263478107
    0xc03080c070b04051e0a0e09100c03090b040809130507050705010b0a0f17010e010218040f0509071802220617060a03060513140106060201180215250305071a100501 72
    0x510390178028088114444d100c040402d00c0d000c04035074a603030303503881f00c03a500d560043c1c68003810700f1205990500b080b1040c81c80d103076128240c030001c10141c00c0640005903200503844a0382089020340d4892010083c5050501c00100283d1295070251555030038200102d0191900c902e4680c1241c00d2000350452a916006901140d540290112420b95603200c42559460300280014502003115421048640e80c0c00800c102c12240844110b08400d490401048881d150005241055403d29074a080300034503010301c03e40c082c0c401e076100c0400f1540e40d10404000c031000c1c4044041a030310203880f0548030580c181840800e00c01c04494003540210003400400100c2c6c0c183d03110350303005000101d048408015a0300e4110b01564800103015084c1e40d2004100000395084c42095100c84400c0c1803c910b01c031503500062a01907040744043d840a03000144030240d03d00ca503680d54411a000c1c14107200b20b0011307060117045508441401c2c0e51088402c0c164030342d00c41e207031030750a48500119020a8141400c1c00e004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 263480602 1250 263479352 263479399
    0x6080304090c050d0c090302091303020c061c14060a0b03070f0c0f08070c081209010c111c06050f07030207081e04090e010213050d0305030f0903070c03080c070b0405 73
    0xb0b02041c40030801402c013941000c0c3c042d14600250940722251118510b106116549074000c2913203081c044050f0364800002d0b4082041003524004981c840d80343d4a080d20604044d43c28a02802545454142c0c001560003201110501c01c4034112441c2c078100303550310043c0401d03100c22910100050f0801d43d4078164140540340e081c8101e4012081310401d28010369401c0c030381da032101e1016580303e544070004005152003000b084031066107002e102c03402c18041d207001a20281c01c0c46002480007807591880d5880d03848514550880185c031184131000702c1c0490400800800c42036401c0c0142c40e4645000680d02400f90003100c0300725070f21280c1503191898070040400003100a0380c103125a0081080300003907400c1076025007614000748500041c0c0d00c0c84400c07040d00c0310b43c0c0c1d40d5020600031560828408003007900202500e5102e405460301040b2035039820281419441010b0005051404420021041c8a80c101c05000001c0c0e0b030000312001103884842c9501035000d2032040941c0046100a11801302103a400c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 263481852 1250 263480602 263480621
    0x3030204121505251b081b0c01050406090e0604020c15070f020a1109070e150405011701050904080309010e16090b0a0e0a11090d081c0203060a060c081c0c11010608030409 75
    0x21074104450325546e9080080e40a202c10440c591540c0e01034540d040f005200720204200242002c501e0503160a05c06810107815100350701462420000082c0e1135113540d01240c81c0380c1040c7d8152040ca2740e0001052000700c0040d83c200e00024002c03414030050500000d1348494041d0019038000c1c0070046074041108084006000d40c3c20480c2d0a424180c4a0300c40d400b8015816400258040c0c0340c604100c001046520780c160a0065030007090010481515140c120507006600302040d40ea032581d5804109000d00600f00510310544150503680300a072060115140656481c9042807100040f41c0d02000711901041c01608048901031000c14140380070341e4008808200006444c40c01c2c045c04100080c05c034060180e040e24040c1001034001296012000c42800344800b9030b0045055040c14408500300008030f001762014082a9040f071401e1140500c16510015020220004140c1d103c42074240945141880d10004c80d040c1c405402c682c0506005800541d9030310b4004504040ca4080c242d8042d050010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 263483102 1250 263481852 263481887
    0x6010504090615080303010503101a0d02010504080a0b01150804150b0a03240606020601030c1217160302060c0c03090d02180103060c080705091c0303020412150525 72
    0x1120340d80300001107620710000c2c44c442e40595165850720081c1810030080001c004485440c0c90800042c441040c91001100e080c1a0307240404400207100681d00303807185801061035881240d00300f000300481d1012f02c50580318080250000e030800b0341800c3d00c072000705680052201c0c200351495825040350340d02200030b8240040458400750b035240c40703a40c4080741c19042911071000c001152545800715018842c000d09039407005095a40c9980c0764038980094900850300344030940240203041c0308280c0300800350300b40c100058a41d82c182041c20001c0401e5684d0303048016008201c00a4282e5004405540d44061035038040c1d4504142d1a04000b9001784550041360f01801e1590412510401003008501852040000183d010101c6c003001d401144014480c0c2d080003800c1261030495111483d41c140c80341e1071142c0412801400e440c0a50190150340c00c00310000c046900a6028001025882c8405c0036200c8010015501c403020961100400000c0512a080aa02c40f242409109040b000324050949 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 263484352 1250 263483102 263483111
    0x70f0602190515190608010207060605011407080a03020d1a181509060a0306090311010b0a12031206090c0224010302030604031b0203010515030f15010506070c080f0d090e0108060105040906 83
    0x1024150103c0d42d1580200074203a41c0410270344104903d6110300005489c09007001142c0d03900d0b112100081d0b104024006080038408a1036001c400c2c000d8046e80c0a24020203803d12080c3d00801ea03004140c062a0805403060103840740c0d18064465090031540145464503103400e903e8002424000400da0290550360840c0d0b08040c0000070801610541501a20990380c0120081d107144c4c11500f03461a8200e082d218201310a402c0201030040c072809480c1980c941840d611422010120340c00401c500d52040401e036007868602c11070707a1b502048044065440c01003005003407102000314940440240002509a88a0404a000301e4010041c554024600001c00300016080d5404207094600544036610355410010403000745180c00d008a80c8a00045d0004002c49021000e2090f40e00c0410302c100c60107510006016405c2c020040741d40700180c00319404643c45035002c0908941d445c0a800d07140c0002030041d075000324615440d8007803035041304d107880e004260313903400c080400c0001e26030f0709811618940d66 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 263485602 1250 263484352 263484391
    0x4060c0503090d110a14060715090c060305012102030d03020702131a04050c09010801031205160506071803030f0302030a0b130e01180b0126070f0602190515 69
    0x2000d009041c55440b5680d10301a03842000c082c4030740c0ca0342541003104072091b420703400034247d252803054841040e0400007178a224100e114400000388154900034010601c0301c4000728902d905500254100d0707070031694000c40c00395004440181607945110081d03150304a103025041c002e129070058030300140000d0400c5039400d800c58400c012604d1001c04020b80c641c200d68100503626061040750f500c10805001d031403810f249070703000801a01050100070010510500c0f001203031071041e401e840c3c0181c000340351400ca241c0c00d030505507942d01088131801c00007002d8829649604a070146000104c81d41501c60003064042001c0075406074100501850b80a40e61711111001c07940d4079141001d41010321900088c040144c03c10450940301c1a0b40408002580078044400254030782440a04491210f18040420806100319035400300c40100c151701c662182040204041000900d501d0454001d0380840344201601d0510381c510b460ba415019165401030701ea03640c102da030b802415039800301950780108442c580 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 263486852 1250 263485602 263485609
    0x9051807080106050103110403021c0819050d0501120803040b19020415030b040203100501030e0f030a1107060f0912021f09030605130c051309021c200604060c050309 73
    0x581c044a5141e44405003085656014801d44802d1882d1018030340c0703010b0854000c20a440c010080b04581c29060000090030302444a0075103020118010f00c14aa034040040010600c2d04a0240a4450f600e00000001c5040e804071500503400d902150450450b80d6503161105450b0006011400b0590429011210400b00d44002c04c0a045a403e0104e88280556030050454042814240c0100e10410034403241403600c02c441404c4230700034640401c0710078170f2100e01c600b00590f003070703010070b49200c04500a903083d508610a103548160103030459043d603681b400112940480c000189011408596041c000007a000f11540000c1d4000381480c078030702001840069a1f682c90b41c08000014001e4502802000190f000b0310742c20040d001c10412034200283c4032038484a00500c10544121050850f00001c6a4207030800141d083e0020050108035140b00322044000c05907030070444499030749418903203a43c010503007000040308d03000d0845420541492001c0c0d450501504007078801348000d00c608036640e039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 263488102 1250 263486852 263486863
    0x1020c12220e0109050a0b010e060c0304090203040b01150c080403060b011b030503090f0c030c04050709030615051008070c031b15020405180f06010c1505130b100e01090518 76
    0xb50120700400d4640c0741c07221100844002401008001e41040703002d5006a0740704070300c1c048150040f142d899a032052020f40074034610465000d6088180003004000030b0004203580c07107041352400544451544080c44007107902d12010480140503030010301081c000b03e041c4ea4400d00e0003034010704086031403180c035403000d002d144040c01041300001c00000400c0035046081c03104010350090400103068402d100d00000380c650080c030400720300a039540e2000072800b0b44988000e82c011900104108200600301e2142901d4880c80e0081c140589210f8508080d0580b050001d03a12852907551800c080224543d400c98188901c0031360f24140115502034034021888240e0400f610881450005903a580f80c0f00c1440b11545030a001d81c140e4031400c1e420000c00402d0b0355600c0764030075803d18107002d404550789041414182d00f441d441c081c052800040100c20503084014105071400b5403c040e05079a40e042000d820401d0a0140c410000241c81c0100004041c603081550010140c0c00440c551200340c006840c5481c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 263489208 1106 263488102 263488109
    0x4090b031c110d08090a0201030f0e010f0504211407030203120405060403030506030610031103030c2d06061c050c1908010e01020c1222 60
    0xe540c288222408280c200740c0d074264031030380d000e0001d01c0200e00680c51400c901c00c010399030880e02d00a8070054841c1081000521303400405a004402500c00c00040040300f98a6404d5400e44607401e0003600c0e1b540907001d1000a06140c903041581003080000300f020002e42c4103182408400d030748081d9454408600210721a5915101d01c1d0480c0380d0300c6941c5200007072410b94014441007210100f0f0081c042c40c029a000d10080d2244000c140c2c4610003580d040303084082e0700d182080091080e00100c000a040102581d09000c04030300e00c90f003494140052004042040c0d1141c050f6104251428111031071418000c00c840d24114003c00c0000d105d280c012004880703c000a0000c200b0b00f0400c2107101417028010301e80d42c807004000c0c0c400d1540303107014544031542499402410900148241c3c1d00c600c0c0f40704004d04000c805204841e010343d0043c564240c040807485901e103422040520014002c = true := by decide +kernel

theorem cover : BRFrame.Cov 263309352 263489208 := by
  have h0 := BRFrame.cov_init 263309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 263309352 ≤ n) (h2 : n < 263489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
