-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4221
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:54:55.897247+00:00
-- url     : https://prove2.me/submissions/9024f235-7eb8-4e3a-8a28-07cd45c0dca5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 758992805 ≤ n < 759172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 758994055 1250 758992805 758992811
    0x1020606030d300609050c19140f040f1a071a04140a050d11010e12091809060a0c0c2003032205040c02210309100c1707110a02040906 59
    0x14100362031040c2c3c1a44a00300724000a200c900300141d01c021644050240300b642c0a0a00104107005c03059000c0d07413150300c01c61800410340304000313041d480039018065104045400105020030404210b1003035808071400494011641c0c14001d05113403861007a1300c405008072108401c8541ca280b22019600c0d0014892000e13008240c0d0f4032a08281030441d0b2240850740341d0400c04c40542c40e140d102c814441286262002017181030b1300c110341159074208403100c81c5140080421004a140d603102814607401c0140103030110607191450b00300d9200c48044a03021f403420315015071400004d00c64650007000a5100e59005800b00c4c9003c2c050680705030507a0026410303c02080003100041e00180d40e002541080358040e4056400c0070100016140b4100d41d03082154408018003012400450032980c3da0041e1406040ea20385492250504106010601440407401c1001c02e00c0340780e0b03114445001040c120041100a078480356421100e400e5605060103455122200e03e81c05840c0c540d00011110f440740c0000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 758995305 1250 758994055 758994107
    0x50a230d0203130218010b0418020c15010317070804030609050a0203030c070e011d061003060503060712050609091b04060f03230115031205070b0103080c0c01020606030d 75
    0x54420703640200e0740440e0407800455000b0442c01d0030b110f0a80d030b64103055207040542d030400003ca24035000300c2c80f484044011018507600140125412a01001100d07816a5441410b44caa400821a0217100460b245400110110241d0030f466003034442d416800707252286407600e99100c54001d4541e0b03400a9401d03020311440700005980c100001c3c0141d001550150000318034000200b404803205a00c17581c440c0b51803400324036030511300c40c960b6644802c084a0300c19003801c000c1c3c011030060000c0d4004603094800d0358103000100703800808841c58041803800c103003c1955008144207068105491058003540700d03c3c904000d540c80203007032800d5554041c00000b080341d27440220003004e540070740c402d450f5100d1520000300305941030030003846030702c0e42d8400a220300d006121305840503074400d11004c0c1080a0500c2420050342c403507030446e455960018103a281650712402c010f4141c0c0c0c05043c80b100709120b4042490301a500210340140302d500001e001e48010064681c05a0740c2c0300d10050400141e01c88030840b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 758996555 1250 758995305 758995327
    0x914031905060601090911030601180806070905045c0903150f0f1003081912060f0e060609090f15150a0c050f0706020c0a0501050a23 59
    0x31622024000d100801c05400d00340d0000d06840c40c3c40c0c2140790124244140181c40550000440b42c000c1000c1c1b800452410301b81c1f0040403191080d800100c0c250044030300f40a80300f644043c0c40e1069400071101007007000c60070044403034400c514401c0512410b56201c514030450036007020110400c80e18070002c1103400b0680030f401040d40d48085203105a04800b00d104480750070100700078061808009012889400c140d400d044011038000c0ca604146041c2c84000fa003c9261180070000071648140381a1b203e052440010444000e5014500c0008a04020740148024240900c50407a251070a4500c299404e040c030740c05050341c0007424190400781c01c110405494840d1b03264580306080c030200d81c0a050900c9400078181100148041d44900c02000d04420000d441004540e040307105400e01b4182030042d8507005040109581e81610f03036014125000501a40103e04048171200850342c1c1c540e02034a5600540d540d00074211a040041e40e070001540c0346041c44012000582c003000c090504004071905 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 758997805 1250 758996555 758996593
    0x1e010608120c060705070203031b030910030c02150709090e010902100801031712010b03061906020c1203030c0412050a050106171005091b1503010608090f030406091403 74
    0x1400c41c41e0980001511801c1442c1484402c3c0c00103424900f031850406141c00007903990162804002c0549001c0d043d0b1300401c6010800c581c1400c1000c0d00c0c0600a40b132994020b03000300380e0001641c0240c01403001d44103409241000750b620562090700d0711013007641440d0134940280342a40b841281c56589264000150380c481c4d64105550640f951810001c1d03045141c0460076a4105580400e4250103100c14110703070240880d038905507000780b95003d441742c0d10380002403039910180200c44c1003c58045008a46180c0c040f038401d50740304056840401c0101030a004650b20701c01181c214004450500c401e00c6190004071411034501e015400b00c9015071015100e81b421100c5a03448503038a4151426502518a014480031082c0244034404224918100100c10749810324950f407c65196082402e00c0b000f542c0d040d05c0c031041e03201e108808588035a100c6c02c014246100c2076407101000d03c14441c007508800030000c200c40c01d0303454030354550184500d00f01103020040c00717840020360325004242081401d564001b0f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 758999055 1250 758997805 758997823
    0x14030d0c052e1418030702010c06111314100816050a050c150103030f020105062b0f1505010807030f021009150c0b0702012307091e060e121e010608 65
    0x302040095081804070b02004c2c0c14048580304213034109118001c0903070f0300044014038494000e000819440014045c200861040041c2c81d00940c0024201142c0707404081142903214100b510202d040100541055032036020844da054110350a008004030701c2881840038041030302da01d007066030400d640c586880d42044412030890540601d00001042410ba1141c00740020030320301c0c0000c00ca2800c01e80081545420740d910005080c1d80f106110b00d800c044000c1c0d0035800540c0142c1507903010034079481d00618149044900d07403045400c0c0300003c03076645000f04000d8116540710310214040c0a8a600f44020605100c800d8814484a1034000070407610310700c0c0c1030070f104040b9a504281c2c0c1000c1e20780500c240130054651421685020a40452407080000c00c0d0900c140c9841c1100c226030345d003d42101c0440d41e58001529108000f4007200d280d401d10030000c42a204075448104031020303804c0500031a08081c01c1100110b138065030822680011202c0c1100741380c3d41e01800800c01039100c40c00300c3e180802c41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 759000305 1250 758999055 758999081
    0x1806030f0603100908030a0c210209090a0b01090608070203163021061d0f010605090612060a051c1a0c04051905040614030d0c052e 58
    0x440400c84103142c2480521075074038549104000c070303200c81e880e800300c5800000c0a00c52000e0b030301d8018a019601030308900d084412a0aa810401c15020107030202941040001901401040002c0f4420b40c40c14041c01c620701d02d040e074800e82524907000c02210584c102500201c1940401c01130200d840324030154000940740203104031030440d8100106c03c00d42c213054041040740706503642c9010500c00c0d03004560600c002086261900460360740c040c001c000384040d905c55090160010014852540d005220138400e40109000340c11507a6030744405d8a0510a42048543c06801000700303a84203c2086c0c10b00d5040341e0f016080d160410b4440c4082166010b03403120300380001c070f01b49001c1001c0051080c1100ca1012400f100d01444c2c1c02c000e802500d2501850003104c0c4501d418882000d110702055030440c1c01030800800920419988402d06030004c2c1e804100c1a02034007950030b00240d514042c0907615070742a405030080400c00300800c1002d24000c81202c50170a010101d101928408545019034858000342c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 759001555 1250 759000305 759000331
    0x6040605060f01030c09050d05010f140912030408120c19020f07050f0f061b0d030b011d150a091e08070501080f01060503071101090f050618070506180603 68
    0x98410000300030b044280b65810541801291070703074981c0c0080508200c40e41034440007400c600e14034055024098482059120741d10f883c40c504440000001a240030703038484419038442034100221603030326200454026002e1101004203c0e2400300d4808404d5220b8031900c0d030b036414a050700850361415044e01a01c200141e00c4081552203c0c98184130b000014041101c05240542c6094042641c1d0503002d17020a00c5200c01240020300001c0f070701c0d545407411601b501035079444513000c1d07805001000c5805e00350b03001900311078401184c07036000078085110210041405a100150034030800459101108000400c00d0b086e100080669000d642c01c0e00c40001424510780150800c140c9510b40f00803a8404c504210041060101a070a001c60560540300d00d890040d50360380c0c410006440c0c11030010f800b800150305c0d0011450901052004080d0394a01c10310946140391034551100c10038403214000c2d003c041d0440c0c103041140d4902000109400d01c900e601c0044006071203400680b1540089480f44440d00d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 759002805 1250 759001555 759001561
    0x3030902060d091b0305060a020705031306021f05012610060e222301060b04080a120f021f0f0207051b0103050412030b0a030204050a020c0714030a031202040806040605 74
    0x80302e591342030000c50442000400840c503645400d0b903110f9028011480f00703030313000600009120040c0110350310700b4050100700b1421560b0f030400a583d008285280c403a0b5180c0304200240d800220b0180034102c4000410301c004111140a510441903806c9402c03083c030340708a0080039024000703401070500625421224400c0784ca81150011400c200060003603400d40340c20b0705004002aa030741185400340c02d0040c110700c01851030200450040c9450340151000e0480442d00140581c4002103155a491180d801080402e07405441901c0c0107503011800800368004911002c62050381c01c44041c08500c00081c003040c00702c22998420200d81c00208141c800b85c021a1451455a10b1107003545983c01d802e180170006403070540c450700a60b104412004c0f04041d240c000086459449181440145400a000b0440e90521400590083d8802c443e0081a805554400110b0607424042d03001b411030054050000481c3c160380032205130200000b0f9910340d9a0a1001050168080006500c20b91288000084a007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 759004055 1250 759002805 759002813
    0x103031115061011121b030a0504030b04060603170d150e16090e0403020a0c0609030b060f0111010f0e150609150a0312030213120c0e19020c01051e100b0703030902060d09 75
    0xc40c0c40c01c0786d9155004110082843c1e80c010125802c89400c825160b0442d1118980403024102c154005040590b0280380780c00310032000c80c010200d161589800704007903003100d091601d2690350303485500c814001100000c1c442c50009800541c00d01403030320300301418503282c200c0400c030020259416001030348600c64a00402085c185030034041c009505022440900d103035112800e403034001340104d0107401d40031040307120769004a10319004090508000d02410000001e010300070410415240954854000041c005101c98a0f18502402c0003600711080e55850902200081c4601181035400c05100354000010a003166034500c0d600320a5a07001d40c0d680d0f0309401030203002c1100e81058001070a481c13621000603611583c031001f115010b80604000d82e0383d0641c40096628045d07071504400c0c1c00081c00d42d5040406600003441503804554051503070b0b560a01e211904401141c1e07408100c4400d017030610140d03800030b000c0c2601c0da10a01e0080340400b8541d0101e41d440d009202d406003415202d03600301e4200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 759005305 1250 759004055 759004087
    0x409111011030a03180f0b060f0f0102031b190303060f050a080c0d02300d050a02190f06020408011a031605012109030206010303111506101112 63
    0x5148034505018000c1c4209549626845407403190814540d5400d510603128150640c003402103a0096000010444581812800d00b10100c4c1c1d000e01c1410303001c00c0d0300d5007850f1842201151401c10b174025030230005601642c0b109030b281c05c4030b01c087c0c40c0b143c01080c40d00c10200000c98000540700303a80101f070981c0340c1032a00a02200d1074102d94031074800340500b030150540c0010700140030700c002c84100408001c1400499580b500c0c20f402803031404c20603050390a10009410048000601c0e40c0304440c406012a00c3c1140c6d50300405218400580054200805000c03000c05403540483c000d10100da075240c01e80d0340340d49c105c0c0c5c02a4080c007a42e03511041c0e203903014140d130004040d24900c1a00501080500348110700c412076000d00405060013154500002c103a4500801d0044c442c43c1c1003400c000d02500b03414060750303805092108038001201d40c85460021900442e070304295150589407001642c4031181005020403c640720401004200d11005201d0b6000300b100c08025058441c850380d0301c1650384802495 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 759006555 1250 759005305 759005329
    0x30705070906050609060a031b0504030212151801060905041104182d0507030c030b0703020708160303090501240b0c0706030b0109080102070803060f040e060402060a090302040911 79
    0xc07040c40c2403410802d90701d903a07045403180074040300c8507542c4000ca01c8041c0e00804000f411a200d0b04144940401c0f00340c0c000000b00203490088681e0301ca20500420b149940c1c8501c403142d002c0000c060340c045988100d01c00102c040c038100120010071040e840b85c5a0004403281214146e039a81c200405040c03c0d0300381441140b04060041d1400a011001a22450110000030a4451070703101000407a8a41c40306030725190400325441030913038400550320700348042805a240416501c0810809c00318017413a020344200c3d403055034801e1041d41031400e01071608142c80d4605070142c0a1589400008000603801c1c81465491080800b0100068500040202807800560000741c1280000c02c03084405040c0000c04c001110080d1501089844142c40101c501c01d11a40c050070141d030011481d00c0c20011290091481041c0c10340728803a501c4038201c200000c1e107015068422454101c80081000f5040c408006c090032501420051604e581d41d9010a08490b0200c2080da81000f0b0b004017017040b4a481e502801d6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 759007805 1250 759006555 759006569
    0x30c0a03021b0a0b270606010e01090509040b1b030411010c110402071211031804111306020f0c180a0b041d03041e0806010b071a01080d0f080c09130905070803070507 73
    0x111789011070000d90310314020301610f040c4103a0b01c0c00014203a00c103440007000b0b0b02c0041c01c264a24281454240e02080b4207480c800300d5161090001c40400810109403481941c001c01c803004050100b60064828000c0001c060340c2d0480f01c80b0081d402a2100d00082a40c40c1c4100c9111346060303540d003802043e02d400d804078242c0c142c1081008600710f98400c80d508140c00d000b00e500040961049417145140c0c40f509102e40402d4050040016040c2d4020855200021580b800d13034891210103001c01083c40c030002400e900d1080d401022540b100480e0707012420512001d08000b40c80c0c040d0b66040f6600903e0b04c0640e54842d800010b00b84007480750028015495010b070341e68110320324100500c80da11000c05010b1f10107114000302d58030f0140a401071407043c1c00c2c01d40749202440755840b69030f11500c0e582c00e1001d80021551a000c81c40d45148030f400101d2181e00b041500c681041d03407141c00c02c9201c41911540c0f24200e51030700300e0700e000b140081c4100c40c01420654011985e41700b0310300e4564100030450380480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 759009055 1250 759007805 759007861
    0x40203060f06031312020f0601050604061d03070b13030c090221041e030905090603060103080d0e031902060124020a0b071e050915030c0a03021b0a0b 66
    0x442920358214403400d00d4400c030b41c016103075601c41c86056010070350000d001c2c0c00700d050800031190868000c0b40317140400080d241640c1c4540c0c0c0b00c0041c0000c0e03201d0782c401d040c00505803190f256664401d105004200e003030300400b07844030707582d0301c40350010704e604001a90300e4010b036003500400c104003194007800010301394004158200a5000ea03040400003480ba2101c0d035850080d40000c00f0070403da42031040c010b03180c5041c003900d40b409040c010401c81d514041d0900130320260700403c4852a000403e00c0c100c90380501c01d20300e040c42054009014207490503009446200620110071a60008284404030368002c1d401009107600d003040000c016844840107183d40550201e00c440c080f540862a00c940c00d821001201498644260441c0d007050701400c254800f14800104501c51940000181a00c240031a08a100c0650700d2400c84001c1c0300a980300460311204000d155462806a0082c1030800d08030b00075040030039a040003190030301ca80400110358000388801000010a441e81c40d032150404030115503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 759010305 1250 759009055 759009061
    0x121c020703051507090b04090212090c130c0509040509061b070317070507020303070b090c03190209040305130e011805160c050709140a0b0f0607060905190503090102060105040203 79
    0x40383e112100e52480441c0e8480e000d0008040c2030149039441d000b8804103483c0c5560b42e0740c0f20f1218000350484106486007000c484042081e01800040350110348500804180e03016854146e200028100c0703002100c10701c00c1c14003c0c203082c0c1d40d541c400d07907100302014405000c03145043c0c080200e06c4c00c503004c0600b0080c0414800c070030100e40c3c4032130b806601d240d05900b207001c2501d684009480c10f0040150096040c48001819800c208031480900d0041030700a08485c0d0160401080640301c0b070903510761032003858084081c8005071030b0404030550400d001e814550b141900d800c14880c0c1104141e0050342c9400d951400400002a24803000015116444410412070a03c110400d10501c2c0e100600d504200e0700c0b41c004810301c82c003445500d00518102c4410841c500c03044404000122081300c00c0c4030040d1900b0f06c032040e107081496001c1c0d603051004020903c0c000c019907a41000f00703120700040e91305105c4d020300818115110941e00700c3c5540144001c589801095000925104050300b001d0300540c010301c14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 759011555 1250 759010305 759010313
    0x60112120302090a03020607080711011b032a050a0b070203070809010815130b0a15091703070b0106090e15031c021203100e010e0405100c02010b121c020703 69
    0x4400301002035180241e910341d030300800141c15018036003010354020300002e12a0100401603000301050b62040d0041c1c0a50500140152030b228000c030703a4104044056200350340043d104c1e50802400c0020720b00d046942c01ca101c1d00381c000b0710410b10f1045503e580041d420b20103201c02c110360700358045003a05c021850007000d07544a100c10700034ac02205040c42507480201e02e0710141c0b040c4c015014900a00f0b000341422030f59010001800c18400301c00d0051700c1041c40452aa05003828600c0082100d88034820300c58600205103240b500c0d40c0700e422009000c00d000040000c2c24455030a8001c0800d542c03034012040c1410341204003042c014040e5902400e580030425000d44000c100f080c0c0041d80d4440303886800c040440700341d08150320002c20b04080c40c0c002041111046104040c8016104a58081d071550303a04c036813407401c0b0581c05403405003083e40981c441580e9485680c20030510b620081c0b00100d410174000300850603010414408001d00d4010007020450106520b1140e400200c403840106161461512 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 759012805 1250 759011555 759011573
    0x408070602122107021c0923030303040b100e04050a15200c03121f0b120622091a0a061d070203090d0804050a14010806040c0e030a0b09060112 63
    0x24490b00f43c061500004800e18000c0c84100c1c40480702507034041c0d846901e004001c10440290280500c0c2013000c4441d80c82c507400d140200190b03210054000c6181da00c0340d80311035101d407900600400d400c050604000c01d108500d081c449015910400051681407180d141c0205841c07080b445031b03040a0b240050040e00300d600b8480e200e02e0a502e2720303000c554540d13410105038210301c83d01001504490050007802044d4844144400140c080ea8101611054039925000b0084c422040855051650000800d00502d00940344184a0070041401c0e00340c0786029031060292440c076074040d40c80310000c506c0c08524003a45245690b006009030350800c461410f11400310f024078042ea051310801c800210014080034007c004039900f1440060030100400f036240f408082c99406402501c3c0140a6400d0000e4004030703249048207500d005854840159a9a1b4240b0000705040ca4904081105222031001d5586003403004100751405815425900d00d030100d903003450504c041c2e00ca01513206080c3d408070003190300c01e8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 759014055 1250 759012805 759012847
    0x1d01110a03120b0303070c05030f0f06180a140a0b09160e0a150b0c0f0c060a0302070c0b0f070203120a08062403011203030e07061b020411040807060212 67
    0x424482e00b0703a0484108a4010203c0e809101c2c0c062200094071803e0290000c2d90000f00c5070704808441d28a0580d1404030748031034a060380a0810340c032030300108582c00c40545001540703100c2d8004490001500c0d40b14052041001020081310b50858031018050080a00b807855000a510000700000030810080c2103401c00b1a00c540a0591454404180c031b000c071030740141600c0c240e603449900070951180201c40c400d900511402d00e952003000581890500b001c204150054001002141410b82403e000e80207503003c09021034520700b1401e8042402d2100d00c010b0045404030b600300a0302c1700d0152041c9468003055102d40326080130203000866140703a0220070729501800546140802400020000c540c40d4034000d00c89141150220006c115000e141140044603802940c051200034440510180c4070319003070013910000764251000e0160704142c0c010345040c0e0340c4003a20002c0c440070205114600343d002a0003014071504901c0b010010543d0400246030140c100956251800039095504204140381c0c3c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 759015305 1250 759014055 759014057
    0x6081f210807060e030a12060509190905010c051306030905061807030f050a03030f14060631050102070503120702090a02121509100f0e0a0e0d1d01110a03 68
    0x440000c810400a00c0c10b03924540e520030700078090201041c6082d51240c100542d000009100da400300541014076004840c01c81e64081d01e180e00c90340701e40700013030075124112400040c0c45032942c03c0c0d080020400d1080c800d0500d185d50ba019280c58000c1001e0183c403080b0360000d010103007020310801c0491390110b01c0d01e4100c0c00249140546483c920249410500103600260440051255582c00d01c1004034413111034a109a80170440ba511218401f01152000c000c0b01c1150105400028910705080005001c19200624550b112084801446409508419000310b000030070000c2000b407541c0410610000c0d00f0110060440e00000210320111070103010f001903c500380341400720b00740189650481e80580d140b00d11000b0b8901d406080d0584804800002c14044c584e103400041143c40300f580c0c2c1c0c1046d62a201440e807052850550803017480c14015000300d400d9a034400010703102c21010451100c0d07c0f071060312100d961181c5103000f00c18540c42207003c5414801810240d41e228080481d54021075641 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 759016555 1250 759015305 759015359
    0xe010507051009030c1203060306110a2304081915050609070e0d08032e080a03050d06050303030f01080c0321030a091e0b010801020a05070314120106081f 68
    0xf40d418112a141c0174010050303d881c00c200700703860000ea41a000314040d28062142404650000454500184111001c402c0020b20305850111269000e000590392010b00045583c1426200c5d54401d0800c0342c2010030610000c8410a403104100b01c0d145141c2c1c6980b5480c8041240d490f01d038021400c0310030010202810424003800500d580e90719066001280c03900094102e0300c9113080316402d82c12104910019a4041d540f00704000d001100e814000140c07408940501a0711550b0f0340c09a8041c0c1124805400c3c2d01d40b2004081610744080001c0c40c4607a6401c4503107812545004292810040b001003141e0003900601503440030300c402c100a40d000000301a01c4943c0d655200340601c801028040001401340d0700e00c01c07030807204248541003600244d02410081c055642c0c0c40c01c4850803441850054408100148441c402103802083e1820346140064800c1d480d20120004491564030300340c0015001c101c5132818802a408001c0d03001c26000d2066180710000d6040c1500309201021043c04420080b02c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 759017805 1250 759016555 759016571
    0x50601090b030c130f32011d12061029071401051f050906090f0402010903060c1d010c05120a050c0f0c040c090e07030b0f1f0e0105070510 61
    0x3900703c049905459003044840815901d0b5228807500a10500c1956084145086524081c40c0901808851400914058002440358500558138511503802e046013810194005010381e0b2500071418007030640102c0074041a14007031340100441103854000d01c00710007003c09041980d41040b04012000710411010782d840e00d11a1401c490a0074040c1007403100c030350130704041c000b02d241101004151500040745407944c03192aa001e1107100582218499441209000814801c1491006030b941103401031508007100f503169111141a00c0c0324681100004080364485280003c42c50516400f0b540300b403900149000781925890303910400c61640c2d00c107080001030751149103402501210307070490316001030342d020303040034000151200003107900280501d09014007100600c0c8549800b10035111000d0320a1003907240c03001c0c110000d0010001498118610b10a6945079599014048021460380040800c3c0e50700102c800901d807501d5005100e0610206026110000350041480f0b03550047d45000091804 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 759019055 1250 759017805 759017821
    0xf03231b130f0c020c0103061e0b160804031a0c04050d12030b13021b07080307030305150901090b0102010b030d36080f0c06090f0f190f031401050601090b03 69
    0x120301071882e8100589040c0c4904501500840ca9444c0e040090301c040150541d5054030231803505080c8080050554610024018940b010001d0107100100e2540ca0607c0b0080e41d0f20004240d03c103400685080100403003194020400c0403042e948050000826400c0c40c1c0742102044070b00800c1c12005040c2461542600c407660704c03d42c0208900340e0700815640b1441000320304030000f54498254070440300340c15960b1420801d03000507010100c07170342c0358021490007803580c85c02c400802000c2e101440728180042c18070150381d155109180602010403001699610781e0300060f0840b000c100001e4001d4000c43d84c0c0c8080540c100e00e082c140d00850a0a105001c109a41d0101c80205910300040161070181c10102d05100300141d41002504100c1c1100d03103100f0340c0c4041000d00d01442c8441a409201d030000851541030004ae1002a210040d00c652884440f006d0f480c041c540c0613802c0300f0003810030a03c08105119030410b8846c40c2d40c2c1d03080c000704401d060840c002030942644d03000303480d0f02050000c0421000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 759020305 1250 759019055 759019061
    0x904021e03061509250c170d0608010c020105060609040c0302070f0b0106090611100e030c0a11030c0103020f041203110a030f0f03050f1902040f03231b13 68
    0x1060010269000b0f4900031044a4104212802642c090b840f0b4000240d20300c100c0a11040d0300d03044c49508200000300c121341c21142170010000c229800442d00da00107021942d1070000d8012241e8003203001ca807d90810f40038600b180e44000200302160304110038840e540c0c441745c04a0340610415900420b12072000401a40070b0711481a005145602d00759100703091100741d4040b24180d030a03d688001d0626500d8000712103107800460f181409800c0f11100030201d46d81a03100ea400340305c0140a50341400c004e084a242010242207060390940c80d000d64041c4903240138440c50300b00110900302141880c4060506011031b014602404c1203200c0140a0681410f014560a10349120500215590b80c081ca00d0b000b040080480028404100003108285280340a80075003486140c0d05c06240d10140d6a184007005040300e03401d00482e2080d400c00011030140d82680c1001d010b14022503208802260350394440e5000d0b0820040125580c00032014405800700e281110000305900b158034225914428001c1801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 759021555 1250 759020305 759020359
    0x1e0610090e2706010e0a09140a0b100618150203040e010b2d270402210a02090d0b06130914010b030c011704080c03030c1314090402 58
    0x40d401d1000c04001202058640400c502501d69080c07003107102403034104507903e070000e00030803003660140380018007a0f04d445d500220312180501a0b01281c55200c15440382040441d0101361050703020b1108101161110040c030078010001880c04005c204007581d0b500c801806240140000601324039480580c0c02d108200390f8028007048600075170381e035035920001c403400d9215103000a440818249007001007800c0f2030401c0d4856200301c10711032900a28001c1c0001100082100c000126005851752039192107034400760110384078139104003c4040c1c1c2d00b07a00c2a10345200400505610340100800e51240d00c0788500142c5180d402000f0540a0f122440040c0c00ca80420619120680c034140c11981400b14147c240415071048000802044402d102407545428003142c0702400f09403d01d942501440881801f640e11500903507070703142002ca2001c0018199031058401c1950402d0214048035040000c0091074007c11100b64070750030004035140440e81000c8001c202030b00c117a5070703035200c0d0001c0c20b00c000062613 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 759022805 1250 759021555 759021569
    0x2040501140319061116110402160b06011101050c04060806030f2a060f03041b0b0322080a1806030213090e030c15070315030c030204020f04030b01030f0b1e061009 72
    0x145a81b00100d40d202e00741c8544005460290b0420400000b40c1054030031900700d00031000340440d01403a50388601c075207003202610340ca0410044550402c4190820301c80d141c0151101c80d103850b541d6190240080400801900e903a1082d00300c1507500d09402c1000419101410381c8991840d600401c141014110000e00d0784455000040024a0007481404030b00542c40b50303100e081101011100f03003800c0454401700f40500e203141901000810803026490050442c1a000d101d00c50080302c02d1680c03200b4042c1c0241d4040f101246940066895a144502d100e8019104034901181800c3c0060308080300259548111000e0740e41c1c4001416203440c00b070048034215540b1004175200c06410400000001c00b0488003030700041d24281011005803100581c03901101e8200760203108850654003008000c2d0b0262159030300e0280b08100010021b1040310000380254002c00408407200103d082003102064000d00900000780c5030f001c4271400913038039a103058000405031380c405020081c6010581c0c0c48542e54002038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 759024055 1250 759022805 759022807
    0x1a01060806030c1e1018180507030b030d030e0102161208060d08040510050403210e1905090a2019090305062a040803181f0c02030313090504020405011403190611 71
    0x101e041c290340d014100707c842c2c01110421590b640c0c1d400032021141144546607041e0804c4120f80c51302e9200341c000201da4000c41000501d02102289106c02c20100050125400c0b0484a415800300f90440310155202005a4010904807080c1e0b0311314205100c1ca000341d9200d14900b50310280014810300640c0d0185a02a00840300310a2907101e80f000003040084950010710643c0c10344c8541d0524440e0000804000d02100c402142018208080310b9001880c0e8803540e90b44611121031180d5082ea20741034a442e0160007035860442d2425520394070a0003090303034140081c0040820014030001076143c0c1c440443c1c400c0c2d46446001c0c500c242c030386099a8004410303075031010401080d01d003c080000c02d03d000c1c90403a0609500c14120a00c4840070440400301c000035004215600b405004100c10008176100030192840e20b102080090400c42c030302d400203814240d5030410402107042910480d40504901030005a0301034a030310009684000c1088107141c002140600d0204011140e0001c0c882030070101812 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 759025305 1250 759024055 759024059
    0xf070f020603070210050606040f0e06030a0c230f090103020607051c03060f050a0e0f0702010e01230f0402150c0c090702061e01050112091a01060806030c1e1018 71
    0xa5445d0031085034400c40c2403510000c00e44500d4220205c070101c42e031090040d0320481c44d10b140f61010340f40050200d90180100803500300010b40e154121b90141001010081140740603801c3e071810094480780c80350180803000d043c030405549a9010034116581200c241356182907034541281401114a8446505802e44048035075444e0150011001e54180700c4210302da05607030304108000081d0a102e4000716102100126811002c00c4a180d948041c040c000440d48010408029085556000c440c038294040c1e80c0107481d500000802d07482d00080010800c0030941410b0700050f8080c100d12510901c2d09800007007801e502c0109000c10005441c0060102c1850303c0d02c3c1e000603442c1c0804940385410040f040990f103101c1d40c102480541a43d1041c3d540b00c01c600f0101040b140108a808000d4801101c5a82c098000d11401c0c1100b80c0079052980d16a005410504203161400f400040c010b840b44010b401ca110081c42c0751084082c00750703002c60f5054450058044113549884d013210780c8034003401b180d001c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 759026555 1250 759025305 759025307
    0x7020d0c090b030d02011e0b01051201030b06040b03030a0f0f0e060c0303040b0610091a1209012f07020906060c0d030203073e030405030106030c03021201050c0f070f02060307 77
    0xc0c54a500d080c0e068500034000380da000c0b0b00701c0e044d00e11f6101c1ca00408050904525040d5400710b41c01d03590604055142a002540c0681c0c0b04000340d00440309a000d1004002c51400c00780030316003070403600b90000d42c20110901c1e000f40c81c0304411415201000b51011007002014440c1c1c0c04502d04034005040c3c0c5651700001e51015403203600488060399098084808502130b418844031000d616401356680c4c0440034201000c1559440004c8000988030306c3c1030025004901211101701d001d505410000610048030b141841c8851919510010000d40d481d0407a00341c0140c518120b820b02e56040f0b070b0903a159a100d50000f24a4090440150918404c4200d02d83d001c6800d070340154080c103580e03210b11801030801400004100031218401c0c440e0070524105280c001268400080c2c0c10034060b054038202a21b500129085980320340c01a00c86642c440000c10a60800d5058005007210080c02032185160500c1103210f54030440c42c10611040000942406000182c054011800d0f80280400c5d540e040c8014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 759027805 1250 759026555 759026561
    0x50103120509031509011b080709230405040501020f0403080a140403020f0f040603021f0306090209030a0f061103150f0f0306060420030117070e13060207020d0c09 72
    0x811515400e020300c04149250080c01a07805615004000341103844100d07012035142c1d2030241800703991350748035800c120b20039612180b1417406030030543c1c601e400c91800304c80003004e600d465440343c502800300072402405500d6541d0100203208082c2c40104050b1a02c0c03070603500a1040c1d0714140804030002c50084104000040241040b4446640e0101e5001400341210542e100e82c1c0300003544030061941c8428981003042404100c1d14004200013045a03036070700403803004000c10825412054082c1038007095550903101b040b01411049034114148503650700481d503580074001000c2c00003000902d5001c20080070b604621034428002401945030304111028110445040c0c1032a0303c81c00344240b2500707641c10980b400c030341c1d1004010010006901d0f042c09010003080140b503d1980f049820b40f000098101d0000154001d002d410300e6440c0c042e55400c095801d19245800a0040781e112409010480b0490460b8a115030342028005079122114400a00c2003101107030000d1245072130312030015003001d070f583c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 759029055 1250 759027805 759027809
    0x14010915020607020d0e0603060d0615030302011b020106030f14030d0f0507120e120f070501060e0a06050901081f0204090504140f0102070201081302041d010b100509011d0103021605010501 83
    0x50204c80b07140b4403541e01680c1d840786c4081020f8006405100064182ca024007101046034042c5c000041e000c4003645207280c0d2039115810580160f9141c0018001c0710040b04039180c561106440200041400c45c2d451050102c0c2c610344c0901240352200103400c1d407020510440758048140c290811081c0c1032580040d0241104581900c085030030840c15406c0a0114052140c42da4100400341030141c03c4440b540310b05d9084400500c22000d02840600d0000782c00348220005016244942e002c980b605080b120180c2e01c3c607410142c09201d140300100080903002030950b80c21045a804070340890104d03d080e2000340a60f51050400504020034030080c89100125966203480c0201500e4103900344849050070b038402e1146c0240015001e41c0002c0c41e80300c0207500401070b80e100170408100448400600c030844e414107098640d8a0b5035400d0052110300d440e00304140c048a072814541d0038043c81500280c00850140703030803460030005140003000b0740c0c425411102c00700281e4801150103030181c01c03e140244024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 759030305 1250 759029055 759029057
    0x906080615210d2607110c060418050c0a09060305070e0a0e04021509030c0105091c080d06050d020904020d030e090108010c1409060a0f0905220507081014010915020607 74
    0x14003002c20420504c9107110404080885859119201d000301100c0c1c554420034880f00301d009000c000413140d038401c0000c0c001410b507520300d101507600c2d071034100f011103401901d00640c249042200e0314105400c280c11703508481060400003000e80e00d42c14280c40340800c0c00c500640c0321002d0305001c1000c3d0394940c15107004600a4892010790030380350441a0181c0702e4240c1d4036a01da800007000d0161588100d00404120304040d02108403c9590341608607403a606182c216024007001c242c406400c4240e04c50640241401c41da001c010842540105007a2540030304040d001c0c00c9681070741800e06008202150403060050000320f855a0b5681216008081007000c01000455200009051014420030795985200090510f071914403604425030700d41902c1c1d00f0100030720034a190002983e0707441050701c8008064610030460f2151803980380070215403000305800240003c803404c1c4602d0600d0b0000c0d010654124000012102c2200d0f801640c15950300d80c84414094001c1c03c90820060303012031450701641035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 759031555 1250 759030305 759030317
    0x10f0c06090b04030f0309200d120504080d0201050601080711010902030f030a09060c0506060904050f030d060e0604051315020403140102070507050102070b030403080c0415030e070906080615210d 86
    0x400c5c20071019102d0004000d004198400450248014502c5241c561400010040843d011b0159146a240c00c0440440307804500c021030104070b00301c400e02020a441001c3d00c004c1001d1316040001901c5400040c1c03009081019106008032403007025402022003a40040480301c07100040405240d4030342c460f6400d40c000401110380060b40c2800b5105012849522074090031080e580c083c10b105015100800c00d481510444200c00e0100d40b0600c000c01a0f40d6140801050150806440c1c0c000608082e2080740a940b40008200040144500014002d0341c000380106c1c01200104280c0302070b014a401c040c10454000d00d0300704100308154000c149035446801607420080c0d5441c01aa00c5e800f89120300c1090800400001d400640f0a0403181c1d44400d04414441c101a00c032008182624240c200b20380109544840601a8a600b000002c0040550701c10602180d414000da4a417290720180000c4400748201011741c0030f60750369402800444e05a80000404003100f51800c1e503661100d003440d0000320300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 759032805 1250 759031555 759031577
    0x132408010c0206040f02010c201005090d0f05031e09040506060720150c010c0815010207030204050c0f070b100b03040309030308130204020c1524010f0c06090b0403 72
    0x4060060180740740c078507005400e86a44e151525561500310b00c008a041245e40f480100000700751642c0d014602400000d107905103c000707020b204419101a650b4410320901b84605e4600341c0d6440d186061569112a104038000c0c124500146075004010703448000381e2800360000034001a07000517102080e800c075000d01460311181d0502911703119200d0058002401c0c07684907810440c10000c1d038040f401c1c001d03000c40c405e9801c0003c0007807250403000713a05072140d44940e0415450350b8881c0c1960f802400f03013038144808400542c0040e40e294071901c8000e000e26200d07000031703c02074116025544941604021180e4400541c50594030410088940b02d01c0781001000c0810000d41007000d0b070f0300c5250302d9200c2d4010306085403004c2e03400e1400100710300d5020101456010050700c50380050440d000c00708004001d4206401d08080c907560008020240c2442d00c0881c9a0500b0000080c07500900000e00b045a41d102d01d0f480200c41c42000b03024060007146c20410480c0800c40501c103141c0c4114002c0e941c500800c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 759034055 1250 759032805 759032819
    0xe030c06040b040501080c070b0103030e040c171303021f0608120304020d06393b0a0b18280303050a12060e0f0c030106080a05061324 59
    0x1c025801a2400d240c1d0910040c40254042c034000d0b6003009050700264105403141c1d650030000402604100d0000e20704000c01c02d454201401004180c0a103400c1c044c04017424041d02007110b58004040710b2640c0c007240c15103014907000748100f4466400c50b10340124140860384416019280911650409100b80c285000c16600c6e4041641d003d81e40c0100a041030062540b142d0300131b066205105c1030301e03203440400001c801894581580000004945c110342103110303e40050102c0a0040703418085540c245c101c00303403100c0030082d44031f01b0707200191980400500840118226940c10341025034030500004070b10000700c0c40704943c1500580c1c00c85118503000c407256240e0bc890700000c6655050300c0081c52043c0000ba000c3c4c0c014050280380c038941003a800c03c50b4048031041c0c800690016003880304c1682400414100c00f0051030303000d40007516880c6503514100004050310340003045804040d565401040da81d5542c4860581c034624054028410b800440981c0f142100c80031454801101e80110b0018940e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 759035305 1250 759034055 759034057
    0x5010b1306020607080403180902220801020f0304060504060e0604061e1119030b0a0f08070503010b1e0a051e130c0c03030908280f020601140d050f06070e030c06 71
    0x8504a55440352179482e42d54040d02c00010450b81c1045c03540d00300342c0c08285201e1900c0500700442401140203042d03004050030700d11101c07035504005850f1b40100714840c00002d0031811030350080d0380103000041958581c203010005203000b0b9100a15802181c003404180540e84d00070350110600200b41002000e10864110201c5802da41002c51440c0103021a0142864601c44c074404100c00f0b00f804034a5055440003d203e1280d150844403020803558010301800400f085403402070f080a800030000c00980b000050301da189517204440480c1d9011400e07902a4850b8a41a00206000380c15409040c1283d603a03c0382800c00c606000340070780803420b40744414030b070700c4d0180b24150302c03807600d510380011601d4504502030b10000c2c078103462541080212502610352240c246108204c5510006441003800c6002000e60019135a00021980303e40014005421f0103180c18002c140c045610803030101652825a0074a004a80070300014080c0300200440d180c2c001010483d0040100e0682d10840d000744200320307507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 759036555 1250 759035305 759035311
    0x60f010e011518060302070b0604141305030405031504060e060403090605132c10050a0902030601020f07090501081011090108131502180f0112020307050d05010b13060206 75
    0x1510032280100b0016248926031a40c881051410700702d90b001c45100d43c3c482c0d5000b0741c0b10310300007a80051108207000f404466036802c1501202c0900410f01084440031202102624805c02c88104910400400004100322401805c000d02035442011203150044150321040358141c1d2100c2c01e0001e4014404008140700f80f0459068885a06d11420100e00f20740c01d4001064010700c41d001300340301143c20234661001d252103200714029003404040b64188480e0440c0040c0403080b034145111002d00060f903e05541c0026190035a500680307980e14000101d1400840c0c0d0100e411602a00901085092140d041a0f0503298443c0032200790710b6022400000711080c001590400c03103010300020b03250307620481c003442d0810070f01e00001d580981c054603800b9102c3d407101c482a100550000711401101c600c4c150000405501300c03070202d6107020303690000c0d16000f04a681310701340d0390340000003070090390090003075500c20926a07100308100c1d0f850314140c010580c030034007850424800d012000101c03d4800100f480c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 759037805 1250 759036555 759036569
    0x121407020d030c020c0d050601090c05070f03030209010e120a021e010228140c090112080d0906061d0405063706090c0f03060506030108120c0102090406030b040302060f01 75
    0x194241c603580210010440f140400c000c5010b00b00b16600e060b6600100c8166071401000546555494014010100c4111780c040d030080c02024400701020504c41941c140c40c06805040250340d500c4404c004a80e0300c2c0040485560202c02c1c54107683c009140020100c84462095aa00080c0359950143c10501344102c41e0160040e44003c0da052112134285400e8004a022180740544100c4a0b64407486200d00101c410029648002031641d90340c98106009401890540200e604171296612a01020701c070704010856200c0d26281c4100030820a07030712003002041038484102c4440f020030109018000c080c0d4042d00c0a119260201c2d9040c002402e11080443d10310032260071485c3d40c0103c176000c8220035100500e689030f41d0780300000c1c0404940150f060032030701592124003e005604010381140c406801c5107000b0740b801c5c0014009860005444405102010700054980c1c2c40603a0182c0684140c5a12542003410728000104000f600c0e404d850041d4442e400b51382d15a40c80d0340e00042072141c2403082d20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 759039055 1250 759037805 759037813
    0x6200301050a14120105070503070f0906050304120903121110060506030105222c010e030f0c1c0c02132c010b03161d010812220612140702 61
    0x12000e8003d409501e103043c2c0142c500200d1518512040f401c66404032012030100b280001000f050b19030008400043c440c0178107111200506044006165010007000144071900188060200c42d01510541006640c4200250020202000003c000c80000003070301a0b47d103d000c08915000105021344003d0f500054081402d603031800c401c000e200e001a01c120f07042e201c1c2c4141c61241002c060700403407050746c0841051140c40d9001010244c0c00705211a440f4903940d240c1800014081ca01104442d201c807000150986c4075980c1d215a14181103107a405c400360301300380000c021035154102c04400c030454003c490a68604c9412896441a80d04003200080c0009044c64404442010386040e4000d5192420001600d65259000303e45000c203c1c1510225048510707604200f0b201c1d40c01d0300d000d80c0150200d2080003039490b04501a64800d004280e40280a4021a00e00c02c0340c6204080400c800b41000741140482e90350f608083d01c59100318180c00303a2107003416501401025007111890258805900030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 759040305 1250 759039055 759039059
    0x109020a0f115d07080d05040c03140c011718030c1e03070b010b130e0a0509010c170105120102070c12020f010302090f280b03090c0102070b03010e100b040306200301050a 75
    0x82c2d1050750101004072040c13a81804180c0b031b00400c520807140300d24802e4031540e036000d0642c105000d070341000504da01400d0703000009003260f50360f100380340050611640400407a9921803840601e49598031074000103041c4008103440c00468400075020300030b500c0700303030141d49107800780301c03281d522031264910141001d107031400100040480c8000030b01e4803a104905012000d5101c06040314151001d5030507034921350701e030b1050181030740c0300380f09100c014102800c0014a051040b0008403210718140f007003920070750081d40c05440f800000c3d0120b401241d40080964001c68480f00403c08085502806a0150820031a8205c1650085c4203c0e02880801041e030603c00b4004010000008440692440b034070303840904141610f100001d402000d0800503001523101c0c600f9607202840d0030b51082040d4115401203800708100085c45013101c2c19101600b0841009654050300c2115800c6a6486100d2800001400000f48010342c1d01c441c44801038401d034a07600001364814524140000c0c0140395000d0310042007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 759041555 1250 759040305 759040483
    0x20c0108151f020f01060915030201030506150a02060906070918021b19060e01060509011e15170a050709140a050402070b0108060109020a0f11 63
    0xc031142850024800c0011041c42800d004446030490b2403100960701038480d4552111081c051032002d080500420481080c420b200e41c004003c2c1d512000c2c0c14581d403007010a2964450f08518071101c0480c0d01c0d400d80c0e0350300c40392009544031004c50316106907018078000f19050601c28010311044038080690048e29016510740c0500070341c001c0b0001d50040c0c2e205000c7d540d8400060110031382c1c1d58040c40c28800d03076400c20b04114080e5500d0000400c0e15034904541400307965a103850f100d0556001d100e81d04944103c1c3d141d00c801041580d0402c400e1071481070408501c2642c004200440200707080340184040d2265040041941c4045d55404041180c44038140500060341380300e1034034000014003032080d9640c1c89000c01d00301c1e03101100c29980c108040c001481a500200400d034010404120114500700c0154401030036000500d2141c02001a551000591001e040200c010070f400c080241c01c98504030f4100d4100592003402c0c510101140c484031559801400c80c08030850305504004008250340c03030180b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 759042805 1250 759041555 759041581
    0x9050c010927050c16030e10050405090f070c0b1005011706010c0b13060509011d0a0308010509270a06150b0405040f0e0f0706021204120b04020102070b070819020c0108 74
    0x8416210038058030440b1a082c000c0784170b01501036101c884d071100c3c000c0d09011804d40c1d251665418418200010040391303c444000310b078041e10110340401583c481c00d500300c0c2c0346040c1e1303c00580300e802280c05008580c9545220700048400980720003041d00100740c2050192182200d80d54040742c2c1d46813800d000314120780070140c2d01403003c0250301d460039a16960790040b034509552031007090b0354501c0150458000300c550840b90100040081c1504605554020541c00c814000c05000356890404144614401700c0712000a19840c00042460112030740500e507601249a801d171121820990030065802c041c2d1032103025500c150710914030b09401e120034030001e01418018800343e1130f41c44003d00c80307580003405100c8034040508050800280740280c000d03d012406000140c450b00200010489210881c0480706550b511045100a6568600050381071546590106498070030000328a02000020401002402400100c2e1031104e401240120f9407036410f560158040383d541d0303000c2220407800c09 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 759044055 1250 759042805 759042811
    0x1081b0904051f080a0203070e091f020702060f13051e0111280311031810020a06060605040315061202010810050a120b0601022b02010f09050c01092705 67
    0x343e50704804100318000075548140d80e03030041c00366400101d22171003186414030a5a004290f0405124924201680802d4072400c0f5101068014039606065901440c110740542d40c40c2900185081d883e500b42100c400610352001ca4402003840081101082c50b24094109000c081e01c0d004c80c140948101c0303001550407041c58521000740e842590f0030040b120304032080d0f0f0310030362030211150400c51082e0b1034080c1c9402003001850303240390401d01c0001c04036138179aa0030a4003100700322602009181400c005a0506400c4400501000d080040200300260460000c104803841544c41945c1c2180400c4407204844480c02001030060080b042d490244d84210740d05170704403003e01e9481c00342564410009001c404250300030850b110a401c880e0081c0801148003540c03108080c006400f01017a61881c015212000d0300d550f0040003006204650f44070300c04d6100c0780c400c51400c0c50412000700141065980ca0300c1c01146140040d00c000408101c034064502c280250b40d107945a55100311222203506c4029200003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 759045305 1250 759044055 759044071
    0xf09061d01110613021306030203060c070f0b100609050402120423150708010503060f0c0a030605030109061a0a121205070506040c0602060603150c0a0905061801081b090405 76
    0x8a100c01442c4101403104500844209a07044030003581e0f4810702400d80316400159444178030302101007015071408141681d10a1300b00c80c01540d640b4852504850303856000c0b002500520604040000d86818102c190080c0d44541d119180300b95512420001a4494580c01548114002c008980060380062007442c0c41280c1c00450a04c0101c2040c615107081c02a1a9591120822106103c545c6400084e8140076001c03d401a1055142c80c0c250030140181c050010300030142d001130b400c5003c1d8800d0340240d010b003100400a210f020440d00784800500aa28030039443d1000c0a0030070b80c035620b0310515600c122030400003c804901403a4a40d41d085000e561000c405001042000d00006002440824403440c840c004020b00e250400710001c0c0303485c900030300440c02a400440c0d4007180c0356000640e1540000d11170032850303442401d29012648a0091f034402070300050089141d6064080d140030701c1c0e00c030590a81c0c81204640c2d9580c66148400c108404003003909900f080020032a06164020039480409 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 759046555 1250 759045305 759045317
    0x2010618091a28140a05040201020c0d0c1e080d111e031603030f0f05090c09101508070305060901050f190506030a06090b0603090304060c110d080a0f09061d01 70
    0x22904264600200b103d441d60649030b50b00581340c0c05071100e44400750071039883c500811a600d8150b0010750354115001c001c900c210780380310401c17042107092005680680891150030076080c0d290403800d020b018240c02110380390300030800e85c00c0b100c901c611030700034024050740000c2450610b0300c00d00c05840c0c00c4214003003265000802c20520540e5201c061002968401d90300080c8448610b00400100d817107032129020691300744814080300902c00100e00d8258441110301154580321405402c1510300c160740086400c03803071400100e51564004003038903c02c0d10b198030280403d0303840307808200c6a4403003402400c2d401400960b48030300324204207140c48102e4005482c0f00450380c4d111000203d03942c004580040442e500d5180c103120301c040d180a030601d1400141c51140c250306110390896224003450195000b080700d40311003002403041e001c08020501c0300107020440f4030a040e041141d850391100c007072100410080303080b04c1c0c00c044c40340c0d189a040319026905e20700300c000c690742441d2120740340040c06130412103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 759047805 1250 759046555 759046591
    0xf1202070b040b0405010f020a0206040b090f03190c12030915021005090102220b0414130c030c091502060403030506060c0106080d230f0d0207080a02010618091a 71
    0x1c81d0300000c201034018032440685662a040005008125503007070030b01103401c045001401616401c040d1400d0320401c0f400d2a07100e07003040011660040e40500c0c420384c18410716140d2500c031020b120f60f03d4900d9015952241034980c50320101d11560641c00d600400150401c4004c201c441005410310020800034415654088182c0040e8000e85038195580c031120b03540010313a40012010511070104082003a1a5200c601e07184c1620700c40140964401c01e1044480c1140040a90b510300310766190420395200c040103a080c1182004000381464480c100121300c0d440703400f203002551400d9001810969500802131aa25070b0760032009024050010754000d0400d03c80d800d5000300c2802101c01500c001001408030345542c0320300602407000012090b440c03c4000b0001c0c2e0221728098101c0d8a601c4180c0045555a290320000704000d00c110700d006400031601190855416506421060440e00745403651110300b240c0200c04011500030303040c01403c040c20180040c101c0104174150302e6010701002c00c401c036075132 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 759049055 1250 759047805 759047819
    0x71e030e09180f0c010228080702030a0503120604060501050403020d110f131b0305040f0303050402030a14010504050714300102070804080d020c0907050d06050a15030e03070f120207 80
    0x2062500d00c00075900a810002602d503410001f086c1441d0070040b001c84106840700d4140000180703004003400d202e0340012001c0540d1020440d000101d6030040c101d0355030309aa45820320954030140e0b4002c0c81581040e170005999131040094034162a00180800c40c2500d032552824145440903241a8004804c2d02a054003592142c2c0300603000081100003041520745030085111114940a042c81418a44004d100106e10306e4052180c0180e03260074002a41e4a407030001038a4440ca0690003040b0350005540100b01c24019000540120301ca4011500e0050721074101003405480380c80030700e801c036129005000242c9142001105d904030980c07400741501000d81c0e038040c05c0e81d20aa005982d10180010208010300c0c040101030800388051000e07081200c1c51000003104007002906c00c004011011a90b441c40c0d2b2556030003d0700031b15005014460320350740c607050200700344440f03107070040441c0c5000010000744102004446400c1e6000141320f5025003a9035070b000c50405480460030451017007000202c1c45d2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 759050305 1250 759049055 759049063
    0x7030f06031401141803070308190513050c0103110d020a090e09011b0c02090a0e01180308010f060e0d082206020c10031e1d01050c071e030e0918 64
    0x60740b203031001180400502c00d5044807002e0207400812003070340001c045490f4000120694130010340c1803525a03800d80702d0385801c4010050303c202c1c011b8914501414417640089036490f00b5146885401520012460034005500300d43c441100844501010848152002d0369580185402180c1d4180101403c0e1103030001102c0c44001c03a441d101d00ea56504202000c000b012080ba08a0881490b04002440c5240c0c0804c07501100648900762061311495020080942904401036540c8407800042c000c01050600501450082c0315280324403060a00108600784590ec0b140b84140001e04100d404007019541c0503955802178044550100b40310b041c05481040c400c840c1001400b295004060303242e1104c080000d61162601100181440c210110350380051215034403d685031801800240d4050843d0400d020005c13036a42845035501c8c11082103100c81503203000e840c85c03500a00c014040200401c0139440240810310000d4046440d40c0c81d83d80c00b502d04090007d502c1020f101d101c1c0c2d100041040150704e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 759051555 1250 759050305 759050333
    0x16170d091a0705190627020d0c030203100501060e030f151b07080405040c11100e0f030a1206051005071203060b04090203150105130e0c07050f030418060e07030f0603 73
    0x25841d52060300024460a4018104005070301c0280201c0005081030040f490302406000034008c150007020401403000c103500f09001142c020702950307510f8481f10680e100401090041d840803801c0c00202e180075090018603072040d011400d0090084114641036032041c0300c402065502e0180290f003001040d110001c0c0500001840303543e0440e216800c2604200944403004500401c00500c0e42e045100307010700140180510302d204400052101e0101115424001040c60f06642e9100002e24030080d41d0340100c81940c00180f01408004080d100c0c0302304a10b24030b9000411001807418400007000c07500d20081102c0e1480a820005107403a900e09010f405600641c1c0884c6c0d11aa0110410101400d074821110010702c0034a0694500f520007001078a00798400d006139010306032104005032201070307160201c814054004d02141c0d004188000503554aa00a015041d5852440a0020610b00f401d00800013900c02283c02030f802d03503072034040480061211180c0040000e40700d050010120b110540c007070300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 759052805 1250 759051555 759051583
    0x10c0f06061a21100b030a060308030c0c0105060603060904081602181f0e0711030f0c060403020f030f19051207030606180302090406180516170d091a0705 68
    0x144640a42c501440d0802c0034014070f0500141c0e00c01000040310300107480100352500c4003040751302c0344c450180b000d00404050b0401803001c800041403008158845020f001c6400d00100240150f5640b42c1c03c2c0034203030006541154020046902007000606290040d00348042d0104054a403040c160700020b084071011188109401089000d21016031400d458002c00500070030a0a00c00d18581511581a618010305140030054920b0403105146030510403a44410689100ae43c0c5a06031811f1031a2684015a022009803142242c800c1e00e0780c502009840b162640244591300b848403603030120800d0002000c941e41007007000c0201540400e0310f44034172070080341d003680d002039101d00300071020f406040440c09140b200f0490b06800c0006946450b8034683c03140c3e008001060700010304584107803546c074103000180180110502c031807d03880c08941460490760126080c140c040700b0950801d40715082d540a00000422207a03080c07240c020340080c82d80d0507403502c070070861030142d20b9150750f410800301c040845 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 759054055 1250 759052805 759052807
    0x80309010f1e05031503010c0c0305090d0602120603010e0d02030a080c040e0f150117010302151c0e0d0801060206070804140d1101060b03130b060a150f020f0c010c0f06061a 76
    0x2050003540059851405e02050f002001142200040038045500c1d04400608015000407202682c0e03c0c1d000580b4400390b0f011005540340c068810392204910000c0f18064000c1d071070002d86200003000010b000c0d03a0600c080d0040d501d48004a04101c420304001804c40100309002c11000070003e001c0040c0381d00c00c1054034554125402c1080607103100d040034207035083c100f00d680d10344c8402103840c030340c0f6850440c2d504846405001181c0c07045000c0038040c3c03040100c11072051305001c1f4020b5200c1c0d00f1407002c0440b070f24186c5050240d502c6042d540c1c0e00080c080e1400580c0a100040c042e136000340740080e0081c2c01200042c56400c0800340007032410344011044400624000203c1154250901034000a010742050450452500084140c109455200e000d005101c890300801d59507200c5403c964083d01c546c007060110400f08090103403841c0d807400b10040c0180305440b14040f401001013210940d01c401652240c03030045490b180c20003602250748003138411580d110400180340c4807124143c241116000700c0a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 759055305 1250 759054055 759054061
    0x150f071209120f14160b0c0a020a032d080a0806040f060f1a0415120605030307030f0e0316060c060231080615010f0216170d09080309010f1e0503 64
    0x4d0424400a0212040c60307101030701002002c00315446260a84140c122a55110a400daa0451030300207401c9000c0c0d00300100c02070100c00d001b402e031f806680020117040307840440c244c0d00c3c0302c00c204810350312000780403c1ea061245c00112440750b221160801c00081000c201285040c440c0700803100143d0101c10f10041a400400040b500c003444803404100400c0310038102031a24040000d03c1d010500480c00b00495403010b03c4401500b680050040d040c0942129191841403038050556a0301464200c00708801e82002c413118034000903240b142401c10045030342c005117050340550307100041410403110315400740417001e2115082d60220300a038221041480481c40c0c8800200c07804503058100c44480d800c0750003000303000f410104424030003c60a2800625110031004102c0c1049e48040c01c4040c20883c1c02070000d5003444200d40c0422a01c01002a550804c1e2040310a990250b0703d841014801d820911110301c103980158525421880f2605024418011030240002c8180541d003424003c21004418 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 759056555 1250 759055305 759055313
    0xf240307030b01031e0510030b040302013e0d0e010216061b0806010507020a030b0a06170a2004060317270f10051b0c150f071209120f 59
    0x282c90070003000b8281040741012207035403240210040004099020381350000b280a420012004c040210341200380007400e03040c2468024007802d1005403065108100e169001ca400449044803460603404640e0080c641461198240380c680007081c0040c01559035040d26aa54403003030005203e034801a140200c51f8441915268007103800b8080140c4a25003228413802c03c850b0042200c0e034003e1001d003041c544030742051000401b4628580c0000305040e08407410312070324a990750001c3d02070b01d0300c1c03a000c132a0704601291704039a82c801d0850050403006495040107a04107001c61040d05465026201040898032500e0b6100c000400c4070441c0380b03000001841100ca0200145c0350300b42204489541220610b84400061641d1111200e9920850341011a4201580942c0c2107e1014100b8039103c480b0f8910031090507120f0002e8a403150042d040b100c80c1940745184842182d021069012040d4103058031512407011000c03481a810302480220400450f048103902c100b5064070344204500c002201440ca8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 759057805 1250 759056555 759056561
    0x18220302010f110304050d0302250b071e1b0602090d080307030e12040b130816032603011701090f0b0a1a1c050109080a080708070c0c03020f24030703 66
    0x14240c140c1043c24410b0000066000c03442c0520701c43c580c500035803541d0a1036012050003a010550b0b503444096107010200b00130600c001c5034440c0c01683c6445415404800d80009000340f50300b28a000a00008200814000c0400e480b2590074025040182003600c4a000710b14884400001950301c50400b00c06c0000361503050191040860300000070341402c8000f00d16204042c0a107015142c03a0440102d03102642280c8000d05200811000c41101c5032541c04100b40c20928019000c2a1041c004240d020300500301700391090101d0a80300c1c01003c0c40c60386010b035402801109902d40d83c1c0309540368540e440c04180c440401c0304400d07000307062440c018204448098100c41c92802d104170766047d02c43c070501243c2e0f0ba0a20307015818208965100745480f0394034004e401450a46001859500d0200e22400ba040e408000b19200c0c1071291a205210784520106407000c1480000003419041c90385014001414000d03103041310f0300c101800c146e10700c5a480410b180d9140000307921500c8071001200304110658140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 759059055 1250 759057805 759057821
    0x4020303221e0f0f050306060d020616031d03010b1c140609070f06080610030506060c011b0905220c0e09070e040c0504030b040b1e040302010b09060f18220302010f 72
    0x81c007413114680c60800401d4071010024045403040341180c00314820740d100c00b411074000941c04009204c1b035400300d240292003000c06a03840b0310610009a25000c46040510514a030340400810179010f650840c980c0c00c0c0303085400d54046491502e0847c0800400c5020007519001c0c08400b8050301842d0300f45442118042c7c1c09078800f50801c00e0000a0081507183c4040300ca002c010180b80101e802d0f0b603a070f800300c1c7e45446840300d0a2603942c6001c201030310b00900e038640512941d207695100600d441d50b80042211484c40b040055020000203034800c042801ca55000d030044070a035041c841e02c00b0024100242020104580a201003040c0c1d485d000a41d28051041c06440a00b905105091a0940e01c910140707100c0144010402201070005c245040101c0d024640c40202640801c60701d4030b0f02d440c1c001e001c0c0111822040c002d111701004644180750207105244070500c041c1000c851007041840d180710344400580f0000c0c503035501c4581020440e4010350710307203004c5019800100d00383ca030303140c03402045070884 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 759060305 1250 759059055 759059069
    0x225050f0307300e131811090108030f0d05040c0f0806071808030a0c0510050c071205040308120a0603210e0303070206040b07060f0510081504020303221e0f 69
    0x240c003c0c4100550043c500c00a02d50041d2800a12094403941201c01003000e40c0c5a14900400050303d0004c105420214008800c030a07030781c03442d00343d03a242d01075652402168410b003000b600c28031852020344900c4e800507030301500980919031003642d103800152503950a600000d01c02c3d0001010451203540002e044101c9440c0d011811516920b008035464903800f552051100b007000c0c00c0070010a01004000c00401151284001c0041e81481e140340405035008a4084a0352052050140e400c58020000c0c0ca0441760404504c03450300026520703201a4100c0104014010b542d25440840410b00d00c040c003140c0c42840381010700d031505202c007002d80109800914641700c1e40c8200300050041e1990000d03039007101c044105035911003405180c0500030345540601035221030700d80341c20401c0d100340c007218200c00c5600c11401c0d2400072401281116803034030112006500360340200030001503c0c58010312002d50410f08010000009c0c0c44805a400359a0715603080460840450802e022071101c10051030020509 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 759061555 1250 759060305 759060383
    0x141e0325173709050f07030302070603020a0f110f0a0326190908040b0304080a080a0c170a02070f0b01050906010801180b0a08101506030225050f0307 66
    0x11000700308034481202e40000440b41001480458240c1c503580000d0b0005a000003030f2900340209008869035009248410380051051140c0020428041d02c00c41d0f0110301969901e50348640400d6040ea0301d50200001201d20f441841d65510340b2120030f01c14680a13034440c1c0d54688004503581c4614241c4400b04644444600b6581d051000003000181d492109034803042000c87c411a182c280264035003d240c3c808120b98000204100401413101c00500d501100794444c0800b03500c483c420030301151012111000031640c080c000300400300540c40a51b501840d5000302603c0d1201c140d8800b024000100d408542c818203100c0140102e00e040024a46d1201c001c0c60042c09561428118014840300071a0b41d01c006039403801401c4c001d4039507071030080c0a04940d10031144140402e41040000781030100e403500111002d0b5002041c1d60b0301c41d000f1a076442c100ca851a4540030007440c07000c0302002c24a51304480c54850241c580d408000f0500107072840314018451201c124020340d100001c000c0581600b0600020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 759062805 1250 759061555 759061591
    0x1b120901060e06062104061808070302010507090b0318030c0706120605010206090303070e03010902120604060f0507140903010b1c050106060c02010c03031a04050a0c141e032517 78
    0x76540c150200c1c0c1c94040170f00b44c0c07041c1d281c3c0c0c10310f2801071008040d030800840c3c4003c0ea1a090000c0f102c014200c045c41381d4000c00c0395030b80f200001c99a03040e16024580080d0340400219413800a032200a034108103175402568503090207401954a010b046900034400301e48801d190000303555030792103000010708003800505500d00d004501c0507141d100040c2607605100601074511040d440075072011051950213040d1441444182c2950343c3e564800712021201c05040080514000005015007400b5414544031158400c2c43c4006407002900f01321181c1c0c0e0959a1800031646a070b54903050b620300103403081c3c0c00101d6266241041420359015070420002d02115841c0140140da2080c0c110010f1501441d0000c0e4050803040a01541146080601d0b03001d4245010b000100c280d41e0700140581c4503e4a0341034034200511410b90b900e0040d452040c03c40c40110301c0041c070012000b402540d10800010321500502c40740000070074109070b40d000450025a5202c85d0400494200410f2a0440c0d0340d42c607030b00710643c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 759064055 1250 759062805 759062827
    0x629041805060c070f0203100b120111030c0a020f10090b010b070b010b07080c0a0302030d1419020f0403080406050a260c0d0f060909020f15031b120901060e0606 71
    0x14070701826040c038141000803c0010f210174040c1000032664000c0581d20030340303801d01d0503402414104170464414208600001e0941130140705d504034283c0398a01003415540c8050f00080580c0082e640e10066014050007000c21010604c5000715072007640c1c0000691032a61300303165561001c142c01c0030940d101c0030010140890340c10a00039044450546102b40d9458079454017040d03d0241301150007040c8580d080c0c1c04109074003c40078007a2480d5003d42080302c15038481a0000050084d00c0e0344140030449034000c002000c042d0001d1021810220710903280569a540303032021a8890317401000012804580300c1006540a02c00d50400191002e801070740c00401e031811454035602420342c940c00c5100127158000c1e000d040d04000719000b014001000340310b43d52030845024064080c07080b886680344070140c03400b600c0c08500c40041800e500304214115942c6682d9802c1c0074104c2041651036910078004002100d160b1800c00b44903034003090000c10624603180c04001a044044d01d0144030700070500c0481c40c05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 759065305 1250 759064055 759064063
    0xc0801180f09050a060e01050c0f090d03031b05040e0a05010b121005041406030d03091a06030a0204020f19090503210d05010602070e0a06060e010c0629041805 70
    0x480c5464030001100380800c94504010080390000500034040c950020040c4642e9034403038202000e01c42c000340860ba662008855451013141482410000284001003190a00b15448130900348030342070000f101a03000444900070020701c034600000400020781407004038000200e90341c204200310003d100c1d55062108540302401910b5400f20745501860025000340c866031014002050094000c2200003d0b001c110036203200c044500c24040e2254210040c14544a84290b02c282501f01004009009180c001c105141002500082d814803d110000c00580d41d248001d00303181605a01d01a501c0065005a100c80001c43c0c17480c1c01444800301c4104000d403000b0402c0c08880c0c00b100e98a482ca490740351469503076806070602c01c1d82810724084c008280c850300040c070074003510000410f0800c2540c1d43c1a010060b13591500a000c00a107a4080d590040d50092041d2880355202c4d1401048090340cc80c1d43c2e554001c02c1c40461403506421031a116000e0400d84030302040711508042100820b801d07502d0b41039a03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 759066555 1250 759065305 759065339
    0x14010f06120b090a06030b1b0304020d080702040c080403031401080304140102160f0f2705090a0f06050114030f030a05030601020a170301140f03070b0a11070305030d0c0801 76
    0x14844030041910701840541d020340da03041001003083d081400d04d24400002440d490208648480c42c50010036006901d4400f402c002a0081200c0c83c5140e07196402c0c4801b1140c0b42c14110f43d107080901c040401640c0d01d004d841584510b60343c0d141500c0c541402c0c010151220449012914600d407070040c8542103001c01203406807580016000c915800342c030700407450b000e242e501c4110300c148500c0e00031400c815008071840c11034000078550b420042c2c85552501d01540005044902740803600307090b140351002a00a07a40c03040080069840d80d40041e1250302190104e1041100c0c3c081d642c0005001c000c205090b0344190b81c40c141c3c000c1021070700151030180d50340304134404001440004800a5081d030f108010342c182c201d80c4040042c1507541030f42ca0100c119002801152810340c0c80540c1c040d41e50600d0407041d04c40510040040450900e0301d800034a65501c8000c9000030084000c4030300009440070040007000b58881d000443c1c0d101e949010000813112081200020044100300410205d101044030b405 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 759067805 1250 759066555 759066557
    0x608040510051812040321120f020d0e011e020f0423100e13090f1506080706020a02033c0a062c030405010c06020c01020f03091014010f06 61
    0x589072240d0300c10901030001c03841a20f041d84221400a0b481e04a080040c1084034030030442d940c4402c560084902940200e07643d1500028010680545410303401c0c1c000c0c50103201d440e40d005252018400101d401d9607172145042000769104c490f0f8054a61403460203020f180242242141802c441d072000c2c4409202d140f15101c0c0c0ea0140045102000e010b03500c40d52038405000340743c210040b03038414000d00a081c103007080300d21907040d2842c10306030b0030b14030b0040300314042c0c0c05800105424143c0d40c1c0d501d504030054424003003440e035407036010440010030041603028112503001885003003003030f104244c03804500c110401e01c0c0200c9040c000709100c1c0d4400142c0854901c00c68103090b910f401c6104c0034589001050b029140320705000490113084540810428031100d0444a0480f00701c60740345180e641e214034400d160004901d4542c0c640420000d501411003586801c002615000e6840e10780407142d0020b0700c031500550801c8002c120f030031042c0e115402c2a4a0130943d400015807400d59950081515449840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 759069055 1250 759067805 759067811
    0x130309210b0402040204080607080412020d0c080d1509020c190b04080708070206130e0a060303080a02070503120901050613110a03090503091801090c030b0904122303100608040510 79
    0x1c086540d285c044c2c03005003184000b2180c03a40380007000140300c82c805176400d82e01d101c2c4200103d144607102150003031519a02c3d88400010000e2075807040e1007648138423042d9200982d6542d9061a43c041414210020510a48056116005085141d05025844140e9440000303010a24030000302044141d03588107800021450b22803403c2c1c184500d0a20030071303e000b540200000740c8000000d03151400001650788012581ea905e17600c10140340102c40d0700b4000078001c140b082c0000b030341603089500200611031055054038104007000b101d031503510f08250f408000c0c40e5180c20801850b41008240781c400405001c0c4103000810040d0200c0900b03200d01101e810030503172144000f009020742041224585c49000c1d026401c03058034000c00e848404002c0c052014000c0c1400107c54109102c3c1c0154000f1010003490078025480304d545002c84a070202c0104418800c0302d1560010030015050366142c80c141600e0802d0b903070f01d8614a030340998170980d004103062012040074030001c100000341841c4295a02c842c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 759070305 1250 759069055 759069061
    0xc060c030f0715050a36081201080c010f1718030d0b0301050a0614100908060106050a030b010f170603030c0304060309060b1210091703130309210b 65
    0x54258419824200c0e90808000b49140c1080074072100e444500d1080c1d5010070079910341d041400242d507408640710508011a4806003140c02c0110041c202c2401c800c03244140aa50541d1441c5054004607a030a03607041c00c2000401142c082400700c001d91090900c2c062010062103400500f0442c07a24280001c509600b00c00940f56001c404064900b800c1003008132503c2d040d100306071002415203102c005009508040104d0542c04142c00f5900940b920304a41c0030f4540006410700c01d0000b50001c801080001c030610002c0e111800f030040c40e018022540d5495a1030b808601c1c041c0a03181c0d40c1d00894100034814084c258010740c08203c220400e4552070010780980c8441c0e00081c81e40c050110900c1071408001000504590943e21070058284603601c18415145c0000c10000404c0040a07801c103560018805da444000c040d0744914081807240262007a01d0700e20110304617680e0401c4034207001242c8403410302c0c014503420a041d0030082902e17080104a1102495241c5440241c00c4402842c9407214008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 759071555 1250 759070305 759070327
    0x61415090303130b18091311040b04050708041208040c230a090c1b0b07111912200705041503050d26090309091e01060906030e010e0c06 60
    0x1211240420750100f040b54907124070821069034014005a100d81c014003002c0502c504015800600c0340440100611089002d0b031642810300700301c00e0a99503c5680e6001a401c0e660703681c40381d43d00524003580c488509282510341030001001100454042c02254800c000c002a03941503520143d40a940c800c42056901d03c1001504049840504e640300c200c1076804a03108045078011003c068155444076a01042d0286510203c1c102070809064280050000744185020702d903015070b195000821604411001d07265000380260104049680c18030300656100300e282e011040b202a0700030044000c0007030480501013542c400c0d5600c60310380031300c0e100c40c81c00c41181102c00d1180015070700041520703a9003100c2c1c2001403904541211000d014440080a000ea110071b080016204000c03150042d0715040a00b020040192001803180700e2080c02c1080382004003c600c07002c03d008250315200c81c41c4007410301c41e0140684403000c1c4241801da00d080042105640c00050075480c41d142652000d03030f994140d0031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 759072805 1250 759071555 759071557
    0x110415020c03070e091221041a13021215011401120e011515050d021309090b060a0510090302100516050f06100303080619090f090501061415090303 65
    0x2850542c5400b0740100080c2d020943c0243e0f91040044005a4030303503000d6844040c1c081d0154006c0d50009228010b03060103560700b05170407590040c4c00791010301d00e045491841c43d81d0304d840841e208921050912002411400c20810341c0700b041d001000076096000b0740301c0c0002d8403807505201e60089564448502042a4001c41650242d140a0041840322244200035a070103028902e102c03400780e0008c0030001900200d900c0e403010748640f06035039640c900800c00101802035003107168a244070b044689400610b031001803040e104c08611458044886140010800240d048903611003030046601c0200100d81503484040181545e50444d400e0301c41c00803095007111540a0a810123552181d15a0b000050103070004010001c038a6100c1201c0d515607410900441d145210b12009001c109850082411072600c000b0b20000d030508010807080c05913403013140c0c10a940102030034100a958483c1048280f1030300b0f000d60300160003c42210302407021402d0114090900448090810507004038200a8560f400c4c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 759074055 1250 759072805 759072823
    0x19050d060303090f0801022703070506032d090a0807110910081c05040501030b0d06020a0e0f03031e07110303030709090b011e0c0503070b090a030f0311041502 70
    0x2001000403685a242c00340c0101054002c1c00c240040c603120000b9140e10500031580d111080b040349010400340d07410300d001e202d00d6803045a40d00d40a800b40215464031790f82d014510400e02c2900324401f10200c3c0d401d100e10350001c00c01e007292654944040119408000070004ea90641c003d10159a0741c00d1810400310030001c907660558000c001c8002d110b40c02840054001c160384082c820303105200c2e0241d090b910076074088000c240c04203c1c1171200308100d41c0298488013100d07034080c2c82180c0954407a40e841d0205c1c0e1100d41c0e10b2010903000302e8040f03110308298114405c903038810340c02103103455800703004641110340c1c841011241020000d601000c0000c119500302825201404a07a2a8240a00060f01e051014000d540c5050b24241c1c4055580d84208038044000008204a04c46241000c3d13046810505202c01501d042c481040300d040041c1d4030070f120a00c00c401880281910541a1500414409510f82d8081c109401c2c81002c0895440040440d000c40300d003c3e6464103918649903040e803c0071214 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 759075305 1250 759074055 759074077
    0x2070e06130f0501080d02100c020607050309010905010c090602191e02060d05040f0204180f0206030702070b0403110909070e060609040905030a02010f0b1512071b030903060609111905 81
    0x3c440006007140000540400e054060340039200303c0b08040c20360804884038800c180c40140c0c02040400d1600340224000d58000400c0000880e00320015100c2c903081d1030054500800043c0b2003402002455410b2064940c210040071400d05420780d45c0c0c07210030381540c50007000c1201c07000e40340000c804c543e55103084a4a4405401080c0b00702d00d440d040c08068160390a0f4264081c0d81031407000e03402410000c548002c065030000b0304c0281e80c2815000d10000d604010080015803081300d6000c141e8440001c054001184202d032040d087c4402d039418045031200c0a0501d80c010703445000b082c0b0401c88280b9250f035009009070b41d0291940c2c901c80029015040441000e080c0e400005180380100b5819048808804443c40c81405695454020301041900d05030840152503410710108030b1880cbd642c90000c0e0825400e1410b51640542c1c01c0d0134240e0003503003450803404500412810001c0003a03a004010090024042c200304038511185004564400c4c1c0440404107005224219030b224056801c1d60044132030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 759076555 1250 759075305 759075311
    0x2071d0901180b040201121b0c0c09091103100209060f0d02040f030809151c180803091509010207110105070615140405240d03050c0d080f0702070e06130f 68
    0xb85051035001090182d805a0000e0030280d40041500a140074045511640f8014075002103a00c02c000c40b629a116201291030794044000081d500c0c04070302805042038040d00c1114005220300b010107107401c0114002c419003a0043c0a4041c03903942e54015a103401d50301c03407480c0340e54422920207140244240d42180060012108010080c8000030300640403c117019a41c0410120034041d24a945000b0304066241e00054031400404002440d04a41e60100c203a0640c080c1c611020390300c1d14080c0e0000c0700d100645510950f141611070100e80c1005030004400002103190000a440b01c18518492014281c140000001d0010030010103900107088007040401c4050b1450300e408403511860f000106842c071840c10038021511042211081484400ba000b003032001a0101c942480090700b240c0c1403e409206050000510780c00045c4803000e4080c007607a544405600e4910b14990500780c000c1c00400442d48800c00c14450407050240c0c00c1c1c0c00071070403519015001104c0d0603020240081c502ea414160382 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 759077805 1250 759076555 759076601
    0xa0f050a0603060e2e09080a0513060f02060402060f400e0126010c03020421030206071206030609051b1206190f02270102071d0901 58
    0x1035560010055a202e22000e12040c0d00c442501552004003244140c01c2c40c07002e200c0442c1c07001e006004a0715004900c4000328140010341c4600145d5080811207401140000036031006d00d100354004440a800e81e820310581249400301300a41c0d9260043c002400365800048040042c10b0311403d8401c4041e420484464091460800160f8001407042048030703e01510317078454094000454860540d1803000310000c1d00ea19201c40d0703070f80000d07800f60310061100c07085442d0b0703642d14428003c3d59200d01d070302d44015a99a01c0e03c04e144881e0340ca42da149000c0f42c140c0b81c3d41040066808104190807a03620300d4600c0c0c000714600340240c004c0025034401030034203107008840400c201002c58064213020301201000201c54101085c0a83d02114925907052904040b001803a20f0301541c0c00c0d100c4071003420a0001e400054059500e040764071111043e0b2003040707182002c1d001c4003141c140107129000d080c07016180c0503140204009032400d41080da481d0300d00541c800035a50007400d5110020b01ca41d10105044040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 759079055 1250 759077805 759077821
    0x8091207080f010c0e0409021c0b1f05010203030610110a03090f05040e030d050a09170d061a1b0a0204111201060c08070201080612030f090909070303170a0f05 70
    0x5006481600c1c5503000b003032000d141410042c400c801440c541c503164407003d52444420030000742010081241d2041160500030121250100c00030801441081d82ca5580d0509001c003072075035254207401050b4019040001d000030390b404026280c0012083d18554100b00e40c4610665102c8030903101d1110b07030310552242c0018160301c40148411200080c20b20400103868009100541e030074030f0044503941d842040311803800710165000c02e9000180540002c0c800109694089000d160310404a50b104408524030740390746820300c9000014080c0e40d00c424020a001480840329000303d0000303081140c2070030000c00c3d1926003403200421090b4010420080c00ca8076200b45212a040f501d000c00c900d1108000104019004040e0b00850b180c00c081018107100c2c00b03034011282c0314002082990004184a00200103660070005800c1c618031990015440b0400703002840301300702d401003001b0860307802500200040303504101c2c0e029070101002d00503612076482c008403202400859100f4592a1318000800c2400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 759080305 1250 759079055 759079063
    0xb180901020720060403121403070e1806220608060c070c0b070203070b09011110020a030b0a030b0601081305070311090132030717010902090f0108100504080912 71
    0x249124140d00d4400d2164070a0007010243c0804045401c00c408000a002003a104ca11210700d82c03800303140011954445401002d100d410035120325020074041c1071004a0b0b0328050b0030549890040c03000b400c1d45c5103808400541c101c1c0344581c02140304016286032441401c4141c00c50382c05030a00008035403190421079114011640300b400309036860b08444802090040c801c10072101182d0b0024002c044070390a1245a4520390700680c0542c1c10302404c0007110b0003084041c491900e54607154140181c403450220005410b07910380c01d803554401c1c4d05d101002d20002d2002044180c00400030310700890745588062400481030107880010b012441003036400400c10030040c00c41190084151410281ea03607890700c2038190b201ca0207158540182900400081030308022144400180c00201110740d0346681c1c0c403408000c4100d5002403506a511400900e0550500000a9070000007012040d091076150007806600c1d500b1036002104129120b80100e01488414015a00d0084005029180e00c040c60240e07665a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 759081555 1250 759080305 759080317
    0x7050f0f060f031f0803030c0a032304030914060d020a090e04080403110919050403020322091a130207061515031a010207170703061b030b0f130b18090102 68
    0x4146080d08072400d40d203403010413045480b0b580065040d07442e000c640d818141c014a400d0410180d0b0303450004000481d0700880341101001c40d0750f0030074034202401e004064202a030080c1605180280344c40d03040d40c5074201110740d42c2ca041c84005071038070101d5808440c14604c0754032100c180001d41e404d00c003e00500390000c1c01202e04c13800d59010310920702400d108550310110b507043d002c0240c60302e07140e41e12640d030b8000070f903c80d10138410740c0c2c502016031650300c4101028803620000009000f000f4400b000b00344c0b06910803413040c0080b05812078281c20001e00c1c40351004120302c4c6180d40104186042014640240c00c600040d0a5050b90302c035200c0ca0740119810703464219200013402c01131710035a140650000024800410303405409c0f0b0a06014410390702e80b040b5240e480b0680b18904000000c12524858040c030310b20041b914400407c62000c00805030b422002d60207100b25984299a90169203448594039030005c18039011401003c980c0015030105540071098004804403020843d48080650007801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 759082805 1250 759081555 759081571
    0x1503011b090801060b04150c140709050f04020603011e0906061205100e0610210603020109080f0c010e030a020411031f03120e12011b11060907050f0f060f03 69
    0x150981d60382e180c0c0e090704c2d0148580c80280c20100800d00204101c2c402d0302d0088812410282c00044496484400105110b8039420081d000088140508440741c0181c940040b09030642c1c9078603003410303000100d8510041c07080d12107107801071800800c419802c0d50080e0040403104401c01c4540e5a81c10060f00e4024101b0368200401e1803c40003540301008014805d0680d412108102e015036204803c1c40200141c40345080d061010140c05d0320400c24450f840d130340c0380c2150700304003051640c60351002410b016426004041242c000f0946841c50227800030715118031103401d10f0425483ca1015020908082543d14080d4101d03090403604070300c40d088400250300840e0301b561071441540400c001c01903045103902001303107040c5c0e0710810031081e5841070100b00f29210006204c107004000b84c2d00c20900719030f2400c0c1b1545d490203a88070100f046a070002d40400e102e40300b920251a0b1441c02e00f00c401d440720f0080c00b62510035001c01450f0881d54403501f102c83c41740d05000c2c01003980c580c036101000b031642e001151441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 759084055 1250 759082805 759082817
    0x1081e150a05010f081c14090604080c0a1a0d0507111e060703020702030c091005030a1103061015080403050f180a05060702030d05071e24150e1503011b 67
    0x10300c488002076074941030800e03502800807062084000b1114800c06280c5540310350b109202044d1259100c0c9c000b400103200c003100030041d010303189091040307000140c0d02050400a410b1500001440c0d04400c99250b109601800106951502015a08941ca000f191011441001103031a0032180321121a141400308004407952652000011800c2e8441e02400079055001309540c1800c504120746411380110b08042c04010343c985410100e0b01d0686000d00985010300031310504103080c2400e21501e50403901561409034040d04203245505c14004c007001400800c40ca140014050601ca141613071000c1100c03081c5c2c2d640e1030b400c040040394a0105011858130650100c4400500c501e070400480d103800c2d41c050040c1682e07a020900a4540380c000440036650680740915588040c00501120031280d4410002d008400c40b500c0070b4041500803240000e034205190102a2840c20700d0441c000c1e0407a5544254100c02e90344240c5000c214010001c4195059030801e4440241280c1015441c17a095003159154 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 759085305 1250 759084055 759084059
    0x307140a080601231206130c0518010c080909040614010807030309090905061b040909080315030d1b05011808030117070f0603021803060a05010906080601081e150a05010f 75
    0x85203a12200b014100540000304015400010211201c86c3e20180080090720210180490042500e09414041001a40004011001c09030003001040e503038000b0310704482422519600c40b10284900c15407a481500c6c3c9100240810069401c480001d500b241d62000b4030b56507484040b40d4a02040c002180480c1c9000d10210f0341c1d9110f80300e441e0846800c8001420240c44006d074902e94103000c0c80210a03500010000414040024011100b03110300c1200d0281c2d032890100483c92240030721800113446904151150350040d03610144048003c14025902282c2041c0c0d440c00a00512010929101c40b80c1e14a50440c28003c404010f541240c4100b00e030814800c0d40009880e885440c4ea004074244440c6803081800242d02c25805085200c080041c0d009120b4401000240340c00c04c1100c0415060351140014000c0e02c000c0d01400008020802c010aa294105045c49480702d8010a1290f010b02518800005685013000400c1450009440411482c2884103905014113024068140d0801c040b144c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 759086555 1250 759085305 759085337
    0x90a020a1e0b091e010c06021c05010501030905100b0a0f030c080114100b1303140a050c0111120d091406041a07020c240a030f0b0f090c0307140a080601 67
    0x889400c4a401400d2071080070040410034906044d070500c09040060f0144144005085c81c401002c1008040007903441b1001054920b4068881c16080781d810941400034400c005035000806c80781401040c0070100d5500051008948000895031140030326401d541000014041000c54040070307501c010000b0710040d0f141014010511100743c400310143d0303610140400403075541da0701401031030061704400412682e0f25190441d2a818183e110103031078001080010402c482000a292104020f08292303400592002005844040d40c1450300403d060006403d505890242c1c0241c40d400d03841700030b0507451660311040c19a06d00d000c032012520000007079407441a50403440ba03090321800c0300ba0700400346c05801c4810320800030440b60b003440080400490001c8900c1c0644080e00801103580e60014440c0e04803000e40068070502002a4040e4800c80c4c901c400503107030004919032143c07617200b4260742c9071032782c0c00100c0b00043d02c100302c508903c0c070114803500040d5002c41803500030502644d68001440c02019 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 759087805 1250 759086555 759086557
    0xc050d05070c0b0a0504020d020603041b06020f0c060d1d030d0b03010203010b070f212313170708030a0903150507020309040902041401030305071a150405090a020a1e0b 74
    0x54050034080140700000c281551540085d507000e4406050103200262550120b00c96800c07c0d01d04491210644941442c016034080d02c680007046140f00074841080c0002009490b50a2041250300070400010741c8116181240c010208580c541c2e40308a804100303910203151290048203401603c02d0401544884a1505009980c181d40c04001d043d807625a46940314460b5407040c2400712140f50407501c4202101110300504410030146866121030700451090004000012420403c40d803441882180c00011900c400704058540459145440c40c0b41c160115142c411154085041303071000050704282c481d44040b080e011a0b02c100710810710f4a0f03a03000000d040c0c4800b150300a0069000303205009051038540c20100c503050000e0700004401c241001d0401c450b8000345c0080d00032440010713448080246030300c0c2141e03030110a0158482c0d80d060070703e14031012442e0540c01b103100b40c1c2ca42c0e0128580040500200400c694000c000000040d42c40c4801d01120b162941e06250401110a00141c0700180340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 759089055 1250 759087805 759087827
    0x1d03030c0606270c0a121122030f11010207090606120b03060f04200405040b090705090108070e04080c19020a080c090a020c012306240a0e0609040c050d0507 69
    0x9965040f0035a200c0b00114641e800000404007000010440e60704e01d081a4407031481d044146080307441da600602070400d08640c0c441021070460402030601000410300c051843c0303407026840b50310349504881010040f40b0300a03030ae8006401d101d00d001c0b00000c0c0e0766042110740c05540c550360000e00c42030a40800f0552189000c1700c61044502d0340100007400121180c0c0c1400900d501d141c8080b141d4210100400d089030411101207460f02851014007000140800010009002c21546a01d079507050600b1152074148a1062150f10390180b00414104403404062314000c03811035080b1110381c86c0008200309640f10100060340146084d640118200031301041c0300d90650b6002d080d900c202d03202c01c040c01c0c0085d805a01c0d032904a5690342c00c0e50401d108404241016070b103003018003a005090800401c5502c0c1d210500c02900840c5c050001c40d2400c2c1804140da541c910181800040e20b10540045202403203181074140c0c0c0246410005088039030403130043c00d80800e41c44002c004958a800080d10710101075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 759090305 1250 759089055 759089119
    0x1c020c010f090806130303110a030605090a06060507151b080609010e011202060f0d06031505070807080c0306030703021002010606180609031b03060203010b030403230a1d03030c0606 80
    0x184c0010100101011002c0c101e80c0319140c00180705409001513100798100000300c0d80000c0c0c44003001c020038607003480d00a40280c0381140410141d8900403000e841ca2149a0f8000d10080d40c5c0585c0e00c3c0103403202d5110940c502d170b10001c032001c41500740000809000007151040d100380c5000e400441d00880d41042c41d8180c8020028001020385140c003044042d82050144074a81d00040240c01070070842c0d80908002503119454500e800147c181c1c0100588800030140b4040000b0030081240d015404150743d508141c169440c260f41c1d40700c0380c020a080080542020390408061840c9400050b8150b005c1801c4035160b65400040416a2040540800c040d00c903140020320700490a101280ca0380d2042d030f40c0b210004010404043d500d0780d0382e105030381007680800c1c00113501108210074140c003c100f400c50005050035854210300790f1445911680603000c0101c040000764203a41004181d240c0c0007080480d0001d0440761140046440c190361100200c5101c3d000707020a140b0400c20260b4800c1082ca00010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 759091555 1250 759090305 759090313
    0xd090b040b07020c0907051c060803131203080105010e120a0b09071e03020103022d04170105060a031121010f0c0c03020a0b0c04210201081b0405121c020c010f0908 72
    0x40c2c00320841d00c6412880000c4018040c083c0402500c0230740c1e00c01d070390080c681c1384051038940341d100744284001c518542c0200b0511003030f03411303e000083d441050a0305441090921412070261000451219131054169003070721302c81c645c161030a02c190a48068860083d140880d0041a19a21480c920300a9615418903c40301a48107000545c06a0040e20b81c81245000d03401231240c81024141d141d10360841c100941c544001003d000b541c1c24010442059400c1200074000b605001c40801c1c541e021506c40a012002140304241166030b504141100e4130301e03003446103050a1b202c15101d5000307104921001c0300c3e4030b00d04400d400e103840c000d0100101264054000e090500c81c03035290303000c84000082c404014480704000c007141c240d0448260b510201c040307403c2244603183c188000f50070402d015001c1d401c0100d9560a1080e5000301804440a98500755180e0340c0244071045032520780100d0898042c80748d4403003407034011300913030002d01d002c641a400d0343c4000c0107052480c01915061002d000712616a00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 759092805 1250 759091555 759091561
    0x503030909040203010e07180f0c02060720010c03020c1e0a0f020a05100210060801021e07021c151b09051c0605270304050d170d090b040b07020c09 65
    0x3034001d44060b0b215002400219008560100036820080d1b10b40002d80c1410141a01008001c0c1900c078001d01c0b2203030324508211000700340c1000ba5603284000c01035010405503102c00340380000303400f0128000445500090082d0f4168500103400307500844654404c40c480d45d8407000341d0b010030885400e0030a032030001074141d100341921895107121000c0c0c81a40c0102c062400010541c4600c2004070b45400181e016241a5050030700380d0b01a00c140b44d119072183c0e8018060051050003102030145107440780c1c080507a0343d104a1010902e00f01c0e503012000d018503d100480f0050100c0d040b40c0c20345003021076038100704801d2050715000002c80d90074441e400140086000b44080d0070310703034101c80d49251040c0c01c81c07850550507a2100d007540c0c07084584c031a1242c1c0b098004514101d29040a5050030401d402071801d00d424074001c14001d10000101503d0141e0b4003074896160354120048444210800005200e071940c141802c04050310300303403000c0303600144080000d1025440441c0c103090456006001d10a503407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 759094055 1250 759092805 759092809
    0x13021c0c0302090a020408030703031b0e3105280c080a020901031d07080705150a050306190807230a0b1c0905010c08070c03050301090c0903050d020a1b05030309 71
    0x41002089013401d16030030000030034142c0081014150151003a0f0740410780402000720407a1030440000c01000340542902c030003985d50380f0040710034030807808018442003d440003403040e200f80a510145103412403a040a00411741001e82c01d041c6c81451000102c4021500c607c021011a41c0350b030f08080c0019800740200d4003c1220780c000301200e201c14900420003e083c4488003030360784a400448034030303940059000c01c0105014020fa00050200b162800c0402c01044000900e5102c0c5026101c100b040000c000340442d568042c2400d000e0400300c4041d0310813500c0b4202d45a40c1c004601421004144510380f500703c41844810456401d40051700d018145e52410f81480a590095000b04000144c1d100e90000300b40340901c52f0020883c010000800d81c441180c0c0040c042480141c002c2041203803007800c10300402d03007000c205e0341150f021a000241d04013008008031042416904000c019008210884101540c0080e4210047d405a404c10420380d14018610792000170600c11950036400c144800700c114 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 759095305 1250 759094055 759094069
    0xe010b0706091106120f090703030210022802011e060b1603201c1106040b25030e0601080f070902031e0907081911060703140313021c0c0302 62
    0x103d2060401a110045007000a80703160007441910320744072445402c12601524807064550084000030183c00c4060858400a4640c08100041c09030130740c00203605640003003440d0100d1030259420100b03140030300d0a90030090107003403443c40040c4603140a840c800140303d09441036908640b22060042e2401038480e0803507201d2401c00342d003a0f0034082054509000c07042c48907001c0384000c414001034491804080c5501107010b80f00031110003001038002c0c81d85c141e0b06000840e107401ca0340002e100700d030315074030700304580324009607102074210814568030b0741b00b1001c2d010340260101d032060500351001681c880003602d50713400100c10b10000d81e601c12081000070386401d900640e00003011a400703207860016900c082c0e50a61382590340700c60a520405c810084003005010030940008241410301c0701740030a80703031100d28410140c1024071400340011075004240c05030244004144c0c4400840b916443c1c0340c40e4400b02046815403c0e0f00410005e417407020310480c2e80001058113544141d05a030143c0c1180c0074031600d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 759096555 1250 759095305 759095321
    0x207050d02120f061815060117041707151d030d11130605030906010909051507110703030f1b0b1b0d050123060c0c040216020a0e0405070e010b0706 65
    0x510300a03402c0c5802442e9051114074031078000640c1411004c014000c0c0d56207003980e181c6c4501e800d00207690030b0107020b0b80d10003605880a026400300942544503402c4c040c02d0041c04240ba0103900c2d200084c03030020402030040310f181d41d44010700d0030801c00003002402c0c074508a03010000412a0420404102156201d500215192003880740940c02d0160498481c00409426000540418404010020614400c201190140100100a02640e503240c0c0da100d41d1110040001524240702034009210144140c01881042e00400e0403901c0c920303501d06015014014489260000071181683c03180700004400c2015141c4d0352000900841c0d40e0b460344000c6845400e8402c00020075010499400001610b024841c00390696071001458000320f0000301d081c0700c0c268034880303011741018009910440b001046410010000303480151f9241200c4480044982c1c40341d800a41c0516544c03000b00e801070302e50040611462042048498090300c50f00314400701c0d2024442c2070814001040500c00060042d00071a403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 759097805 1250 759096555 759096589
    0xe0a1a130c0c0b01030b0a050907080d0302030406020904050a0911060c0a11010507020a030b011e050d0609060b030307050c04110c0703030e01260402011d06040b0919060503160207050d02 82
    0x4402e0003039559644000c0800c4e032043c0c580b01c40202c1480b41090b210311800b0382010010008041c0d0602c2d2041a5840b040d05c00189802d02d0b82c0440010148025501101c44074070b03006104000c0e40c5003886440b402003008003c1a6a99120050102002c0c10031000b02e440204034500100b011018607500c1101024007403024604201c410707c84800140c40d05095170001d148a00c285003507540c1810a0100615107404c04074403001103440b8108410b448401403041403030341008001c60200110708086c0058990781030354580600c0700061500c284500807405480031101250f0501044d0f12120406065000d28012560241c000910400009004403503521b8070403130604003000ba05004041660f280c00101d9841c0180d0406a0b01300f00031503078060701c03207032070303241ca200c0c82e8481e0001460100303840340901e0141c0d06000300c000900d00c10070340e65100000c407a003409011081a040e10f039000140303540c00642e82c2e0041c42050004240c06a400030030f44c0024cd8034040d1460340d80d200c0c1502080030078802c00000c49 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 759099055 1250 759097805 759097817
    0x50306150613080303240105030423015105011d0628030e060a0b03030702040c03020909150d03050307120509071503020c030a140c070e0a1a130c 64
    0x143c0c0b15028070165204949607402020911121a0f07508413020f4540441810488104100b00001d0130240c080c1e80b4100751003140394188481400d04a0040a441d07844036808011150189000c031004000310110358a42840402d08510b01c641d5001e0941d1074034040658a0848003052240303502c200c0e44940c2aa01035000500c0080e1418003040345c41d44031040e942d03030000300108201e201610b402e0211014101515080210700180390185854070400b4003142c0ca01c0ea100e0b001e0441d40d580070000d40b100b581e0024000c0104440070380014009500c0b0807140c900a15041000401d82e56140420158680003e0703e00d0302105d45a5404031240d51000384983d06015000a035840d00d484a446075500c2200143c1c02400300a0030840c00c90450b0f00300101d01c3c1c0c00c050041211011915010041d126600c2403428200028104409112198040d035000078405226408001441c111030303004c00741c0200c0c0c4541c42000b041d0207816080c1003040c04a043c407508901452840c100400890f4003000c0d0a029520f010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 759100305 1250 759099055 759099059
    0x3020306060d060305010c0311090306010324050c0c2b0509060418090213180807020a170c0a1a0a30051e040c030807030512040303090c050306150613 66
    0x480031243c55400680b000d82d0346070613950440784c05100301e200000c0041011030804a00ca40065501c0380d050000800403201405d12180804401068445446101c00e09201e10310b8080d00303580e00c80d0000c09002c949845903600800d084910741a0300300395060b041c442541c5d581c480250544141e4015a49543c2044042000254101c400004202800d0f011a00407402e00ea41d40100b110034598285281001480d01d2181c219065003154078400d5154020401d42e10341130a0300000d204480243e00002d2115003007189083d11000100d6540044002124000510340e11585001002d141c0031010b50303038020013000b0800e8400d008078544804900790302000c0b8004000900c43d05200f100514620101a455030144070b2041c0600106198140410b1036562440c1361544500e0800c02507840042c040b890b00040020600d803090701242c00c00405608421901d00309864000c00421a8070800e80d030000000c2004102c910700824042d00801c25a001ca0100c0f814110401425034401c13a4082e0b4a00758030600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 759101555 1250 759100305 759100327
    0x506151003180f0303091a06100e030a020904030f020d09060504090f06180603030915080721060f030b160905060906090406030b010f08010e0a0327090516050304120302030606 77
    0x100003d481c4603a8010440248034a002004040300e1119440c0603010300302002880e45441303c3c02c944401c0c1d28a045100340490501003400d24018203406900302c074030117041105042d08001000c410004c103071300700c824031540050100c1e0a24031078000c0100044040000300190002c5c0c0d009001045064400000d401c7d90703da07480f000450070701140445254072070004005158101d0052402041d2081c440d02c20350400c4038009182c180010126418014090428004855000e0003038001c0c6100080400219890f00514442c0000c2c61008903a41030308500041c58078950b5240d400c0402e8031903203c003422581082c0802c060b40e00300000c041d030400820b000f0451035580318040c80b0021401030180000a506040b186440c2010a0700b02c2d040a82c1402d064030302500c00090a0fa032043d826151826840c0f40c08042c2c0049000075400c4980310200500005c80c030060079500c0301d401801d88407065a40c071146910103480c1400300301c8000d0400e00003206c801d5000c90003900110390288005100d02d1a051358130321 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 759102805 1250 759101555 759101573
    0x10206160e0a08100b0d110d1b1409061212030a021213120c03050a0e04140f0a0509070609050904050c031e100b06071403040819050615100318 63
    0x10010945520101c02e10b45130b00f41903c280e00d0a4502502e072030469000d65200e0240c0c404868817018018020100143e0034040801c85100310300e071680011559403591002103d00007603110a0861040a031400800c0c15813030400416684604034101908018203a41007005498000402d4600069000c020380c3d80c0621a9103400d520a00610b10660305202d6642041113060b0303441402c0e007043c40340c01d103941e601103070300310054418840d09441c06442e0068240046070241000b10803204101301070350144034200c9404e10002d03100c1c00d00e4807001c005c6a40c0300000c42c0e544800740c2c0700e060007188564000380f0072400d10090b1560301034040e40803215200003000100745000b4441001d5003001500c8a100c00040109004004032034a50a50510081c031094002a02c540304114004012095111022048000500a5070014064a41980c1c2401000440314042d84902e420499813800380b180007601c441d020000c41505220068156040d12003d1142540105002604410007018900c203100c00a43c01e00303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 759104055 1250 759102805 759102809
    0x7051e010c021c0311121c020313060c080403080a020a051803010212090a0c09060506090d02030f1b0f040204120b0405010908040b0a081312050d1503060b031b010206160e0a 76
    0x140e581d503103071500850290706141c09000110100401040026181c0b004c0001e4980b8101f42c060b0010b03600d40f101c0056031910b02c121a8000c0046013040d506908043d00010014030450281d260401c840c0d84440c0c52070b0480c840e00307042c01c0103d48180311080500d5440d10121320810006000145401c042c0610309180d040d0441d0115401c5d44075280210070848007808000c01000c6842090095a0900c1e0001d1260b01a905006025a11080e0078809540d000c00507011807101800686e240c0a03d811316404154000c03154035801003034a000424002c3c10207208450442c0e8020f5109400041e065036400415200079005940941d20b844141d408241198010402000e4550b40e0303d40d9118a10805031a07220f00811a082d464000c845440c0400c40744000f40c0341038241403911543d00c1007185586001030000c290550000c541b075810100801c440740e80030f101540c0d0200c0440705280d880c0d03852800300b05819a08180181c11401c00b00e0030b10303d07035001e42510254aa00341890400344507030229a0b024115 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 759105305 1250 759104055 759104057
    0x303030901090312050610121b09060306050d02060d090c0f0b0a0f0c020f090a1508010b04060e04030914010c060203040b010905150108010e0903040308040e040507051e010c021c03 79
    0x602d039210070103400c440d0509010030100300900442c079203c0000b642c8488a403070213034140030440e696804814400e511485500383c450b81006a040c9142e60024803202c41c5004441c0482d290142c00320b024901107040440179580208504d0ae800c5410900401404c0c410b00c04a9006c0040000880c02819490100010b0843c411600b6101d07050342c14000c080714a1850400300380900e104402c00583c43e50910b1960300c1c4001d442803d0301d81c542040b0200200b0120600c0c0414580150010440b00c0c810b401666034540221010320216031109840303000080300f13540040128590b24002c1140124241c0302201d103280504082c0b98508241e1036810030b9900c100d8080302c0c031141c0203005218141c4036202d000e40041c40c0c00c28006184a4200000e4003102c018010b040002d01000006000540d01300102d07000b541c1c0c40b428441c0c42d00d541e00d0078034852400c2614115041c1c09100f10102d80780c2403c0c0e02080c000c420081030810210f01f45070041d510b803003030090180d801c480c24482902030440940d03005034550344a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 759106555 1250 759105305 759105311
    0x50403080606070203150709051503041209081009061803110709020f0a050c071208030103060b01052a160f0306050c2a0a0203011e0b0d12120207020303030901 70
    0x9180050aa0030018002440b582c01409440c01507100000d22110758a1031101c5590176884107142501d00e0b0703140b03030300190340b12030402d04107640412540c0195005902c203c2c0a12a151800a015112441d007401802c07520b82c0107007020159800036400000311640603240008038000f508014119142242030107a001c0781003001c030121041010000d00c00140a0800110304120030100c2e0400244a48580f02c0c04002c40803c45400f260b506202e107000030700042a0502000c005890300501c030350024401507034424500150400325500442c21500e080079a46000342400d40c54140000003600d9603c2005d189101d551218a06081c1100070240a8554070500e485403500e1481d10105a96004000c096010340503c01e10845901c0c00406000340c1c0020844025024000c940852500c20304008c0a540341d07080032030081282180b44541c040300360001d1400e001035807600e0240000658011401018030070858643c0c0d600b144115600d40e40382e4000d00025280204540010386950000d960140031659 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 759107805 1250 759106555 759106561
    0x170c07061a2202131401182306120a0b0909070b120901020904050a0e0106050a23060c030d020403030f1718010209030a0c08070f0b031311190e0106140906070c03021305 74
    0x2800c140c108000c0407502c601031001c58202008814183c8d004c08112146085c030301c0302d6075120f586103415a0021980881000c0107442c0070031045d4054900e80a1860203000d085011607407103800860750317409880c1043c030110724042082d040507150140040c06880155824460b81c0d40e6540d5034061540620080a00031808108507450385007121a640e00c841e01c0b6004031032040009603661a155030100c140c405078060f0080030384010501da88035888001c01c05002c0001ca8020082d1560302500950303000303a54202001c6413281040d10b0502c2030380b038010216035503940040d000d00c0c410040400f0345c1071840005402c0019010119280c4480044120f5a14800d00b40c00d1091050800640c0f004024600c0805006494090300c4c0c211444064209a901c2e640707004550140f144080e1664443e5801404249021004a600f5080b1107071900480154090400000500d41e206040d0b40080c0355409500c2850301e00d880042000b2940140003c94180001c0907000025030354012001100881c103000104880ca = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 759109055 1250 759107805 759107807
    0x12030e040501060e0f1212040f03171614070b04030515060108101806120f0501060602011e0b03120301150305130c030303090201170c07061a2202131401 67
    0x301c05800140070440d604155046503503c001a0201d50f28041c0c036121302984d60300c07070b4880c1045140c03c0314803079100001400045104208650701d044034052000401c840b0710104500b1400e20984d01e1070a406580e4000d4800852008a2101c080d41030040849441c640e5441310044141c00507402501c1c207401486401a002031032407c410b0b4840400d103002c4207203180c00c04205221540b103005e4036040d5501da0310076605039101135020f813000d0145092110460103640c600500311200b81841202c455003040f500203003150050003000b0030200d01d01c4409848800000c1050014045508450351520035034203031700440710300400114060000020705041d071040c03184001c0d080d6900601000d8540303185005050100340c1840d60a4241c0381d1500d0045141d140030300049520030030700c94901e401c00d0090b10034400302c081000010a00140b00345001d00c500c0c0041c04078034902c0742c20354900641002a028041528880711041d044010f82068001410007410217003a441d03100071070b0080027070504c3c4801c8400e895 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 759110305 1250 759109055 759109061
    0xb0406032910060512150406030f1202010c143016020304080d050313060c0906020d080c03060d0314040915050d170a0203070204050903040f0806070801051912030e04 73
    0x265042d15002159490024020514442d24256040e0f9400160210308400404170990700700c031900400a02075107440341810450115000b20071500942c4104901c6d41150041c054840512042c0c0c0320710703402176544140581690320907941d20107124141c030f50342c6004c1803030200c0300240c40c00210f07800740d1b151a0510604120500c1903611700107640c818481002555000030388071014600d54641280c603a00c40f208982000c043c0040014122810080c0c180b14440e0301c415240b04550b681e60890307040300d07581d0780c0c2030f82c02d0031054400105040e0100005030190401c10400b5003c41e02c84c1c500041c0c500c40e402c100724040c1d00240c000440d52622003100d0f0851072080e11a0301c0c0a407004680381004d171185591004282104000528285140411440c00c503500030b00607668826006002482245070072507403203449520500480c01c400c1c01c05074011138400400500c56200b40300544803100c560b400d2508001c5410000d0040c1c10800112007008246182d4040481d009a03100352200800c42400c08108415 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 759111555 1250 759110305 759110311
    0x180a090f050c0f0a0c020a1706160f050d11041701051b0a0f14090a0b040f0b04050a0e0c071703060906030105070903170f0309060910090f060b04060329 67
    0x1441c4203000c0c12190709120f0b0b003214840b00701824503591089052002c248500303500c3c0c1c81a4521110220f846030031540c041030040c0703d00031140c82c00c1082422254241c81440d0040012030000f5824401984854500e074458000007450700c1045007059543c420580790311015081c0174800e65120420300540307244000c1c140802000c008445400c5c0200a00001c200601001911040041d1310000c11315962800c1e00f182c3c0282c801402c3c031547c140d140c01407030050b035001e40b2030700c0b12010300d40b040042c89008107400c0c0c4050307800060002c0e100b545040c28402aaa40240c2194900107040101c0e9001450b658541c1d05180002c079880d80c0c50380b034442d080000340c1d94000e00044c0280d04000822000715402410842640c1d445400d50241c24032904280403107019044254130000b00c000700340b01d071840300010014490004c50049900e19510804075030103540441d04020601c0900070707034000015005401000d08054080c2c40010f00039541c1d11030482c0c5510444843c908180e1100350420803001e480000e940c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 759112805 1250 759111555 759111571
    0x131b02030406020c0d2f130c0212130b0c120a0e030c12030a110c06030a0605091e010611250906140d0b07110105070203030a0501080f0a08180a090f05 66
    0x2401d900e40072001c48051200321b440c484084541c4400440001200f4034102c800f0381850071542001032020000d00f01d40850350098442c40300c50882c0c0000030303001c942d203552000160b000703d03919062548190383c02c200c0640c000750050302403005101c0350907406011034080701e6850380350840a103c1414200922041058020080450a0300c0c9a4400100302d07160300040b0700d800650507806107051420304282c03112680d40b21400006006240002e40c025070142c850854550f03141d070322400b003007022864207481144e12000d00000100100c6028040c42008021f03684281c031044661003c182c0351400e81305500400310059044103022440f001d00c00c01014005101140540020b0540041c8003600e48401c014036030420b0400082d6182c0c0714a4120684140c150024015403c000c00040d449400440e85a90f001e49400c0001514040c009a000d1084001c64058500c0305840d0b10b03981411b50007844440441e14240e03d150380700343c44540811000705040d81c0d00040c55240280d0010944c0d07005031080c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 759114055 1250 759112805 759112819
    0x406032d08161e031d04021c020306040e0d0e10090503010e1e0c030a080306010504050d05061b0918091c080108010614010f110c04020d0f0f0c0e131b02030406020c 72
    0x140020380050f40402c22910117aa43c400180301c01d0000380203842078980c000001464880194500b4240d500a5801418119414081209200700580c2d840b003403194041c00003401003240d10003e060003101c0850240c030364601043c129444178086401c0d64404107099065921050803119141040d110b180074000154001e081c1200003c00003d540e6521010040c01d91349002010a800c0da00480480b002054060414a40b400d01e03400e0070b607100d5404440c0b0f445040d01c070720718070f0958481030000c4482c2590001c0c90400c0b0380400d44941502010003c202da00305108a080e5009410800e03403980d902e09480c3d954140b95913040c152018203444055026510380e040c0080143c215a0700402005100a405e10709994414042c1140b6440c10b40d2050705e558100e4800120741885c5216078004001d540c880b214248480d09400003030804803550001d403080003030311280302c404040ca0311248003440b54524900209140000d41c507a96a444207012503680035910001d010401d194040c00000d0160380215000303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 759115305 1250 759114055 759114113
    0x804121a07050415210e0706090b030105090c091504090905190519050c0405040308040b1803030a18020a0e060a080102040b0403080c01140106030b0307050406032d0816 74
    0xa080301000110b2100900c000040d50302102da0403a003400c00505c600d0002803010000c130040964a900680c0076180000c1c1c84070340045614603108040307138100c07140a008401c0b182e6422417441501d070003812410307600c0000082c56090001c3c03864080c00291401003800601032181e0b280c62407402c0c01c21890300701c07400c04030201c50f0045603011501d480e0b40c110b50041404007007024684942030414003100c8a901514000510040c11390186074503118500ca03004802c0d6646450b49445071441c9022024241039008000042803a0f01c80c1e00109101612a42d220a50b01c11a0b40000c600c2e0a00d40c214108010302801040400e2900c0603200c802401090001c41c030303060810b6248030003482030b8040904010300c00200060207003001d52000020b210300414000075940c480700f006000e0054000c1c1c10f40b007849050800701da546070500c01c10382182c2c0d01004040c0c581c452188451904403542d80309500c00b0507201c0040d00400d02e80380040500e010549111003030480c013403800122400a04112045111042d540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 759116555 1250 759115305 759115319
    0x1208040314250c06171003140a0506070f090603020712140403170705010b1225081605010e01031e1503020303122202030606042004091b030b1302070804121a070504 72
    0x1b0007064030707000705207142c08103a00c0c0b14951a100000c64010018401d10040082060f4401ea003101e50031026603c6060990b0741d400224240d006030013000d08404070b050288107801e40500710600200307424120860610b030342d030b07142c0707e4100c19640461a042c5600081a000f003000a00c5001940001103e1b141004403030b10040b07075a500c0c3d0202da200c030040303c00000304c038105e642294031078000d00d01c0d00d088031418032050b482141401c6140c41028041540f254074900191b002e13001c1c148c13250042d00748641014500c4140c04010342400d111b0404031660340792022015031010310040c0616044450103c1041c14844644003901c64100688801031444a90090050358007041064110800304c6d00481ca0002c1c0148500c070110221148400d031010008000a183d0440d400c414040c9089030030090b200e0034039040680035608600b603110f502c050300845a518112080d4060246d407400307940580d0616841d41001c0c00e8802c201c0300309a59220305080c1c1450a001a00301c1035900c04c5480c9851814a898000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 759117805 1250 759116555 759116581
    0x110304090c031407031a0915150d02040b1312020603040b1f060c1502130b07062c0d0309020603061c08070f1208040314250c0617 57
    0x11145100d8680500c501071611a412101e10f00e4418803c0c04128140280301070014640309501c5402240e403030604000c0e615000e41e24a21407100d032180011454510300c20020036a0583c0700d0101c0c209402e000000d189144c130300c0a40040d210421415943e0341031182ca600490f8001e622404030701e00381140c2c002c01a02c80c0410ba9803c143c2c40055955642c9408a040070300d0034103490019034101b110540050059406050308406c070303009807140c20035000e6a42242003030b4450f0380780281104200c52420840140c041d00144840d9000f48d100060341142e000348000c00b190b00c2804da0400a0079950300044800082c09030551400850800f0001020203034046051400010203181c03040211049880301488401800108254420b4046540b60014940401c2070069058183c4012703415002000c4250b008010041c010360301a1542c100785203040620710a260300c25404c65010072070850603e0340004410000d403401621a900d210102820b160b8010442c44c0c5007441128045560024055103040c845 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 759119055 1250 759117805 759117809
    0x20604060e0f09090c100207050a121a01081b030102120f0c090d150b1804230f010e0c03010c050d020304080f031008062d190905030304020f01110304 66
    0x10800d0080407078400d000800481040c16440d0704100c2e41c80400100c4500070030300405518044461742c1e1442c0c00282c04a1f5200c40c0e600449401005454013841800310503d90594030310700c9900c00c0c10147d0906105d0241100c0c0a900c00f500075444204441350103100c903501034000c0d840542c002c500b04214000c2d460034941000c0d00d80c00c4050b0803540450308000860084980c1c21601503e001c0707124902d0300e0708010b544503410740310410900e003a42c19495803406100c00b03012139040c0100e40c10140c8840e111270003045080901183d401c0c011003416014410144980501c0b0100c010000903800d2aa5011b1418408411188d5100b6403504d91400c2c070b03440d0010259102c1d045c6501c030058881d5110b01d08420188a0614100403424000c030810011288000310319050701d20080030340388541c840c000e88001620000c1c178001002c40404601c9407011148000f560307803000201061f80042e81958503030300119040ba0400303840513003001041000790300748080441b0348002d081c40d003032051800396101913490780034078 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 759120305 1250 759119055 759119057
    0x13031a040b16110307050a1401140106050903030409050106121d03070f08070f0b01180501120b06040b060c10110c030f0c032503020d03090206030a09050f011d0f010902060406 77
    0x4810b00181d80d611418240310000415411640c2d15126414815925a803961046800701c14426140e0361000040c000c11a910702400d0502d90300741d09009040e102c5410025203940c00d88001d00c030000b4040d585018250090003192664603842554040d44825540114880c14800416240400406400004603014150482400d41107a5902d2804000354881c04c0405032003001c0c54a000c4041c01036824080341202c051184903c91800d211045000390ba00074442c2c03020442545a5180200d21001502c551200c070090001034a0182a40090324942001c0c1c2c0406044d40a0881681d044080740324098274200d1007845035081407001c444055880c4100388641c1c02c94500419248030762035003003040c0c038034000e000790031101c8201604c1004841c0d01c1d8184001d0300103110300b10010348100d020b071080c1d42c485a0003522a51a550314540100050701c64014100d82a12440030346101c1d404084c070844031a0b40c2c080c0e080d1404a40b01d620143d1030000400c440c3c00b041e0b454142d54100503030310542100d00f11402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 759121555 1250 759120305 759120331
    0x90c150c010204080f070f060806060307030207050c040c08060a06080f010302060c2109130504020d0b180111030a0507020f0619090204140610051c0e0c0613031a040b 73
    0x2182680398007a00403684800ca8074480c0180d011001100820384c5400c1d01c0044160f6404507075200801c442400044c0e60a40e009041040400c041d184070750000e2010728010b50458083e04459000b107402c69000d901c0d03000015105500740915440c011040f90002e11083c5004819030802c000b03241c0c07110b54103100c002e1058000040c00d00c01d110007801881c4040184031201440c0514513003054035254448540c881c070030401007515207a5000c01c7c0c81010f0040382c01400c0d190303e84956036581c091032140506001e1485003455180400180240030307000c0700d20020b0b5021602c90070500100c0003501c5c0040d042030701f590404000c45526000c001213440e072107900040b1221018840c2e0030100c00924500f04081d4100d070030300d03181c0c19903982c4850b5030601520382954011184801141c04894600a05c003101100030001450344c02007002d503410140449001c281a2112480f402000401c668040000d8005d0065600b0003082071282e1419001c0c18a04c9401e0603c00600d000d0390b4019600c10001c2c440c00030812 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 759122805 1250 759121555 759121567
    0x30d09140103090c0b041505030919050c1005090f010c0f030507170f1201080d14091507050d02191e0c030204062304180308190c090e090c15 62
    0x2201c3d8100c10360458004101584c06501d030740d4106410385c45405400c03000c80c0e400d40c200178200d00c180112407140d92000301030181201090701d460507001d189034080d1110700c00e02c280d10b0443c0e914100d1084046d00540c0301c4581d00c03044a42404900e201c001c8500b1b05001c444145e0301d02003001d501404001e9903042c60440e598142c80e02d0201c44c004045048403070418800700343d0f020040210300052900b022108045501c9a0303a8003e003559802d03901c4551000a000b451007501c524481c0b60143c60707000e00003002c0c140040c54014481c4219000a40103841d03551020f0340c1d455031079406008001040c1c21121020304092103540351a40039000d0070030048860361800d0900d000b40b1000d4403282016550040c800c0c000ca039a00c00079900c003c2203040138113040a09441c10415103160507c50800c003c01da075201e10541c1c100c603880a9590b0040240364801d503011303007090078200394058071420b0401201038450240007401d201c01e400038488010a111000e502c454440685644c4034002c2d008001d200f462303600e1b0b91782 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 759124055 1250 759122805 759122807
    0x607020321040b070b04060f270c0504050901020a0807080709050607060914010c0905010c0c3f030815130f0e19121713020414040303060306050105030d091401 70
    0x880ba9500102c80594003241440c1081844207400c1d00450044000b0310080c800c24202c2000c4038000c4e10400450740c01c1c40c8201a80307401c007580325078030140203420140c5c0e81f0b0356807008207003075a00880751070740140d46c0002c207404603680101c1d490ba0040340341d01e40b2007003d01c0c12007000341c404030403809990b110760000306a01080004a0b08187c038040c1d4880e06c10b1400d403094406041c0a0121500f5543c04118440c0c00440d140d48a0340803032840c03641100250703d005117000c1100400c0780ca11181d0642c0c1d100707021840da0309108020071491900710340d044900c400700c0660400800040001e400403450b2454801d443d0581d94441c0700081101c0c000c04000102550000122001410407e10403400d034001c4d00d0440404000c14880c0c00c0d03080740228513000300c80540010440d00540a030f2010030441c5502c8020400c801c540c01041d190b041e2014000141051032610941744800045508070002515032000707108019890007414010441640180400e043e1310782c010300740d69807900841c101a520003001c1086070b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 759125305 1250 759124055 759124057
    0x10e010317041211041d030906210403050c060708060d17211e060612090c0604030501020a020f0c0a060e1f0f080603070f030803040309030501060b0c0c0607020321 72
    0x8040301c10f10b510a10340540b4100c540c03490700c0c0702014812454240c00d0300d45007101650a07a010800340001e9894207035400200170041e0070103c402100c0c07900101c0742c501607a0010124070f015a02035110140c8031040e40301c1852800c0f500034941410418144280103082d1900c003600324031190b000100300320b041d0803001c440040703001e2102d9410300b450640c0240840a284545801d0040480c2c170a082003410341c0c031038a030300317020000c0d02c00c1500030b4000c001c0747d1145001d5900c140d800c00c65800627900c0c40c1158000107846a0070503041a25241d60010b1011601a01004070b8009501c0c00303400381000320982030010780c9107015889000180080180041c400f69205902c110600003403c013a1882d1340c5110307400030071040810611070007203200b050106d851803400054001c1103440c6000c0d184580c6080d546c8180d01904060811810702102c010040000741b030a00031480944081c0702030940392003040e01c12078908651442039034001c91080044001585010401ea030f580c0c110320001c5044d0f50b0114080d0091 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 759126555 1250 759125305 759125309
    0x122003010603020d0e071403120f0f1e0a0302090108062e030b0409060b0307120f020126090105060a05091e060d050106030309090f140103170909181203010e01031704 73
    0x35071b010f40800412040801c1c8170041020806408881840781084030b42883e900c60021544d00c0740205003c2815204200700050600c009449180141d80070a4049a05183c106200745c01c0440d0700414000c0d000e5074010800e6920040494919030780550304026000c0e8010441c02d4207441891080907080801d00941064102c464050010032074051300d41824070003460807143c0c040c464000e1950004200070700301b22100129030041032040c3c0041150340195005910a41c1d1009032a0408030112400c010710800f003882a4031000c0085090310b803920400003825042d170081449440c842e810300c400c0d0f59800800e0030060302d0215040303403240c4940000500380121040003d0484d800d000c07001c410958408402c8003100c0c009401401030400c5030b01c0000c00c3e03c2d030007414140001c4802c801040440c0401510010500c4485030252a00003900041808101d0403910416039010300d030811848103104119841d4014910320905c1c2c25541002810f4140200600c005411700085c60302d801c8405d04a0821100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 759127805 1250 759126555 759126581
    0xc0d110a0f0b040812040609060305041109040b16050f030f06060c0616030b040b010507060908040810141005010206010324020c0a02010207050a0b0a0c050309060406122003010603020d 81
    0x540e0035075071a903010b5075502c2400340d00c4c40c2c3d008956202070807245560943c0c0a4071810b8a52640850070404128001c10b030041082c0c0c0e015004007101e01d80c0303445103181c0b14060f60060380c0d001920310f0100d1450844480c81c07032460041260401c4404c0c601c00e800e400f501e4000e00e181035200e5943d115000041c8160080c2003095505004100a01603120781c03104c6a0407030075169440610110f602401004116603251a02c2030214a04100178070000d029a80415061841200d0003810507482d884440d140c1050301401e403041c1592100e0b03d08900661f1141140d1055400d0004044541071400003510340c04181b1006000d14560b074103190400310310b40040c4028080c062030454a6000e80a0107503500d680820b070581c05030045040115003803c00c000b451083d00d840007081d81c508074a692003240c0800d12540140c42d40e00003032200d0301e03403595120000e1000341425030f130340780d40303000c640e0031000441c1c50b40807044003003281003e000700d1207059807015241111181c2c00e0068032801070505500140080340740d604 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 759129055 1250 759127805 759127829
    0xa0e0904140d11061513020c0106170c0102060c040807150302220513060312050a020102070b0a05220f0803060102030c0d0f031109030309220204091a030c0d110a 71
    0xb1003855805000d0320601d11111044448a40300c3d81d55411a0020500050390801c1c2084800031800d4003580041c0080c1d8011000002c0b066540c200340c2d0b81c030b5448500c0095407a000500d921300a91b0b0b04001310303a04503041c004a20701e064a0400c81680e80d284c2d40c0b280400b08a048501c580b1458040d41c10780c0d10a9501d05c6400c0c9026400d4000e4800d03001d00d9000c0c103803060281501e4242c0030791680c03242009495200e071102401010810064480d50031103402c4104643d02000f02000103500034094a000c1e218040000c202410011541d080200c5080e291600e00f14400304440081400131104030f10040c2c018804070b5807030300c0302d400407411072084004038407043c800d4612030b00c0b60b65442141d0fa4204001c5d69810001c0450790a0600c900d44224000c09074140e000b401000068500000c4250b413104840001c1c401607403d5070300d0350040c1e030060750000c122a960341c034a022500800e13511000d031120044006d025001d590b0800101a145030342c0c0040c000d8030303422945c88034544420b150a405002290095 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 759130305 1250 759129055 759129073
    0x90c070605010b09010f0e1806031e010605010f1107031709030613021504030c030b06271f05010f0e03120c010f0e0c0108010605281e050a0e090414 65
    0x303c03c030369021100303442c00507000c80c0300c107080244034500b0507200c01d400414540343c00508404110355144080c04541d80750140e030025002c1d103484011410602c44820b00040f0702a8a401c0001d80b0100184921070203001521107015121180400d0300d030281c80d4019001c410520080c0f030034000c0780c01201d40c090307010b00c19001403200d0b42051030b0148030201d108440b20345000c038032803a44010354011880014100d04d00100d0034000200c055502c0c5502c00ca000c1c01e00c045144118050020740380c00c00c3c111260b0103400030300340900c0c030034402d0009a8900e021990200e82a1400d03000030b01c80a940c280000c10000d000002140c50741e02800700f01300500180c5541c43e00c4140780c0c082c542c000d1141400300c000e014648a280f4a0140d00400c4e5450f040ea0142c4a21035103a18280042c0c4641d40304040751402d24034a803000141c0101c0da500c030300001810f0781c2d564411481c040b01040340d09540c201c100c40306221003406400d50f0130350300c800f21035401c69050301c0f03003011a20f807880d0100c40b03c1c1100e600203135207004031006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 759131555 1250 759130305 759130319
    0xb0106050d0f0914160b09090604090204051312090f060809120a090501200303040f0c0e0c0415080603100b030a0b280234020d08040612020315090c07060501 69
    0x10300c0700c0108078801902c0d1500140c844d50b004405e820312801100410502c881c1c646880c0c0403204d50b900c003001400114044081d9030004040311001c6032079180300241e00c2c400c1814040448194201d1100e1820101708a508046503501c07000c20900c20881004402c000180c00c0300400c1c05800b00b02410610f0036615007500c0f443c0540607540034051a400a84468100320f2240c01800c1544c260a051034003030b5103540c0b9a078840e9148084848010364040701c42a500103203107805410614420b260504a080e2240e040110807106640c40c58050000c10004400b030100390b0341e0100e25000c02060078400066000c905c08007017814280d80f80c1c0c024113102840300c100100b0013882c104900d1703025010141d402c030034104421014200d00500800715080d51044034030186c01240c074200d8685016100f50b005400c1c60f10365002074107410900d101151043e030301284c1081025000515142d40b40000d1006500750302e0300b071801c442d46e0b450103070285229003590400700b0900c2d0081c100311000f050300001c0602035503071070b03090b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 759132805 1250 759131555 759131573
    0x12040807050129220b010c0c0803030106030e03072d0c0f140111030301060e0d2001180303020a12110a0303020403051506090411040b19050a120b0106050d0f09 70
    0x442101445a42112440b81c6080010300d81e551001941c039844e490044001c50000f0001000100d051100c5000f8403c04a040c22490303a000b84800d50055a80b581030480c0101911000c0788000615801846401d0000d10f6a24001d5006e41051100700e4070010540bc481080d0000c800000d8401140c004e008035981a5000c0800b0940d007080c1820388282d01ba002c011038107946a810506000e40060005116007485203d1210298100070011110851a81c845103019682c914a102c0e035180000f4802582d035800071003080d52030b0490584c1441d01c910715140691100c2d407244009144c0340412401a080c0ca001d180648800103001084540b81c80a62402030700a5002d0f000968642c400c01c0001104210070156152281101030001d4501e41c07650794510484d0101c8942c1135034000e4643c0c0468485881c1c00c2c200080b02410054101d0700c2d14988001d1018000d4590070030800240d500d91210041440701c4886070444a4500d010346d55081401450780080609190000c0b166080c0b244002c18066080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 759134055 1250 759132805 759132851
    0x30a0504060209042c0303040c060e01020c090c091201061805090102040f080d031a100315051903110607020d032d0305160f09060309022404030c1505120408070501 72
    0x440300046102c1c205c1002d43d036070300003214020801c0026050500000d44252443c42800e0b8042c0100c540610f00d0b680090b4290608451040448401150711501403030482920691100101c000b0826241492803c80550b5044da4054817040e807101c01052110400b58104d800606142d08092010381d240d00e000c40d140d80606100d4000030b802c14442c2c1070b0640540c1c0e8400c102034401044900480320318081079024042d00028103a503039a403441d00144c4c1d903c80401d2000d0003500036001180150543c03600c1d42580307030b040c1500c1c1d004017024442440181ca854140c030400d1901801c0200c14005240300d000c00b00d07883d0034215035081c1205107001c1c04032609900403e016121001181e201205059030481e800a088014000000c03d0900c04104450095002140d2940050020652100c3c05d0782c80d40b039040c28140d8020350190001408006000400c0034100c003134178802c1c400d5400010165170080160054880c0310021484440200382088009412148025401b0000303011402400e15034030741501c880 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 759135305 1250 759134055 759134111
    0x60b01020f16180e06010b190302031909081902010207060b01030b010917030909090c01090e0f0f0a0603021201050718050334120501060e010308030a050406020904 72
    0x25464804003403004202d091180380c403850711140e0580350070411802c581c01d0f5008541d0311136075075031032501c0d401040c40901e000c0c000c5d800c0c2242c0c2e034031a41c0304554071307080e400c9490504162050052000040c0d4a40d1072104400c42414040750907d01801c0003203082c801c0111001118039141c80e80a80741d070301900503241390340c05004200540300c050b20040d000d42e04041243d03400100c01c10000d110700c210012030800ca0041c1c1408603820b01205c800442c200c3c62003620005031503845400c01000569200440201421007848000c45506101845010940014001d20720002080c00081da40c40c46030351001008507001001c01c154000c02c151054000d0101743c991100140c0c01d41d201c6015482c45e06c0401c011210047c00514046a078034031808814040c000440d8100356402c80c101c01c44e604090814005440c085104003501c41a40c0780850840d501540403a090243c41c100400c003181a20060b00d40c80448041d01080c5079640703150140007803103100c0d9420361051411155014400000d14480842444 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 759136555 1250 759135305 759135313
    0x40f050406050418060c1b1b15140f130306090212030c0a110f0603040c06020d0c030e13061e0303110105041110020307081c05160e1c0609060b0102 65
    0xc0300e0038401504c101500380320780c20a413402c501002480d51340c0500c2c803900007854415801c2881c80e403003126440b050790341602c00f80c1c5d4144040345035404c1440150018000e420603490340d1312078900064030307001d04409010600c28000c03a550444006c0d02085031800340c010301245141e941c13245003040c01420b0900d0203a01503072040940500d0001c0010895140e10020f00c000c220540b169544c02440303903100c86c041c64024519401d1010b8039100d034400b40d405180b080505003030107828244003c1c5001480400d1400b005811170407000441d8100707045910304203040d06c1003101c101007551854007504043d0301640c080061619412007400c814040881640d2280e40e8100700d6403044c59000b42601d0064601a119617148004002c19143c18207602c00781c1c4a81c0e0060368104402904c500845400c00008c007112115030103210074210496100d650340c4120300c050584c1070310049600003420071280079a1076000b00700c241022100400c1940c11004065417004050140e1a11807404d1005400080e4180e070151013 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 759137805 1250 759136555 759136559
    0x60b0d0b010f2c0d1110020606060405042304030306060f020624010c0f0303090c0b1c020310030503070f020f0d11040b01030e030307020d02071502101a0303040f050406 74
    0x2c440e401d10030b1080e0040e0303140c10305a10411801c84000102051282142c60400c0601585032298030b00c0c1c4030960b00410314054103000200c140404118030021041c11900060f00308070180ea03850042d54142d5100352000214507260b400f071502030030541d42d5080341c0000305104100804d42e050700240243c03012543e8004400048010603030755230340140c40c82d48296001c11105201e18981d051603040032030381450590664601600d0307200c000c0c00c04181c1030b0f000a0700d0742ca605092165854030380d0000c0c0036000da018500b42c0500d81e00082c0c10354190404400c0e503000408a50000c00090401c0050354228040d40c0d40d900300351030000d00040320030f070f030490140341c00d451a1034240c64000482652190410082c0104400202c00c000c01040e03460b8105041c16070b03030108107101c003d040018521644c400d400034001082e11400107850050301390710a401c46100c104a07020b2a0358007040b2071014003e0140081071041d2800030340c40600031010015509484040f60000d448070041300c0307a0044603000d0720104080742d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 759139055 1250 759137805 759137807
    0x7030c0f050109090b0a050d060e0d0503071b03020f07090504060b0604030302070326030a1e050610030e150c0a030f0606050708030a0902040501090911040c020a0f0302070306060b0d0b01 82
    0x4584900750100d11400d10400000d00c064100340900c1c44010300180d1004e03110b90008030b02245102d8280d030321031303a0344480748081d00042215451843c8181845400c0d8581210018803092503c542e00a4190b0350100c0700c02054003c2107080345141d5848203441401d615030189400030f0201700d40c140c07034507820000c003000d0030300704007040383e081d607415a0141c01c0302070035030b100c400c0c1c41e00140d041c0301d61000846c699603000c010081e0181d4000e8500c1d14012656414442c29011740510313120143c2102860030f403c1c0141685e0b5400f03d605680c80c070b03050209002001545890511102d245114030301d40006d010880c1c5424010010304031030700107850821800b00403100d0b07001124101c0c0215004504108222000324a4010155910403610030003c10301d0025a408076042c0c034000ea200f400d109072a0510141003200700399446036019407d40c1c080180c1a1b9203e0003e540710003d040252460010f8807030541854802d00585000e560420320500509075038082042580c1d005801a81302103241055642c030319 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 759140305 1250 759139055 759139079
    0x320040b0a09290a020c1509131116020a170309030d02031207140c0f0d120b0f06031b0c0622030210020904060f08150f010609030320010e07030c 64
    0x20500c2040c42c40c043c281c00c0700001d14070f038402c11400c01948204640b002a13655032403580340143c03040b003040e56180d403200e000340881c01c0f02c45503c0c0c0b11458100011448000e40560540710520380224106088071081c0c00403032011000c5400001d564100304c403aa000c5404008010301c510402902102d40681145c40d0032a1070340a02c00c50b00040000c1203000c50350803445420654810100d6003081d520f000c1c40710703010f00d2402c40c42e03505001c0980c000d50040b0024640090342004000b140c1328080c028000d0000c00a105a07400c1c4210f02d00c01c00d4088040346040500c4c0f46c04240e02041c080c042c5565010f5120055074941c402c4643e880c03080b0840b105801d4005c41c54141314282c9034103400600202c510300350036401135088038402c0303a00b060340e0f0100080c80ca0b15820140d0000c0c44040094100d05944800c0d000d0342840041500340030100b0600100318250340040180c00312030301450051600c100601c090130b000010048501201e45c208840b40c1001d40e008182c000440b44034000c80310200b90345403200c0c055 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 759141555 1250 759140305 759140339
    0x1c1a060a03170702151204031d030c0d030c0f050a0510141501110321180616030207080711010e010f0c0209100f06050c01060f050d030320040b0a09 65
    0x148680d80310b054050034626001600783c0500c01007880c10114529403a030301c102c1d00001c11800d05212580244014160000c01c198070f1003406600c00700b9038030501c0340407a5440c801c5460403130240d09910018001d05100c1c12040c0440e660000c98070040748650b0805036a1a0203914050721a8081c1104000d540c1c985841200310802840324400c0e09036503005452010f01844040481c140046c924a070303c41b06c14240001d2025441e81074240f01d4844900c100588400b00060948201001c2080105c2d000140000d0390341e88807030200000103079512440404c6001e8000c1c4100101a01000308510040000d001100c020003403027a41d500a440d1180d000456140c0181c00c000c9001c42c50038202d0801500b01920040d83c0044950803c48100d40d03541c1171502d1800003541b0150020344042020301000340e00b8012000203100d4040c2048405082800143c0e101581140090a0603965455400c1483e408043c3c2c962800d0f0240000c1c2d252555900c00e02042e9008d80e000d0701c0000c42e101404144070745806c90f4407030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 759142805 1250 759141555 759141563
    0x60207050a0504180b241c17090607060b010f08150d0302010905100c0809070b030a0c03091b090e01020301080d0f0c050604050a020a080c0d111c1a060a03 68
    0x26410b18001c1844010080b07a9900c8030390394011030700800820041c0e40200e0068054001c80000b51001a29014940701c15104003407090b0018100c04404139040c034000389110390000003007650149000d80b17986c058802c40d098590094000301d00ea905000c2294020768001000384c99600c403618000d00100c8a2910072501200c3c40c2d045074500943c54208001d0240060b440380c0000112000e05485441c0703004610002e40b01041c1d101e1081240d403541c0040c545030001c000340001c20500d824150540b01074080106001c0025a6a82214014074820b030400c5416503082200e1031030031407030103200c0070700b8801901640d4411410400020220780051003124101c41060005d000115007400e0210344603807030002202c080002c0d41e030700c210200d1814414180580c0c850001000d005000344103100c600e507019440704059400c5207040c0003454403200e0341c1c0500a980204941c584059400c001001d0760721058807505603041c0c0003845010401c200d00f2001c904030645944800c642c0d201e608000940d200707804018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 759144055 1250 759142805 759142819
    0x3020409050c090d1401020d050c03010f120308060f0d060507020f010e0d09030b040c05031c0e0a031101141e0c011a1005251208073216030f0906020705 67
    0x11000c242642c610385c1c40044070b400094544040180d1940a941081d0388284000100100401484e94044012401052500c0d4060121101c40d01d01415100700104100c1c001c4014103001111503440d580c18103c19540003804121034200340c80001d5540100c824180820340c80e003862129503180c0011224004881035903601221820f503543ca58002502810807152030b1340755040444d05583c24050b03041100c0382c900002800c03180b2150010503481410760242d01a6240a0051000c2080364200881009007802c2a01d510000c50810344640c4c821074514400703440386141840445c0381014018403800a6160003806960511104403c5181212000c01e90180c41549000032150040c400303000000e200c4846c50355140d580c984001180c018135a011a024011202c20000341c580040071320380c22940501e8218078003d21021000c1001c013200d03070325201a0410108041115801d0802c4900a49450f80c003c2162211494060f0400c0c4100c00d12402203040c882e00400d01610004c0d2402c02c07258014404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 759145305 1250 759144055 759144079
    0x603100e0a060204030b2a03010303050702010c080c1f02030f0708070915050a081e06040207060207051b030706080f0415090b04032a02060a03021605060703020409050c09 75
    0x201004000c04500e0310090300481ca80c44000c40c0b07180c405840298043c8041e580380f403500680540d080241441108141d41c20b040102014040c83c2c0156070540b580340c02c06a5a440c02400140c07400c482c4054024140d07000000c003000d0015010840c84080101d02c6410324508100100e044180c5c08100d5902514039241800210705d10b00c503030701258009069041018400343c94410000401075078102c6a8041140022600503207944100e4095015900403807100c20702d81501c10410001d0350140140c0c0c4031755000300d044014025994115900b080e8800c0444a80c440c500c10b12460101586070051f100e40514500080ca09000d498101d210343c40c280031403801c0d5a80c3e0354500000c036181c02c000030300c00c540d148036060004282c5026140203074020740301e5075088001d00050641c0410860011000940e0040c0800016181c44d4251180e5062074203015031a0b00416044400300798941c44040c0441c840c40c0d090001c0a40c15074001e000741e81442d601480183d440c0050320205114407001c45422400702245 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 759146555 1250 759145305 759145333
    0x31204120504030f1a0a1806050613020c0109061b020606151c0501080708010c05092b06020c0105010603050108100c030b0402040303030e0f0d051204030e040e160b030603 75
    0x10090140e011800c0a505160b12a00da240c3e6501c1246000c4a000445030740c808000100c10f011240d00c104281000d10044007900c200900102200038014100758030780e0080756051f03950544031095607906400c11900da41c003d8031513901920049506840051401041401200007444072144280c40c640081c046511004148540403203001008040000c0c07e0264060248048501c0783e1007210442c0c01043c1c0d541400d441711304028055001c2d1100d41e00d40994420303406d070024180c8020f048201c1c6c2070840043d00314440c8100d188048590700140b046812107504001030f980c090101c9503d100e000304510782e22104154110b560a0080140c141c0c40844c01050b0480750b5001a040f10690b40303000f00f10032202c500410240e0f0842e40044001c41c0e00d0310b18401842030200010b050442000000301450300020710040d003140300c2d280040b1100b2030150f0009003414051000c046071903030b01610421002d101c0000302d0f134681ca0742b6282191554030510000441c9010319007640c1c040d44000303020b41803403003000d12 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 759147805 1250 759146555 759146573
    0x11b0e041d120702040b100e0a170706050702030106080703050d2606060307030e01110933070602090a0608010e0601090608060d230a05060a0603031d0310050108031b031204 76
    0x3c040381d001e5150051001c16888110366160201d0b0306450316101e1015030003c101d0081c07425044034009032181c8561841101c0300250100440d07074a400d1590340c03000340d03001007400340c40d0580001147d4415900004108400051141080003003960b03402c0362665515188044040c80414810107a0301000c0850118600701009540107840750a00155807810440064203440000000c60f80c01c5c00301180c25001c0d8203141d030081c1890b02e4041c031030042d6010843d101e041140104502c40c038840c0400f00e048410054690304441100d00c0003012a80425680d0320010450f000034010040c1c42003031840400c4c02540524071840a540c6c1c1c603102c548241e500c076010307c10725469000341980c40c0011842c3c2c000d20000c8191100228034100720140803100c1c07250070014640800509000c005924109040020a92006092106040c4480005554640880004c0c6003600d8918884806460007000103100700c0000014601c011024800108014404429039124044c078064141c0805103000020001821a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 759149055 1250 759147805 759147817
    0xa050405040216060e1c030b0d030c02060408031303062702191a0a03060608150411251502040e04080a09030f05010207031707120e011b0e041d12 64
    0x22642030840f44070740b9020181d0b100f02100c120650460681040c0d81403000c1d640c9443c1d1041e134201403209481c14008581e551810020160410031200818011135454104032401031480c4801c0b039440d80d40c5e0528182200344d851004039a2103181c500703803005292080d00c1609a070252903503140110f440c507400b44840b4180e135040c02c01c0c942090010104003102107512008410461907000780e10703086224070140442d1071a402c0002484420820484065480d499034034010100b5540400c07003c0105042c9016405078400301750740008428a08010032103141800c1e10f440380120140215001d041403010308070300c00c5014961048202c18000b6000c161031000a2002500602e8806005580c2e0786680994030803407201101e01e650009000f2051507448908440920300e035109986890400c8000a080c0145c006224050315458130602590313003100f9030100682060a010660000c004210b00414454501d82035501c140d207040c5070300a48003201c0c2500503078403034a640100401040098440030710b400007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 759150305 1250 759149055 759149077
    0x6141807182c0105030106081015420e0d1103060c0705120901050d0f0b4209090a060f030807050f0610050d1707081903020a0504050402 60
    0x28000030b01040c0b0004071001c1030400302e140501d8603615407645000440681c0501d200341c0c10494103011050011580703142c10000003000041d66441082c0340b1040c500d507980038061211014000701c10154021160744000c20040044c40b0310740501c2c5451020020540f8031800000ea8013414108440c14091040c0c140c0501440c0086408143c4400080c5000b00032640c80001500c08699041049020401e8a200c0c01e14000c41d1404c00341c3c0440000c1090044450b548616a2129840703660b00034503520107d007004010f4540448888215a042103618443d4468139000320003c400c50100c800341010700c01000b860841e40ca00d4030741c820b01085401d400140014401641e54080002e5445d14030100f18011031041004a450b8003807801c160f41040e100d140d02500d0341d0494001c024160364182c58020035240300701c4050000a000e4103044450456400c00300c0c81d11500014003005014210019205030003881849100460301d14030202d042c0c1c0211603001c030228405100030b22591030075402030944c078581c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 759151555 1250 759150305 759150347
    0x30f06091b0a081e120a021504061b03020318060c040b0c160f030b070c1716020316051f050409050604020c160303080c0705070302090702030702030a030306141807 72
    0x190201c1a041840700341045481805501303031200560380034821001006000b41e010b6042440d490800381d2201c007100d01405410540000090402005600c10a00640b100804801da000e03010400b80095000340c440707900954203000c508020740c01c0042c6844c403807007441d41c2d0181440c0c60700e84800c0c1107070091421800180240c03140510079a4900340b58100400d01030b0000d560712440c41c03c1a0b40030f141c01401000030803e0b1030316014003142c035aa20690071035a0307145403035a481d00444410315100b500803a0003981401084c04488003610310200403001d4400880b503540100380404840d80b02036a001c21104045002440208413000d541da00c0b0f5070b480500070b4405480c06c41d01044881c00d0078400002c560483c000c1503410300515610038903141e8401c1a0340381c0c0f0341c43d04040e512800e654001c1c510001344520394800c00185040e00c00e1040e070710007aa0141c11981031440350311700600030b03150ba401804103160802c0b01031285880c1218800411001c04802001c0711744600c0340840c1c9045111104d07541042e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 759152805 1250 759151555 759151559
    0x21c0206120601200a15112205030106270209030a08130509010e07030e0102030907030f050c0423060409020904030309050c150a0801081b0904140109030c02030f06091b0a 75
    0x5460308031a84030301e031080701a00681041d446c2c10021840e65403030115000d0f01d001c00070322012034603000700c0b40740440b0790381d80c0d128080034500d003040140000c3e003003d505035081080000b01c0d41c000746000901c165242c5c0061140110110b45642240519400303181e056003c8440480824000b10050220510080cc0c0841d13103900c5e400814060300b800e9021a1007403014004008940c3d80c548101070031110382a0095141d0b0030070f601004e80c0d4010074017010f0642c400100301e08040042c01c210151b00e003480a0014070118400c41a628000181e9100d03441c1c4180e1030100041d0540342c203200d082d83c1c0a50062503a401130f11192030480c01407440c1c1004035014490320324504125030300c54108403000101e44014a80d40d402041c0020801c9006030300208550f401180210301901e0110340e100d04810094480503a01e41c1c41303040841c071940d507a82d8212901e501c1c042003001031580c807412556200c0d000703500711480070842d041c0b6540e0751281141c041009810081018406400740c6200700c0c030942c4003d02801d056a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 759154055 1250 759152805 759152837
    0xa081b030d0903260405120c03041e0f152312042a08031b100606030533100c0501020318120301150e010c060e0604021c0206120601 58
    0x400410b01940850744c200c21141c100c010002542c03002214410721005941040e6a61694a107640441d410003c0c00224a09007030710010420750340100300340d500c0c2c01082010141f0400406583c0c1c013031440f6500344003078003207400d4030703034841095010165641c2c0300780b1100c0e2a50510541d800349030034460f00e25030400a203400d511500003003d01987c0208207a00fa40c41d4210307090211417a24a1304520ba40020102c00c10103c2c034044292010400e89440310442c4e0305d06203401d01d040c00064600148200d1520030b0208401e4bd040e804140705001c0001d0118030141c644212484808280007010f103c0e1000740740b6001c490a02e60340c0030440d40385904210700e4030025603480368217a800460381c40120110700c2c1200c20409600b0003a461803601101c0b60707685154144a040380b1285c0e02c80c03240d40103001104608000d07a9100b480290082ca0300703c3c1c800c12841d501400c142c0d8980000b43c4007a4407614501e40d00010407101101c124030341c01c0e8002d24181c986110741441d45e495000040806e81072004240b00c0b01114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 759155305 1250 759154055 759154061
    0x6020705010c270506030a150302060409050907090b030a061a130b0301200a03051e04060203060a05011d04052d040302100b0d02010503040c0305101d0a081b030d 71
    0x10002601c0380d9083c00d420075030038001c25421184164440c241c41c502002a600c621003261f07003280101d003000c40c110010540e036544941c0300340d000039003100700014009901c6840782d020902030704d400c8007036403c0300790707035540c1a0f080d501c2003807201e80e01d900018490070004007240d00c8001c80d00c0519a49000c00382c0e03210300040014000c500c202000c0341d243c2d4501130180c0360a100301c15040c010120b055650500c001d443c40800d0007001040d001341907844000c81c0d40c0801030340007c03885007c1c0b4884013089142a00e45003000e034006959450040c2403000303021900e0742c014080c1990134107061003580140e149031010040a4503025000c4940300710040e180d051800c03500d1841d0300220580c0320107280d140c00d03d07250003850031501940c4e03450414940070140ea00c07a81c400d0803000509809203801a1070b03071101d04201d020b51606610062061040892000c3d0215560704200300000300c007a44401102000c103c115120790103610002c108501c2000010000360f0604469440703803a0440489041005605e500030031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 759156555 1250 759155305 759155321
    0xe060909190e0f01061211090a060801020a0507060e0d12020a0509100f080a06030f03030b012006101706010909030c0503030708010938030309041503060e0304080705010c0602070501 80
    0x9500030b076003042c40702d41007401804000c014400c0704a100801b2501c0f1014540d1001c040e15109110784000305800c1000d58001c54013812984000f1982d030a800340c406042035005081c01c4420a06041042c9900b20010036980c140c0461070b201d03900300302612044100254801c80600c000c0c49400d01c00c1c1d0540d62203100c0011b9030301d20180c980e004169600c00003c0d024440092000303650508045051000461242d2495101c0f0b03807600300070440010050041e18002c0c214142c07031b0f5403080c054400c1d0030b0f1020b0000300c0314000e843c601c0031920705a440f203000014483c0080011200d580c420310041128405070b91149080340d00904c0d00380381c0f00c0003075a07946056520a40311100043d20440044c44440080d2107030000c03111402d801c6d02280c0103404c0c0c015a0707141e0340007412005258114162440c5d03803024022106001c0b070007041000201a0355042c044648021b010a42e401c52810500c002413405c00030403281520b411000131700c11589481d0046802e001d5400045500580a0010b00000f41c0309020f4514 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 759157805 1250 759156555 759156581
    0x2010f1809050a0b0901080c040b061b071a0f04030f020a0f080303070801060516020f010302160f1415040b07031d06060f04050606070b180d0513060e06090919 70
    0xd002d08225030540c0c2a01d00d024042d900c0717001064010040c4540014250302d0004007504d000c1115200d01002880b18090141c1c50703407040c441c500030031031000000701c1c4000c01c0d80d4900e989080068401c155141c6240210310495030350f032104000178008100a034030072441c1c0300c3c07004103050302c0705440e031150b5404420b441c0d03ca903030705900c0481480300300c54212840740d01604007450024200440d0148000c981910508081d001c0c8402d00f03109002c59120b030301203519440b85403e0841c5035054521f01b0010b16002141c01f55040282c142240c00441e1000c2002d001300f8650700c0002c912511036442e10301080f02c0c060995003d05a03150941c1103008040a088032804152402030002841c00f2014445008103c541640c82246003004114099943c441034800007500030740c030403603982d88240d40000c40301810b11002c080703031054549080160394440003e100c1107260301090300d4469a07410080e202c6a0705140b480c0d50100062000c1041810301c3c0d1303001c1d41c2c00800e1944076048000c82c9030010003100c0c4029000c030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 759159055 1250 759157805 759157811
    0xb09070f031e060222051c0b0603010e03040f06030605040209210a1e0308130b2a040e07090905090a030f02010b040e061e01050d1e0602160b010e04030c02010f1809 72
    0x11815030017000008000740b0056480d030343c416030b180c2982c102009181d44007c0100031f50b84007198054a095000c40c0d64240158100c9965903190448000c5180a5104500010b800e2a00105241c205070080d24400580900020004103c194812800d0340740e001c8c040b462842403492000124420400501c03d81400d44c00b1103d564425080003030201100510040420303202022403000500c440050681c009138a003c402440c1068a50341c00d040040824121201d107408a0003103001c5c2c0814a04070b004030800e45401c1d5510740e60340c0040060342c8044440c4003450b08082c14100109015013600c1080b4a081e1000241d40301c400c0002404503000c03645000b10340e5224908105002e01c1c115600d458411a90010384050740c9450000b0b0000743da01d59005000721402c1c00303102d03079246400154808840d400310707043d0f449580b0060328001181c0c407404260f5a1022510000a0034048109a1401290182c0e07504809102e83e170010340705542240d00b0a810000c3d0785250030661150403002402a061100c004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 759160305 1250 759159055 759159097
    0x150714130608090f0721200102010621060902220b010e0102010207172808060a09060e0a0506030309030f0109060c181203020c040501080a0b09070f031e0602 69
    0x10710b01c1500400790445507128201e8291130a0001810304211343c442e24048041056031070000c16151844c40c8020700210a05400403040d10701d03c511256648020390081002907502c4031500c02c2d003661544800700b141c002d040c03000081340c0641c103d0a40a80050040300001810301c21040400c0303030100213055181d40d01c044682030f6680c09645aa030100c024802582016510741340c082171f1074000420207450010010f9040002c8281c0159100c140c40c078581c43c88030041407904051300d5020100d4010340709440c5404081210b20843c1308000c242c945901c90f982884d03881d0b841d90301c0140006490345070302d484180301d121905d03070702004900c00c6001020300204040c40d061070400182e0302d8005c103250602001711808241c040318014002c046030300c869080504034403181826824160300340c200c5500a0300b46400410f403490000303220404188213280c1d81500f030b604d04c904c1c661180e40707e010341e81d01441c1480b000c1010900c241e041c0c0000000100c1c8070440d20351960340780da007280c1c421230300c44012440c5622a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 759161555 1250 759160305 759160307
    0x4090c080105090c09010510030f0b03160609050d12031a1003020d0f14070c06061a03040510140a0b151b1504030806120a0f03021b040b031507141306 66
    0x840203c139400380c1c0c0d0302030b0315410400060007007040c17241e11030201951000d00100704801d40d00050714485014003603494001c514074012810410902400010034450f9000044504240340f20312840780d041214074140c1c0c441c14604901a02101d08a2003c1c108110890940c903640d504040c03030000484c4e10700680d1203402020000648a0500006d8051494000769180b54648403016980c46211f41c540400c0c061014940300000b0241a0008080c81d403805d030b414058500020021350103180100c0c115110508201516000d91750040b041c0c0200000f40d0000c6100c2e0f44036504504900423000f03000b491000454911014260819130007400c1c0c00c80c410034447c1c024081880700c4c4101007210000f0304c050381b91684001d4171001c2c002e04903900600f0000115881c40c50140201001a075010120320309a60480c14001c0d038550720141c2a4101c2c0c110044913103071519161062a90100015000d006800f2244001c042030180040140d010b001400541c011111080e0300285840903082d044080300780d0034040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 759162805 1250 759161555 759161563
    0xc030c02070506180423040803180316020928090204060b0c1902040204080d020c01080106020a02150a0512040606031104052406040b0a0908120412030e04090c08010509 74
    0x800b05001d45002c2145903900550140c80300700881064401241c000d0300c00344021403020508285861814119051004000700c0b40011401026210507540b0249401a64207840e48206100d40c0780984000e41e5007001420f017409856404400440d20891140c0310045028040d41c000c540300714107654581480046262070b01c0341030007408550501d04d007030400c1c1042c090f130b40d0203119100882c0d10502e205040115a1590101c501504c0e00c481520720320000d81130080c0d59010805101c03802b04040c0f00004c10004d10001d24000390540041c00390f6032103020076619030000d40c025028201000401c0002800503801240f80d5070199121341c0c40050030314a90b04100701d0382041e009019118034200418441d960002141446000a480c82180d01d1f01000b02d001680034442e5074486010b4071408101b94502941013081001215955403d840208040c218071410504c102d016040190110b1111400868403814600882003c0640700084950b13031600c90300103200e52640081120b1b0745034070030010086d40c140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 759164055 1250 759162805 759162809
    0xf1d18100519021e070c0b0a050d0e010b030703020613080a030c120203030c09130b040501090f0b060703080c0d06120f05010c0207060e1306050a0f060813050601031709040c030c0207 80
    0x42d20840c100070360740c0c03690308008000c0300f0558001540402e942d4280078040030520300502e01455120340d511098403019050f0f070410312240183c00d07d00074034266080018080c0204244009014003803441c296800c01825400046600701421828140450101000c001d1482801d01030745607618010210301e040310103a0719284c140c00c2190001d00034415500190010748036600800c694040b108180b0300b20034002006044280742d132040c2801c00000c7c1101c2e01e5800107010308070f00301c41404104e158030140041c6200d02400280050488400100703d40c41810150003d0000721102160003580d0b4101c514080e030007030304159580043c80a406081280c248507950000e01c890012308001440c140d805800e40d11440390b41400360268880c01c104a03900c80d4451000b0b40710007403500031404c1d10f81c8042d0710302c0c0403103001c1c075004140d461001c5400b0360311a03000d024106510030010f0209a00b159101140245240c2d1103410700801800b00005580c1c46000e072003c0001503a4001401c510303080c40081c501b152903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 759165305 1250 759164055 759164101
    0xc12050a050d0e220912080601030b0f0a05010806030a330507080403030c111903030b010203030408090d0c1701050601030b061204060e03040807060302090a0f1d181005 74
    0x6182010f4032a100d0040321145010302d500c0f0300100e070f010303210483d02074003400100400300001090320076200c9800c0303860f04d801104c080c0d03410400003582c0424400030103101d032a26a40300350007110401407503104524040d0300001c060141c3d945005107964003031018041701c50b6400da84900d18014100360751044861009003031111400e00044c240f40703070040c0960802902c05810180c42d8041d19001501480410340010713050421524422a0040d100074a01c803600c0b81140040c3c2020301c07105082d03200100b40c0340640d411204503031502c2c0c01c0400300040c0521103141214008001840010705003414a4480400089003002013020700d003030710005040301c26a03844248100c00a000f022050801901e0390340e8001d80c8020009810f038041e12080c0d1960146500c000e4080c030900c50041481d44d0f040d0007621110406480c1c142901e605d07840540040c000c28022402d41201420942400c2c40c4840012904003100302c0c11608084460300b515801d000300424101d0390030307441300148060b504c0c401032189101410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 759166555 1250 759165305 759165317
    0x1806091704050f12031b1510050a06030902010201110a03020702041401080d05030406060b0301080307140d0507030c1b092304050717100203240d110d0c12050a050d 72
    0x4241c00030f0020300020701218003038200c43c903466145031401c000300c40d900d0901c9017410241c00e00c8070050940e245003504c0d02c0000c2c842690b005c14202803003c00c034101500c0b0001e00c0d40c581d0314200300f0114020054501c060741159258081c0c0c004400684008103410400b558016907120414010301003525240380f4031442d01ca0107a4010010102c0c04204940190303400d00d0125940d44450414101400c0d01ea0081e0f0a1640000000100c07e140003004080c400d2181000d01c00c00341e2468004bc0d11203540d20150408140c0800821001134440e90a520103103219400c440400c8404141e011707038014540d0810700c1e0b0f42c1d80c0c031085003845454504040741c0321110381c101030015162658490341c03540c003244603600e821034401a4070380c2203c0d0305011b080c060308604c00d4119100e142c2840010074010200403001640031000c9811140c1381498030703001c18a035410540441d100001e1806002440000110a03103c00c7c040031008070b00387c440703420030f001000d000d4401444003410300d0074002c0c18020750105540078400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 759167805 1250 759166555 759166559
    0x2010e031614040204030b09010e070603060510120f050108030417030421020a1701050a180c14011101110c2a0904110301021332090702011806091704 66
    0x101d814240c1d056584018403002c448540d01d01040181c000c9410003090110043c0c200a0701c00415840010101d13901d02c00c6414035540d69406400f10340c110300540c0d8020044a540d05201d6000f840000700039800480d00040c03205000844c40308940081c0c1011110380c01c0000c00f081121000a400f400104807030019510389890586074602880c880103510305403010b1850840290745d19414490014800c9009106d00a8a014021402444200e602442240c600482004071502c104e80340d194055204440301c00315801c015540c10103003c02c941c40c1f410003107503900f0514000003e000348111481c50700f01d05a207500e5440d08090070a030148207001a544143c00c140c200c1000154104440018103072101d001d946c03190304281c044a410380c0d5150750550300014884c0c2e803075941e00c0a410b017240c10003032407260f40108070001c01c070382c10b1711445e031030703214034210011a4283c0c7c504907800315041140390000103031801c44c1c0300429600c444001400e41ea15580c0f00e00300303014040c02a04245401c010304c091107181c0f80c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 759169055 1250 759167805 759167833
    0x280210090611030c1b011704081e0405180603010e0d08180d0c0b04080d391d06041a0c06090a0308010306050615180102012403170d061202010e03 64
    0x690f031010700e00c007660041085c541e190b40078045102d03070001409041b400925040c00c2980095124482880310f01c00c44240c00c041106486054800f03648008040b084078228081000302c8801010b4815549035517181700891706084100700307040070361915444040d26454142ca051030b80818000d400d04250300070403d9403014540c404071f80e140b5182d202c04518020303226030030300c141c40c0c2c0504c070500c4031428a03241c2040c060261001aa06203030780030010300c5080301030fa0718400501c0d21a907080c44000c242e040e000300040c5010701614900400010300400c6c20541d943e00e004002261302000402c0344c440000c0d21034400c04050001c0c65004409a0051202c1e6540b50350045c2032240c14880607041035591000b08085540d950b002440741001c00c000d06840d04610b0b0100a0303102c840f20034080c090740ca40f040c000b035901c4800603a231080f00c2d000e5000450251a60b00c584100071072801e80d0b0103034003000308200c00a50500784203800242110a6622450040078800500707441c021551035882a44030088882c294 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 759170305 1250 759169055 759169063
    0x102060603070e0f19050a0204180902092a0f0c060f07210216030207080d0c0507060e0d120224090d18170114060d05280210090611030c 60
    0x2200c010409045035450401e01c5c400c0070801103d4000342406c2000340006046075401903c2503440442c103000150041c48560000c0f1140e103180290410790703590000d0210681d400150b16003150307600c01e480d00c1c0815280382680c941e014aa01d4120703500003047d0210003d2080000c50b502100768852191182003019025010035210980c656540031105800e00c20440a601602c51006110744e081604030002c0c80c0c042d445445500a4001501c661944c14240910a52582918640090203800c5850400b40100c540207c44000e00b9001400240b171800010203150482cac00c0c00d01c6036400f80410003061242c561550108944c0f1614025102090011b1918046802e107410115402c0c0f0006041d00000304403071b0b02070185d1104000032482e0300e61500c03100040d00003001043e02c501d0310340e096031b892008224883d00c10400180c82c99000707801c0c04c01c00303103d054495880b42c580d01407020307155001a17000400f0b264800d81900e00080e4612020400306410110851403d2000f170051404c181442c800c465032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 759171555 1250 759170305 759170311
    0x21c090528020f0a0e09010507021b130911120f010b04020a0e01030b01140c061602010603030804081e0301142b110d0804121502040b04060c060605030f0c0102060603070e 75
    0x1060070080c1d00c20306142d0392100c004009140d401c185c00100d1602c110040c2c001c04040794810050b000d110040784510140c0040f2981680300200f40340c003c140c009160b24010010b5000c12071340d044c0fa4000f00e1109603074160b00e40062a076090000c14440b40039442e81d5013500e110104e110302880c01030003500d014070f81001c010400c00c0c00070318ac0080c0560b101c00c0101d0f55180b07407901802c1d031480001503941d43d018020500e1803003010300041010360303c4c420820480c01c90340580b0025000454100200e800190400001d0020718460b80500450900020300045550701c2a40000900001803081d1a113500349411036404031601051616903048610ba0042d0b0481c100c0c0704000c000800d10440e000443d500d4500d450a00b9400002c01600c2daa240d8402600344814104142c036242d20300301c0801705824403070003102c007a141d50100c01c0c0d00305481c103a0103035403a041c00b840071540d0070b40751280030450761010000d520000142400628914841b100007a04008001c0c0000d4002d403c403840c24400418480324042e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 759172661 1106 759171555 759171559
    0x1305011103010b120c0c123a020c031204060605090a0504210c02030a0309091104080d0513080a11040e0f0d12021c09052802 55
    0xc618003007486410420203007001030040c260380c00c48045401c04c3c039000d081030810001c0b203209400c054403019032100d80c04010440000303050928054000100801d1080f110409200c29191228155200030301080c0b6000100041c00304410002c4807114400c0c1814009076040610303000000d4001031148510500340903002c0340c0001c50501c5902c2c011640105100c00d59803802c2c03034030711400e65010f80c01d6080c013450080040160f1001c0c0f1007055814427940e80d003001e00b820842c411089810144195944080611041c030908100103044181902141007003a111b50300943d510060884a400035a228016699003c0c00c2041c0000b14880701d00703048a0a1043e500040c031020380e2a0100d11503a00241d2003015001e10a80c041c002c0181c1e080c002d28400351402c2c000c0882030450718851259020165500c00d0f1007400d222082c0015000e4503070300c880002030070440134405505000d4600f0064 = true := by decide +kernel

theorem cover : BRFrame.Cov 758992805 759172661 := by
  have h0 := BRFrame.cov_init 758992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 758992805 ≤ n) (h2 : n < 759172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
