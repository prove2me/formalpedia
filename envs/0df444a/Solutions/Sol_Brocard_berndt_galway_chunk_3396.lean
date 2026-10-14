-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3396
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:33:05.407068+00:00
-- url     : https://prove2.me/submissions/bb2997d9-7b28-4413-ac77-2fbc80c87cd5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 610611510 ≤ n < 610791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 610612760 1250 610611510 610611523
    0x406060e01021510080703030e041805030412020d060204030506061315140a0b030108030714210d0902120f06310507211b0f050411070605090f060702 66
    0xd600603030002400300d400e0040781c0100c0da041480300d85084400350312a00440d041120507041076000c0303044016400243e040030300c0303540a00092801c9204504503240d543c55101d1187d0300c2205a02d042c5c03850307401c0655442c0d882040d00503500080455a8a551f032428a445640482c0d64505c1a103040ca022030f80140c1d00e0044404600440107072081c818140900c10840c0c144144000d5004401c1080c045110a41c1e0300c02140030300310210045448841900e01203441e03032800465080702d074104100c800d0b20001c4441c0314616500f610314a45407582c0e108a00c00c0010b118840010354811111100c021140c407020685140c40f4070200241c61003680c5a0900414491a15944c94513849044c10101611201200e540e4900d900c107005031114036075102140d20041c08010110410002c4040043c800c2015170004044806000110200001e01d00304007140709035504d1044c2801103846d2a040741c10010074070b084450740c4e03601810411403800c0611605035240414500117250f8130412011903192400051403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 610614010 1250 610612760 610612787
    0x504062408011824080a0512191b020301060e010609050a15080613050132010e22090b0f011a030705091503040f0b0610050414240405040606 62
    0x1583c1002001c000d558010201c2c0250355000001c285112000c101030007003100000c2c0320400042c003001d0142d040c503038208900100c16034810401002141440703110008002c40e65051410aa5000030814603854071002c9440030007503065191820220b107100b030303142040d4140c0303030a030361124102c0da11030040c810700610300c0c00790070381540c034481e009110148200350499100c41d0150004201002e0907120300d00f500e80a03008144262080340203070040c8402100305182a030000c55401c040c0c0100c0700000390841080350080b40c020304005c0c409000c014100141c040c0901e0f000e00040200f100d007810803081e5550240d9248400a8100d4000150346212801030010504200009440d54442420556a5a20401040f0381042010004440c00000100030b03500c0b4034064002e8849070501d920308481c0303040300100300911460308040d4521030161711030191415940a06032040d400c17445400013403059141c2004030412000041c41d5500c91104020180c82204c2083e28144141c81e19248107840d604113a112 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 610615260 1250 610614010 610614029
    0x51501170304141503010609140604030f03080a1d060a0b01020102070503030a09050a02060c0a05010605032d070f060c03080f0408030c03482a07050406240801 70
    0x20600100e040c0801c500c5603000e0040005040d481d110f02410a13680007644070b0f5000c1040b0401c200200ba03040b00b5400c203140c01c211105440c060850b91400b080700f203200e030007400304082c0e4000501560b5040d030150100f8410a1540580c00c82a010103542d00da10803100013006504001a00509500500a40e03044c25848006541140d60b020759a0300202240032064580d44101460000541c4490b4010103000340c107138000d0301c179811507030520710709407000c6500250080d407103007214400c1003462806401e003102481d807028190394035000c56145000f05a030409024109001000507183d504429600c001e0303403013500c1d82d0045030340320035503e81000c80443d400303400c14030100002100481c001c0021584056400e440041442c0304c8146412401c400701d44000070700c13079000014851701c107821f50b1544000c10180007140c0b821001d4400b1180366500e0708240001c3c030b50b910003910a611014081c1602422019004200442d680c654045202c2c03040404042009082e4905190042c400c3d0002c42c1640c440f8107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 610616510 1250 610615260 610615267
    0x806010b0304030909090c0e0f0601050927010e0108070b030606031302180106210603050a02041d034b030a1508030c0105091b0409031101090515011703 67
    0x208040100d07403000300114104500e032903010607480110310841841c94085c0a01c64052070609190031110030f03028121881d1443c0040c02c201c940d2307a01600700d13001d00906561080300e00543c441c0c640112004101c1c1200c02101c54000445c01401c40071a0a0403528864211080c00307643d125a0b54061005441264000d0420030000300240c20354030110000d00d102034020070b2600e03485030700d56410b400c0c00c1c6c202c1d000060030030814141000d40511415040d0810280c100102855603460507035819150070000e0096071965030151904c2c24188114040c801d0303507001d0701c0c0e9a680b4480038410b0503d01c801c02030a0140000c0c401c42e4003189008117071814540c0385035022200e4040f01d000d40f44941004010407104e40d00c42215082c2e00714204601002494610019511002c0003c126800d480d401404c01641d64401000d0400c0040003080c18020104107640000c2c6a01950034221f800b20380d0000b8070510303507092540074800c00000003030407144541981002520383c0d0702e0704204941881004061100d950051 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 610617760 1250 610616510 610616519
    0x80703030c021201050a05010602070602030c070e0a020c0a0b060a1a2704020a030204030b0106030504210203160f141204031e29070c0c03080307023d06080601 70
    0x41c0c49401c03400740010030700c4030035000102c1c4440c29640c0844d0b04944080d01c41e130041111640402c00320024100600145003000c0b0512003582e992400c0e440341103480c0c200040443d40ca00300990403245600c000d90240c3d10341448600301114500c4040c0e03411400307058003100028040060036031124403482a416003070701d013102c00601c006440c80c6491121031551140400641c40d607841d403004022114141d2000750f15a8a141000e590841050380883d003450f060108009c0050740710342e50310036850340941b00c8189100014404a00d103000e8000c0c010bd07142d84c0c90861005100110142113982845224060308615a00c903110362030f00c6071603102901d00001404240009849140001240400074005400d00c8200340c90b61a403480301220000c6148014510300420815003c2507290300108500f40b072142c410080d0364081d807c00042c480034251603808004101c075a4400e1144081c1c03010810707101208481d090b1800120000f00010300712100b0b216840d204a101c046004c0d000403111240080c14590303191 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 610619010 1250 610617760 610617767
    0x10501061704020f0418021908071e0b1c050618060f240c0714060d051306050108030901020106051c0f0c030b0a06092403060b01030908070b0702150108070303 70
    0xb074800c0364408a072441000943d2550b01c45d10102c8000312035452076070a420300503c0141540409801c02003800c2d008240841d02d000140a811140700005010744005c201524200080803500100c0ca04580011081404080240b031001c401d07005c2042002680c44030700800c0700c50b8612040d42000d801850002440c00d14201c003449821010140c11802010340d15010441e10100301c61130740f04114000b24985407025410842d0300090300202d07400500c1aa624400601180580d0000c420304c2c0d611400080e14540c50805100d21041d4444000d00855848282e115281d41007490f03000d0066103002400a09454035100154029520182135a201400d80d1140f841d400c004600580304103000030030000c00a81100038407440b56002c5200010014288141201540e40c90580410801c200c3e440e207000444502e6401401c5950062000808041800042e0701500010401901017040803032900c0a00200407403445c41803409a00b0f54056201c0c1540d81454940d0a000d884800d80c480c00040c00048d02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 610620260 1250 610619010 610619057
    0x60203180f090c0d14040f050f060f0408030411120a020306130201050304081e03040503090114070b0f070e040603110306070306030f0f0213090303150f0602030a050717030c120901050106 82
    0x400107008640e8071100c4070117001d0484155400c4030384c04040100b1006214050041001c85600700021f0660742c10304045941049801520240505030000041403c00845200248103854003904c200c241002280d1102d032070f101d0040003a8001d0182000080313031505a1410040c009505840d454116212034643c85e426802c0042158203950440d490100480d10708800f0398401e03440340d0000c0d6507032210304000404040303a50203001c0c40da5500b4000380000514003c0790650000c28408000e1f481d0b0b56103241150003d91480700e440c0c22525002011042c000c0700c0c250905010b500ba13084840544411208400311400d5210207130440e200c0c041007200090030820b18030541030006107420300341c0312075000307960494400c1e134400c4000c0b9640e00c0c0910000304212403801c1c000c0c0b446002d0405d8091401002945911a40c1204000c0103170009004003000300501c0c588000007038040680e0780320f1428103018405948010020ba0b804003107800012b00640c01400b455050301d80c0d5580d1460405440748040c2c4d050720 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 610621510 1250 610620260 610620277
    0xc0f0c15020702031501080c0301020307050d2a02030706051614070302150f0a0506090c04090c0203040b18121f0b0d0f060506040f091703060d0804060203180f090c 72
    0x1d40800041d400f40c0e5080008400c0042842e00640c00b81d49898503a0340380508482096000341d006004220070a40c0100507103100c80002d6802003030010305440c60f4016801692241107840030100c0810400e1030b4004060301c400e51042d0b0701041070f41c407012102ca00b59140b030002400080e0091140d10101062007003d844500d1003801224200780100342030116001003243c26101188051080100e0741c44103015181d000f0400380c0702e110150074204078400b410700c241d01911400c0c0340c54055003214184200121002002d0701c000041d2030f15140c030180682d0803516881070313100394290301c04144940d40100d410071003c4484842904083c3c1c0b040c0101c009403a211400340d0380f01e402d41c0b090102107611101c0070f00308288070796030000707107442e040b000c0004a841d0341c2c141034600c500d0a0001c10010b0b058500c4900740c4800810520f0703e90740d0b9100080d03118140c001340100702e60380104001070226000005007200c0380201e180d403941b9105500a2141c4a00400101a8082c0c1c0040209144105039401050100b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 610622760 1250 610621510 610621553
    0x5060a050c0f0c0f0d021e0a0515070b010e13032f0f070f0803070b04140d0215071e0825210b0303040303050901020102160f0302010c0f0c 61
    0x201c1c160a031038148401c161400c64141c10034154411903207422a03500892201c00c0700c0c1c2200650340340d0046200d24101d240342a080c1c843d046070020450381c1d09801e0300c000f03110080c00180b0b5141708070a0600c040d002803000f11a490030b948004a05502058000f61041c0c1000c0030765842051181c03811110600b10243d007041055041c04810003035078641e14101d800f40f07800c40040008a50440c0090701c2e001540d4001c5a015117861402d2203410404030440f901d054100074041c1c801d440382d00b05101000c030641840c0700c41c0e108030740003080615000b01e40d1400300791001031403a40f6a0754110382a10f0031040d4003074929120f812003149001d03582c054000d45400039503c24144514100c022407040c07018a07000c12032000b269190030805d203400700748008090034903c08e4806100080810010960342e0080340802001c1c00070100b61b190f042c2e4401d5064405c80e00c9e02201051110f00107061000542144040980c019420030742580e40b4907004d41340b2000d90b06503954401c1001c0c040e030348614400960b910b4002c0c0700c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 610624010 1250 610622760 610622767
    0x60c030e150621032205010f030b0303160b070206090a0812100801060801140604020a1b060b1008010e07080601020d0c020a091d190f02130e120912010605060405060a05 74
    0x4001d0304903115040b10740c205004513501e10901d01d0b4641c42c0b000c010101440c0f0343d8212030030f02c607d90b48031814104091250a000c0b600c9505240080e045004103403581140d60b00d0241610140140a5034050090034035030259002d41d2500340e039040d2120890b02024020f40020012511103030f0b0071600e03041d44901642d280c406140c0e190a241400e45049030b109582c0d40c3e444800d40700a0260342d0390040d804c00b41c101c03001c503d030007900c0d0000f4201071545105004010916544181881070617044030f0398429004008405101507030710060310340d0030203005070134032011114002402c103802010001d0003a84160001c00707000014440846900442900c00c980054050500007600d540c01d0041d070307030901e90000211003809101c0c208503103411340311501720507858041808480401c8400440001040c0c050740c031011440e04c000d007504054805003e5224140c4617203450b2042c5182140c0191010410840d120f8580c0040136202c2800e07144240240e980c005000c100c00c000500d4242e000301660000d80c1452402c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 610625260 1250 610624010 610624039
    0x406140901030e0d0e151603030b011101180b0f060a0302040b030f07080c0907020303011401080c0f070606031424150d080903100e0309040c091809060c030e1506 71
    0x418000072040c1c8041418100c10701210b1400401c100c49185000b1b80d41c0c0e00b8400c030300e000e9684000515001070103150752031010549a0f4071900350b03414081c005400034021030b1407080003050008403501c1c2c25a001d505840101703003045207126000f4011140242040b00300e80c15074007040014414003001550612904603000c80524045c0310307900080c40a40040d242c2030079054180b0003880c800800820864204100505c074003600f0340c17400750700450286400f0400f944d03a01c4844034030f840713100095203000304085040810401160008002d491044a00398808034041408036a00c0130528601403070740c1d11403e4618140051102c402d075019102000f0171400581c60404505051203d07030302502c103c080014021080c1c2010007240b400e840001004120522031261034a03102d004903c80684210749610b4480305803445404184050040c4601c050315000210324904014503045100312030711400d0050364541c2c58040d104203c5509405005005180c0c42c5160403003d1690040c080c0d9413140905080a8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 610626510 1250 610625260 610625263
    0x6050a11091026061206040b0a0504050a020d08030610031a0105030a2304110118170a05010c02011a0306010f06111c0f0e09010810020d0e0f0706140406140901030e 72
    0x2001a1001181e10f0101d041110500c5220724030340e40a000590b216100340000502c1c0c4000180e40310005910006a5465528086041400c40701c03019521501c4da450103814048800021401494204d485100c003d080c00700a80c140e418610640b1041d01d091074200c090740d40100015030380490404000583c80031202c00c0105900302c4c4005440228450008010400c1006460715034000c109003080b06401c01c3c019601d80c00080f407405981c0c10307100b0004026091020400c04910010b5220000780085029200028020b15030029803c850000b80103110306d203420040b80041c113803500707203038094501c0b41030400c140e40c140304034200c5000307501c20441c0a9042d01034002c401c1d0042441944c1c1d808003c014110010625045050407a203d40c11500042017032080018412084c10f00b200d20158560045245500003040b64400800550060104108140201041141c243c41c05516940ca02501d944045601c0b4050fa0081c5000300b18441c0c001c200081071000a000c161070145000314140082c100200d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 610627760 1250 610626510 610626557
    0x22103010902090120030702030607230c0a0c0e22080a08060a0f03050a0b16200c031f0c3209041406040c0224130209070c06050a110910 60
    0x45c481034202080704400c6140600000fa04061585070452440c00180182e90f41d64021003441302500100007842c0c0e0800d04207001c440022034100c7e8a0007801ba9076001018031200003100c0c18011503400c010716842ca8080a120ba0800ca0780000005052980352002235600202c042c02d00d40e802003011800148011031401d08034044d41c8038001038a011070162810291144024004001c110000c05542a1555000c2441c010090202c007800c8a1aa9625001400c1108214000703406d4000c482c00011009100207c8401d03040e503070501042085819501142d18042042c01050a11291001c038514400e0940071410360907107842c3e0083c600001c2c075000800f01c0e4012518502141c19200030880769150038800c25104901c140090310000918a980d04510655040c5070100e510528000c00d1080005441201c83c8640c040d054100c3c60410139406080d0300300340202100c0c510300300700001e1007040d03050003a05030210000c818a4280715403001040017140c081c2403540100202082c1074001d40d01c40c403444 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 610629010 1250 610627760 610627817
    0x912030c0a080c012d090206090d0501140c0a21231006090b2d03012d05100c0317070509040b0306040305030609070918050105010221030109020901 65
    0x4240d07490602c0f40b080c42c00d56100030003519514044402503164956500d0f0550380480c404500025403100b40c0c40042c03558040c05803060f811610890a24041200560003044000e03d8003070171003a284d68201450503d8421141d80c000054080c0300350b0f118522540141000700f05012001190105460501c81100741600c49603405800b01003040c043c0d0b00703a01c200824042d00c080d10b003e400342810328030700c000f240c0b06281c9034451045c0c6410000401d000740120640b4880500b600c000e50342e5958620070350f00103c0c0d452440c1c1005140f90841a10185840c0d070302e600302c50011306610340b044081a015a0714850900080c1c00f40702d1020840840451340c0841a0300c00c0c0b4482d254a42c4a842100030700045505602e9001e0081d4000400c0c0008282c110701aa80c1c0640110707a03150083da50b040c81258580c1c0103500c881000d034002401000d45152540020781640c03001e900b100e54010380c810b1145210400000d41440c2e0160410051162340d040c0d40040c6001141811f0601e510710840300c40040c4480707100ca0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 610630260 1250 610629010 610629023
    0xc060304111201091e0606080105010e01180c0915020f0715030c090b0f3f160c060c020705060409050702010b090709060c06060b0d0501050a050409080912030c0a 71
    0x240440d1409401d45844440c00340002c001c660245d50320301540b00384000300c00310820300710311001d01042000c1c2c01100142071500020b1100356076500407581807150a01070a0001c0907907042d4401c1d400414030852300741d00003ea039280407041c0340485e210f42c0c20f684140040c0850107018038545000d081008030800800c8134106005a950741000002c080fa40405920f10401c2000001007213008808415074422880c2c0034002c0b5950110b81c1c3c00800030580d81c800b8040c00440b090008100c030548a46082c5402050360f40000b12a5180e070b021203d900000c4030f441c00801d0706140782d01c1c00b113400c81c0e000c03e14400f154012201841d03124000900070b0b400941c440c24246480c1c1303082144160b03080c00390b154510030a540000080c2003007100580005140d015000030001011074840506c80303990003610041480d01c00c903a650381c1510319070f100540400d01407030b07010f60300004000485090a100303828245130807034110784c1089490820412884240b68800005200600884600100a01001c00d4441c807460 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 610631510 1250 610630260 610630283
    0x70912030e031c080103020f030a0c12020f010804120c0512070602070c0906050a0e0a021204200307050a1e030206160b1b182e080f0402060a050a020c060304 69
    0x1402c15280110403050b070b02c40080042c0310400c00c1500311840a0550f6411036104000c50310140c0464680301c403120b0003900003180400001800001c0000d0780c0c107614025510310221613a0040151906076050380c0007840341d0700c44801c4041c00d030b22541c80d82c0007042c400c1c0c055980b10703105094400c0071508145001da0f601342e03001031a802002080040200140392036401402014a401c00281c216884c62040b18102e58520380010240303009903040711183e0400000b00b101506043c10100c12605080c0001c0d000800c82e04d940051500e4001500011a07100038207107802c2c20700b031800c0070810380002c02c100c90214012400100040e80d804000d007540314041001e0070388880711070500c0c403a03810028001e1420101d944a10240c01102002124031805c2659284940c86c0404030100b1108051140c4c0400c00704c8040750f8400c140c0c5608074100381000c90f0341d5140c9201d82c4500222904410b0f0944000303602010410440308410700500c00b52104c954070b401590300021000d030200301913903c2120225103c40f90305 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 610632760 1250 610631510 610631537
    0xc060c1805030f0703021c0c060c02180c04170708031b15060607060e0f0601030308070905120709110f0408060105010f0806011719021803060c18060307091203 70
    0x20510001010700310300819151120046050303c842d030a00020380610001c103280180a0105010b44401d9036000056401d001c2d500c050080240d282d50004a12541c0300c07078050000034400c447d0603030003082c5215449142c00e00d82440c1001c034140310300d01c0200900542800280e0240c0910180c448100c00302560303001c000003401c03600d0400000610120010103042d0074856140c44090035200b006901c030500007060ba0303c1c0c1158900d458401071003880d00c1e100350800801095031010b01c01c2d02030880c0342c59070641c0030b07200c004000460120510740e08050340800c1017040054115000751040c40420030810f4035100c0c51504003040f80d803068022540c07a0348464010082941d110484078903c80240c42c200100d0f0078104002044107560010b5401124401f801049060090407071001000801c0b040840d69000440d001690302c1c920850707010300c04d005090004d82c80a08010464001a00f01030039131458400140402c801600081c0002c000c00c200a040030991014060141c2800c0e402525801e0802548 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 610634010 1250 610632760 610632797
    0x60807050415060527041a03063108040e0103060213050f09061504080a152003071b0f1a060618010c02030f1501170303010b18010c060c 60
    0x5001c8050b030810301001d04100065101d0140d4004140c030302c1c03030b1145e5821a4584495000ca103e40d505901074502202d0040311a801c09047d442c4500903001d81d0502d580302c1c84107002c02009048141040018008105856807030910a046c0161241c0c140d075003410303220032aa5082090903003040360541c0c0d00146100150a1750321848000304011120324405503c0803020500160019064500448114404400303103d000c5055501410030141142c1360600c03035041c08072044031079440030a0030901d4985028656002510076002c80720b04a81c2c0c0324a0341d12490342c100c07101c1c4d855410491502011007442c40000b050080d498003654003c590111141021901e202202c642c0a4100c600c1894108585844e41e54000c0c48a542c000003400c01c0c2d04c204095001181c1403480d00c00241103180900c0780d0b800c00d082d1007031045a06880060455100c011841601c1c07658901c000c2c00380468012041c4070440394a115860390360f425140600d8208007052003555074a080c0e441959034900417404198065800c81103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 610635260 1250 610634010 610634021
    0x71a0108060a180f0212191a1501111501030303021809061011010204210506010b0702030627060123031f110f030a02090f10020714030f010608070504 66
    0x80302e6504100500c58948600c1c0c00a820030310040c00d480000101d007003550b4900b44007900111095055420b6080400243c0da0f1681c0e14000c203c4500f0020100d8202c0f80920206c80d600c10300d5032121440c69242c02c240107407150a000291070003c0d100c5c0c0a40c2c0084c403102010b00c54000e41c820b0b2005a110041c012071107240d00c840d000c40310300490001c0100204c9035581c0c00444c1584546e82006020b0380d40c403224080c064400e07504000d408801da042000b0704540d4460140180d203000c1c0043d0f5030107903210003641d4154800e480001c0c3d03041e400742000c60826840c0090300a098401c0c81c000b1404200c45194141c00d1400907444480c03c00c4200c42d01c0d101008001c6012420a8001c90150001080500118446d10000041604043d0303a440b42c0c001502c0040b8100d83c00005003458058591400c2c4c0e110001035408684001c0c000d030000b10314900281800c40104071b03200156001340030031a0810217030007a42c0e020010300c44e506121368810700e602078400f0721a100180c5022030103080c00a00b0170307050000f60784 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 610636510 1250 610635260 610635271
    0x5100903030f151e080f0f0c030304030c140a080f0a0b060609090426070501060602011a13050a2405240d11190503040605060306060d060b06071a010806 67
    0x2800c20070810001000e0070380f03080540e80203583c1005a5050250310318088207054000004602c070344103030341c03604240000d005011030250704211410300c1030600c2410744138021844010060071588000b440300b4003c0f03081503068640302038070014409070380d070440c0c40c6000d801000c088410f070031602010341407010b40c01100b640408165401460290031402051440c000103001a07c2c030400302c07211850500717143c10305070b000046041020361501d00505040b4001d001511070000035600c3e140314070000c440c1c00c072100300080c58010308050a40110030850809400000e1082c0046617a820b6195030238042c1e0414a051421240c072140e03151414001800700d0020460740052050138401c404080e000c1d8203100b1200d03184141000401e2280a080f003181d914050402d944010091203061068025444009184140d0040d1010301864071803000345a12140143d40b120340181d00b09410a000c15115004818404e00113050189040e0641e241c0620300701c05c2d80f001610040c1404010002840204103450700030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 610637760 1250 610636510 610636541
    0x501120b1602120714071707080d0c020609131d100b06041e180b0102012906070807080a0e12030a081b0705070e07110c2404030510090303 61
    0x141c2640000303566806001c0000d9a51000007500b0001c2201c3c810303061014081d81012183d465440e546e4200702c1e0035020a95445a104520000542180001c0d04000c0c00842c1c0e01d406003282c0c00340d002d01c4641d80c0003102d40354011403c06001450701810f48118402301c0010142d034111303d402da98070181440d2051415928660600141c0c806070364030b0004075004c075101c4990038601c003a4a60b0124002c0202079002000c211002c11003464001103681141020350400d07802045203c9144140914800f010010707048600a4600e40605506024004107015802185001d041c8109a5901c4200ba4822010720000540150710034810703040049401d0086164013015605002070104002d081324001040d6606007489403015030045a402c8044030550364121042c0e0350071585036038102800300001c0d20451300240c90350010f002014000700300c148038821300400032001d02b034041070421600c0e02400e2a844901408020010000c1d00801045101d0101c503039021030700c80c1060034060102c030b240384403602c0341c0e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 610639010 1250 610637760 610637791
    0x140604030b15010210050703060609080319050f1c020c01060b0708090103051e0f040b060411090603060a0b07030201090213090f030f02030c07141f091502100501120b 73
    0x6210101103a03006403400540910042420b004070300d080010b90409400d0341c900001d00000c180d254210350141d48880c1c40c1d454065a4440c1025640e1040c41510168408010b01c03140c50f043c8200000c0a00302c011080c0e1710b00700620502125526484000500081c0d1360000754148400707002e000f944010030f0054115070031701c00c0948802299220b4075036220304141d56907000480d40d808062541c4903050300b075860032885103001027001f049a034048d00c3c00e4501c6204000015082d24050003040c41003100c100c406828001c05d4003e20005800c00341203960720010110001c1903c03130000c4064401d8902960011521a03103034014000380d000c080039440c80700c5052a003d8808924400003402d1725981c1803400c0030f004d00550500703c2c154019010300040720b0050410029002e10300d280b4602200900302c42030200b40c0d1070f0800c000411414001c5040200314804002c001d440780d070b00c55005c0780d401c19005031844500084904400c0310000d0304054055612207240905104a00750140d610001c1d20383d01171074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 610640260 1250 610639010 610639013
    0x609050c070c060f050f120a321924060504140906010e0316030209090c100c14060a0504050c040b06040b07060207061a190b070b180a060614060403 65
    0x4503440207010320401d0240e03c20028507158413540c22a88600c1b0b240d1a00d640315600e026400d0b0340700805135134160f030701d80c00d22480c004d0000203140702851091502c03480d002030b40380d2522226003a100040015880201100580ea002c0d13201d80604e403600142c4002e540d400140d0044420714104140d04070700f0801071b05020030b200501c0e0201d01d91046182c200c818080c90342e1401c2c0120340e03032030b45414001c1c0c050040c03013038980c11070042d5120082900c1c8212070902e8141d407180748169860094082c0c1c00e9100700400380051041e80100c86801400d030040d04051003503215004640c1c9049000d8a07011a8160344904000c1070003424084100c800f0b5040b28203120515a01000a28134083e85c082c40716900c000280d40410818941c0c103c900f4584e011400b800f410054a03840c0c8208515084018000c220007201400781c141742c80c440303105403001a0903481c14518035840d07602c04420018400c14030300f500000d191220320402c00c148100c1500c9130700041440380c100801c801541040c00b2160340190301c01d100a20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 610641510 1250 610640260 610640273
    0x2a030c0a08150321070c0603020c0709021215010c0b15210d052505060a0e0d1715030109050c03010c0e01080a090501061d06040b12030307080601210609050c07 70
    0x100801ca03461a40391a07059024813801d1182200c010001e100c5078800280d002d0301a000b904918a49106035a085a03403102040c099100380e1001d00000d50654000a809041d5150f1000b0803a4040c5000d00c400c0c200d0359540001e40d007083c1c47c00304080d020090079044074034281e002c9007103070705c0c880b204140281c0010f040d450350340600e480c8003000e00c900425000c4402e0115a005d000b45042114030358207480c003a08015450740d40907030300280782c18200b009460045200090090344855640d4408009512400b410244420040c20130044410403284500d640d590034010b44484601641c00340ca03400581900305800c584420300d00509000e03030345102c41d803640c1e00210140d034807160407040400c2d4030038070780760003030040c025078003c110b620346020348104440c0310048440e80b191900b5201002200d02c403400304014403501c1411480994000c00001e000c0510486685030402e0301814500d074040c102d80341c14007103421002c4c1e80c2c46516984034010480b070b01850080d180c126602d86011031502000740c5410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 610642760 1250 610641510 610641523
    0x206270f0f2809020408010b030a050a030c03030f020c030a02010e0d0f0c061d0d0f05030f0628080f0c040b0120030d0504030c05100605092a030c0a081503 68
    0x80d02c01c50008110160610244845030440c03422150340050707203034868864200075041809451000c1d803810840c002d050400146a04e00719400400428142030250340032151000820741c21810991100031320044001c160014001805034000559103400640c6402421580280b9209505500916214400743e070032503c1d96407002d00d00c0c5403805821096041000161007003040c0c1c0307044440c03101c2d424211444003251512800d02c603076a40c10801c501c86601140c0c517010035200a4258065100800c0040c44c1003001c0044030850280800c1e821031098480180002c20782e4821580381c0c020301c200013403081c4140720034000030b907003100e04102c0c0b41c0c4c56100080c41080550554101d91000703484c2003075030320410030035104d42c84040582440b0300c8c5400c0c9001440300b00c03141c408481c03603c101100305031810194000c0d0026114050490a01955100a005101424403460100507803085030f51a00340c2c480d2030300a621490a9403400e56071101d9034103004000c880028100031141212101c060f08955010518 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 610644010 1250 610642760 610642789
    0x3010c1d040c1701030b010612271506080102130506130909031b2105310e0a021207020607080a020d0b060304051c0201020a17090a0206270f 62
    0x8410680850596091510355100e500c40b40540e0f0001041112020000b81601c0c182d85d544400495900301e424160f4110404890403092400440b00c00507440306115113219018180e40410015155560811140c141c3c200c61f8107a50001007200d032480c8410900402040103840d15450403000f000041e42000c0c0c0c5016000c80303ea03c880c0c2003c241813040c3c3c0c400c0500c40002c1c50003a0448801d04e4040c594661103c00c42c655020382d80d4052a40b14014415201d80c1c26002c0360b4071603509220018004014000d05451044000111002c00e0400410360468401c4000d00c00c0141e50300441e0300f004810200084c24801103501000401c140190b0041035160070240980b405a02e50609080c0c0001520601c0103032a001720022003004148040043c1c00e10240100b00c041d1451000320391b070100d00f0303482207442c00d03c04034822100080460344600d5035950300400c0481500c41d00c0f075055000032400c1d40320018400402035012240407916440d5451840e400703a0440700c24092602d460080b403099004000c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 610645260 1250 610644010 610644019
    0x1b180604060b030c0711040e060f0405160e1b040b041a0d09110405010807080c061305030304031a01060e01080a090c030203030d0e01063503040b0406050903010c1d 72
    0x10900a485980048020344111802d6645a20308050070901e2500810000d541c690001803808101d41440c0c440c0c0c00d24481200c0191401d603451400c031030b17201e420103032045580d441402c000c000603100040c40000900610b007490207060610a080d08404c05c0c0201d80c103040c0c2401044108000521803044508070b07203203800c0c085a802c00a140000141c02890070445000e4200b0201e10304212408295040c5a6011101040703140d881e1039286d0f035500303440e00035403c15500000c9540a40d140002c007500742c09a4001100802c1c80d00c990100382540c00c1903100700c1c2c10000c41002c42041507030055645000d0700c014034001c644040080c00082c2411006018403024039a0340c4c5010080c42280b48041001e50b0f00501220b940e2440c1c00030303540c02030541c000d2180081d442d08101140301d14860041c541048400120341401c518841c1810340c40d05141148551a1307c8100f00000d00c039041131014000900f540e4079210380b00c1c88440181400e55451141c200100000c20013021051884280300400d1040d00f900c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 610646510 1250 610645260 610645309
    0x20d021e1f0b090106030501031505011505092407020315090a02120c19080705040203160e030712050601030308070305072c0a0b18030a0803040609020f04020a111b 72
    0x51007140240b40320b044880d00001200008580c07560103402150407030344100300c8074841c4620240d41c80225507081c000c111100e85664410322459200b1805000c0d04000207141c45d09088401c60307109400041c00551002114003c141c60041d407400748100441156114001c01d001d183c00b107600c079141d403180200240300e000350b03c0509020400c2008500146c080c05003020079658443c5c10b601d00c00300c4451191260f1072042407001324081c00c25000741d0b40900340944e48801603052040054440d98040300f11a0f405200d559400a03000c51000441e00300c19003c0c40c081c1c5170030b5041d82001820b14034020f041d00e081c582000103010140380d22400d0060f10091110383d03200b01c2c407a113604140286aa1408565004160380070104e00280d000006100045c00c00510010000d00d040506443ea800740350050b08112007480000d0101d00550010381e5511710081c801c2031b059480c070001070103d030006101d00000030500410480e0410080140c1074004a01000c0c0d0500e0181c0140028038000703d203135503880c983e960314 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 610647760 1250 610646510 610646563
    0x906010312170f10081b1f0203090f030c090a1e050421050906040803130f060c1401020d0203130308010602120403061802030f030a080109020f0a08040512030106020d021e 75
    0x119895024190b05025030b00c9400c44162406c84c2d418200803103038811038a40d42c030000464034010b02c3c404641c1d1160081d40c10801540100039002e02e5203c0941d8060103804400003090741c41403010391159003290303800200a000340d072030144107050480d41c050701d20340381005100c04503a9400c1813071b6101c01e0740c2c0e410a40c028080304040b101d07401610b0b28203411400104002c40c90200100c0071308038841c8120104603440c0d903900d03130b600130400c0544241008980e60840800c0410403e030101064018100c001601d805902003645d0100c0c0d0048030807411100840181108144c0e0111005004004601c0288100e1550f58002000c1d441103100040c01c050b60342c3c2c001141c450896031a2a00c0b50340090998205030091312409803070b070f48440c60035400103440c440085981c079514400e5440349d00800b03800ca82054402501500c4000700a0400d03185407081c44401b0300c410110b81c3c001c5000e0071655003d04013045182c10044c1ca8002c0d000c480c10400c550381307603007522880030009681480a51404070003c20310241d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 610649010 1250 610647760 610647781
    0x105091306150e0111070f150504081b1309150b030c03100212010e0405100b01120603080c1e0d0f11030316080108031201140105120906010312170f 65
    0x141c0c0000700d00c0b01c0e0030902c0041c03690041c1c0b210075001020303220b6a81c586506030310180c88504034003454101200031001808280d0500403aa100a216414100d02d09034650340e1071450034055058144000307050280482d000c1c20204070004c08819032040510102038241d46000a0b030002078042c91a107550344071400380c16174041000040d03e110180646604c4078281d65440003070362209170001503003801003000041c2c070b0b002d040030340c0d01c25604a0050103022240d0003086e4083e250142c3d2090401147c01c003411081e55961045900a5104001c0c440d95441c40c40002400c14400813402c5a1483e00103403061040c6001241e0401880502d00c0d260a8001001c42e00b42c0d8038508543c40d080c5103100210411a0900001001a200550548862015a0ba030301c0390700b692440740d100c1c54100700d60004010000c410303041150b2003000700141001414132801c0c09442c03010040484420090f544058010000d1020108109504400358680b00342c0c0c0704039850716010452000f4202e030400a044100160500c0f10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 610650260 1250 610649010 610649021
    0x1206161d011706180103200d12081513060503010507020c010c0b0a021207030501030b0f090a24090b0406050c040f0e0703021b0f0c0109060e060313020d05030403150b01050913 77
    0x8031404c11600355842c6d003860030a000c0b80090880a210611400582a14000c118082c500e48e10191035481d0032034800049030038400c0900342200e200c0803910144000d0b0754080800440c0209480c00003400c52600782050300b5a200036001300290b40101000c15aa643d201e0130307001940d40c000c649806140c80d2034119400074030809401010401090061000700385d41030f08072034101c900419009945407506080d00360111020b4589a0313455000020302c00004854400081481c0d0741054100c6098914880160550f003140e141195507180310000c02c03041141c0c81c428076421900406209081508001e60882d00300032030b0040c40c1c40103c40600180055119404450140090007824945c05080000c415690034810b21003031030074000c480b0140110352040800c00116051039035005415011801032000c1c030390015090203020381c1036004540140e00c4001c00d00502c80d11540040d541c2c0c034514108024600310600c290341b984c1e424111586410ba80c09000e0740d04861049903005501152815400003c10703 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 610651510 1250 610650260 610650289
    0x60305150109062102060412030518090705190e030609032a030a1404050d061a0f031b0f0928020403050705210a030509030d0801030b010b07021206161d011706 70
    0x88c15074000b1003c16501c440139104080480072118014455007081200080040302c6840010f507061003c9450100703401400c0910b551941010a9100b0300a40460709140c802c0701c040c166980000362003450056602d91200031030440c0340c1c0020204447c03041040e02d038800c0d80082c50811103c04900355111103d03004440042500501125a000b024600503028012184180700c03401a814000612400c082000c809040e9009003d007010a01012240300c0c5c2013003e8008a8001c1c000d00001d9600c0d84500b06941c2c01044c6000c0480c40e5520f820240300c42e40e80c0f908120301c04041c014042000062000076104050743c00c200c1b180314400b41c0c0d030101e80c44030400d5041400c0440c81203000c0c120516401900030b16100c0310540566082c40d074014410b0b16003442c00c2c84001c100441031001004001c1400c1d001d05a514030042c401c0d075006441c00e401034540b010580315201d0702800d11908102d05078200107002c5040400304088000e100902c0e0000e800384840e40082e1540e1030000c0d0003c0e2a0381e840c1d80d580201c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 610652760 1250 610651510 610651529
    0x160806040b04231c02030a080c1602040227060703020a12051c06080c040b03070504020d140a14161b0c050d05030306090a0905060106210603051501090621020604 71
    0x103d540d103601d03d50301d0703900c0581c00b001840601da2205880780f020040700c44180301a10b9444070b82c2c07582548103059912030300819041910300c00358000169a18002000c0360448203001c0144101e850207048030f40c0c0c218500083c402c000410207a00004c0d00400c031201100c1d0080f0303160f494031003410000d4030740384901d4003e4452140e440d00320300140302190b44150180e8080104072003598155605000071100c207200150ba05600901040145107002e4000308440b2144480102d00021b004001050700e50090369494041500c58400a800150010480360300050304014a8800d08419001508200304960a030320f4010380400c60300203000e15011200d0040c0406007111055410314100741d5101d4200fa5009449080900040340e4401214003901d02c00e580c100740900a9a468104199181660700c0d601c550180d8181c9600d00c00310f5034501c2504001c60040000d800b8180c02d2803409155114140c0050201920300f4100740a031004070910784101421062200c0103030141c0780005540b90280c0e52068141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 610654010 1250 610652760 610652813
    0x40b0f0603010b1c060b010207080307060e070b03040b1503031201090b0f06190e03160b03040303060504050f010501031407090b070203251d060f0d060e1b03160806040b04 75
    0x340034007000b141300310902490040186030304503401241c80748203502c40c041e141c0c0c0c4180550400f05505900521032680d0b45803c903002c0d5079031000301031215001100c0948950311240104008034540c012075450607002280518500b5102c8040f19941400c107010701d082c00b039928000f0320360760f88480921880b0004000c04060701c80009140341d0300d454491074090300015607111261040d43c200000c800c08403110408001c4110341c28480c60741010341000304260100b50700c50b0f40008844c0c48a1007168054680410794840541c18000050162651100400ca43c60381007402c03c0049030344002c3d89410303640300c1c003212503449410703000203480c0c18148070380b440510741600009501281c00c417506604031380703400006550b1031481003000c00442408035401034010410062a203544e1420590314516944103071400075090b0202c51b9401d152001b071540012005c036035118030740c010346002c0144840305550310000f0b03100c00d800c284400391034540c054401800b02100c400410200007100d10703d004d020000c090004c1c00d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 610655260 1250 610654010 610654039
    0x131e080901110a200d0f030513050906031e0123010311330c061906050406030c05041107050d020a03080f22111003020c15040b0f0603010b 61
    0x5466000e805114040b4441c0c6a0744010054041000c100140c1c002000350b405040a000300c0a051109130002640f0075100c46a0a00040e0100443c10b4401d01a90b00c064031004a4001050648d00325048644140c2c218810840c85650014001d840c400718905034500051b09122442e000d0100b03829400707401002c1c1d0510708240031078020818100c078041c0009030348249402080c803200b4006582d80d1120851070704660301d041d404802c44803001ea4445078100d45441c0c1c00311403041c01d10000341c0b1045074a01c40000e0011310321f07009009003000340504a4080042c54a03640e5030202d034510b00d104282c095500d0310b442180600c1c0030b00030341700d020303410100b80c4d000082c408200940b00c4401c0300048001c140e0560100d0550500100841c0c400e45110503d11065003a03249410112220b0031000c481442d0121107081031500c0380f2185012030b5070103441c0540c6803d90410304a046c5400001c060088242e51402c0001041c500b421094121812040806058942c0408280508184080c8039005075031800c0300c5a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 610656510 1250 610655260 610655273
    0x115150e04233705060112050c1209030405012c04090f2906090a06080304080703350f0c07030b041b030809120106050a0b1b060f131e 59
    0xb031007865040201c12003c0801036108111000114000040c2e031000242160451282d0f8800c42e04000f05042c503244c0b00c006d1041140954a045402d0082400080b607a911120302a5000c1a00a061500034500b41810080020301c02c194a40f100144032907410144e0702800c102c0d840800311002c2c043d00c14040920070f0b0034840010071102c0b508981d20b602c40e140c25182c000091000d500b88105c40c00340500251518002c00bd03400034040c1000c178a150755202c0024030030301c04000034001843c500380030700510751a5007130203500c160f442d440341141d4140c0c2c504020400300c0b41d0ba504c40c0c850040303005039540f101c0701d000d00d89807a4064042208420701c9000404810300c00c1c4400021320a40c41000b0181c0d03020074401941c3e4440074207100c010001d10301881f100c04a4a030054019948411001c000141c0310340e200e001400411050380040c3c0307000c9000802c0c0b41c140da49555540001c2c401440180f125003089040c3c0b410040c002803d08114941e0544a0000c0080c40b030f8040d10b00301042410701e100c15001b800c250 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 610657760 1250 610656510 610656581
    0x20702060d0506010210020f030a05061206010f061103121602072102130c08010302091801140604050f07050415051611101704151806020307020115150e04 68
    0x3c5016202d02c2002e59039910050003101c1c80d0b62480d405280c1161980c458213005004040c105540c030050711070350996268010400c0d00e000740b001022a165603480c0600c003a000d00c0041c5120b400d186c0040110b05400d40c012500d868100e6828410b000c80c03081400c80032420480c080e041040d85100000030b92040051890105c400385001b118608441523200510200302d40c41c0d40d410a01144403100104050f18080d1032300707980814001d41c0917195040504c038090841d41d41451541c900e404260911a46060a2081c0303540f14410040d42d61142c2441400034059000c0c51182c04a40b48070105014502e070301c030f10103903460415a070010700f401d0440c030314110891201c039001c9640a030070281d40030b100c840d1182007842a9070020100c3d0b140251a103482d4005c42540c404a24204540c4601c00031000041c0151185101070180d0001a00c038201950001d007528030994100c20b5520110806104200381d00042042002c85030500d03150340c2c0f98501c0814060a0003112105100001c40720250784941303d10800d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 610659010 1250 610657760 610657771
    0x913051c02070906140f040b0d0b15030601030c03080d06150309060c02070f05010c0809030d02030309011b050306011211130623041205030c01050c0403060510061d04020702060d05 79
    0x25102d01c40e40f9007564008551040c820300e9925241030310711200038280b603c22007036413000147c40468118420f0010907a01d0241e1301c000c032103212644041065544500700c1d01e0700568012030143c8070651454490355800760b45400701070900d400c0015620100c07007050380044014005034440e84180b40ca180005001040b984006849540c1414081090503201007120004d80381841c02d845011810440111049140c1803000c40d4620300410210f881940d00b000801c04030b8036258000c6a0380c2c03400440e96402d50b00c010615510a407928140104a69001700c1900e0f4000c40c280f820641c00036079241e4602c090094525403a83c000c1d00000c4840c241650703000010246c40399920795109d0110300300148003c4000b0b881c11000c0f102420700c030034800f00c8000c3d0208019240600105c0e400e01d1001032460b402c488094441c8001d8840c00101003080004600a40c0c1c0d1240c0180440c64403145000b030040e244000c0034000c41112040b4509a03107641c0e07580e07415a0599074024008644504414003c1c200520081c0d03903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 610660260 1250 610659010 610659013
    0x30705070c1d0f010e01090f06051f11010e0307030e0607020907080106030e030313110d0803150906031f050a1e090c0f0b07060506012a11010e060301050913051c02 72
    0x1c1c80f0850f8560041c3c100ea254500b01c04142e843d21802100130184d041009400700c3c1c640b00005001d42c1c0b900c480010f4414020135984c0a01214503001d00416080e040110703da90418540c9111001c000c4242e40074140c0505100006194560000310b0328405c0d4400290b00403814410b106080d50300c019110706962454504002c14050156000d990340002c07104c1d150850000c80e5130038000780a04c0d900c40c202c15000780c8050756007005075548c54201d4101300c450081079035820420406625000300103503001603003a006401c440d482e03c88442003002100c0400e2007110349030790100d004480c40c1c1d03020384c0ca65407180298031115940745014001030058000140ea000803100e4010941001c6503807520100c030000e06940740791800c16681c03c000341c40000d10840c10302c11004074051031030350036403034210500c05010782403400c44c1c03040c1c60403842214002c0e1080341001510f044070005605c501f82202d040d5801220b21945680c3caa4980090f22646a80024040c0c01251081a0307010144502000905072940 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 610661510 1250 610660260 610660319
    0x21503090d0305070c200103060b0d0507140c0a0308040510020c0109060c0e10030c02070b040303110105010e151306090c0807020c010503070f1101061a0a0216030b010b030705070c 79
    0x308119101045c1c144040d280440020090381e04a41a216481448406041c04200c0075607401c2c1d0b070b030044d0700318505011800342c94008100f2100d90103019607030101007a0382800c1c2040c01000d041da03a42e81c1104070007030510000f5404102880000c000b84402c50a00c2d80e025540d80c91140c101c8c45c007030b01907240e04440c81801c00f03030401400c60207074141101d8514042d2159908480500007180509910240d01040d800341e100c009c2000074030070004101942c001e80b1084900d910b000d0b040e17400c684e8140e00400402032510300384200081480d620220211003142c0030408208442403401c0140040d6000190281c500b0300c0040503241c1043c407451003092a6000e45040200901c01520141b0041f100000003410000816074602e0081c0680c840751880076000003101901c2e03000b425407060b05411103e0750f8000102700740d10813950410006003ca0145400000c51074034542e10102107030010302a01c00f003110044000380341c46201c0c02c155200c0030b40220003001900e45e6004101c04000c02c1340b5078294404002c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 610662760 1250 610661510 610661521
    0xa050d0609180b0a0204051827030a0c1a0f1015022815240f1a131d010801020a0e010f090b070606061b03020304050d021503090d0305 59
    0xa2280420741109442c0312592401e9940e02c00c0340355800180b805021503030034480803a145d11440f00c8190f0510150b01400b035182800240c00002200502800810220f058076004074080c0c084140c1d03510380a9130500c00070040051030300201c403201c81d40e41a13008210210070414107004803214140141c0c80c9100c15603001b0b40b105c1d48a550900000340510159026215909100c0358094040c034090303e400d943c0342507084290307071015209003000d04030344481901c8028813003854410ba000340e401c000158a404005500d01000c0e07220390440351203542600b444100529168500071011034800c5d07580c00c0c406041454861100340581906904040348004812001084850052088640f69040c0e80c4035105145440d0004468010031494090104056100d00042c100d02c01005442d8042c8203003030200d5080e09081004000011051009800b03000942c110000300b0b4000c0101d038243c40c2d041c0c1d405886500780340040341c109040c03949600ea51000002c1003000c641d001049154040c40180c2c0c05009940b601c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 610664010 1250 610662760 610662779
    0x4051206040c03020607060906050a0905010e0a02091611070b0d0b011403060d03110a03080a15060906030e070b0a03090219050315092805071212120b03030a050d06 72
    0x719401098032004803014409803900c5005044940d00c1018040350b140380e50764910059403410764440041039102e50703014081000c203001d05041c13003c020f001029103800c583c0000b400800c0251a09c01d909130b50b40b07100f21060b44555003400cad01c68101d504540c3c4041d03580303014030b50359400000440c0d021864181e94003000c2d032184618403004001c443e04c440c119207402d41080380d00000b400e401c4043c000c040c81e6410100304140240040c0342d001e5140d5034140e14114440307a040d03c0840000c000c1e480302c190014840030750400c0781074040e03a040c0d1030000744113006410b4103460107182d82c111000c0c04401160350a80540e1503041414514400d03a803091008024100c0c101191100340919a0701d6003000e111910a8102080c3c2954400100403c07510200c0107000d0065000c000c200171540c49010518141d01480310402040004105c2180032104420003900c80c803c512580c1d000e401c0c10800c1400c1900c04c6241941c2003980c00480085c00e41e9a00c14003243d000d810f5910424507400c2ea282096400190303480c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 610665260 1250 610664010 610664023
    0xf0f0608070509010518100914040b1f0c170a02010e06010f1404021b010608060c13060305090f0706030c030f150b07140105010303121407020a1104021c02040512 71
    0x6036803030ba42e0030500001c0064910303800c491003486d121400400d2504655483c400c1c0040c80766190785809015900309080b120390034401011450156003400070b4518141ca803002c08004a54811039400c250310141d21045030101c400400140c1010101503510a5859661004040140c03458008000740f2031803100346500c54a00340301c0d0401128220504010f0403910003681c43c0f4a20004000510300119684110228078841c8224117960390b4950081c00a8041040182e410402042c0303001d0410400700b440080071003075070280c0000c00d40c40e040480d0618900b0004060a2403050702501d14181d01c0d800003c0013020b2020f555000241052031210480b2240d200324101045a00c141e0344590703040040c1c50115910070401210204081060049100d4080c810315000e14801c0d698200000d12103a03481040d5201400c11645550800c001d002c4400d8000907002022a4880f034040c000c916004c00040003801262828101d41880084142e2145032550081056820480350f2001007140491156a00c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 610666510 1250 610665260 610665271
    0x9050402030a0b0a020f030a020403050c1e221b0201061a0f03071125060503061e19080a050d081b13050607050d140a02030a030902190f0f0608 63
    0x100803442c428046442e004019610442c8001e0152510a0700d8000281031392040324a0084594013240901c00c005003440b204504042c200ca982070b20310602e080b68078442030114070300c40c411152960b22400041c0444510841c0b8030000304100100c00c000e0501d04420b40e03401c843c800040d443d003240410354221428041d061400364500440c00c00400b8024140560310241c80340c1c01340140960400240b450802c58001a803941d511050310274481c511082e016061107410900070f12400380101b0a40b84c03120180e205c8050344107040c07010b07200818004990183c1c04045000882c40c13040700d02148402d40001c800005901c00c008442c0c0d01d82450800b110044002c0d0f500c06907080e4840f0155045100041c090402101c1e09088002c1a956510000d0401c0e801010110b03156040000c64642c01c6800115101c105403072190400d1a081c40340500035128400c009902013132642c2c4240ca1025900d6001c00c0c0b02c003480400c40120b052603140c1041641185440c0b0410a480101d8080800c4451003071411030b0042c0b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 610667760 1250 610666510 610666513
    0x8030a020705060a021e0d1104150207050109060e040b0409021201090309120b04231005070f0c0512180d0302030c0d0309031b080d110a09060512040204020f0c03031f0905040203 78
    0x70340f001501c0b1007056024031a003047d210348a0b9035600d01406190000c00051041000d9000d0394a181a000b9060802e20b51199051000340d0780c0070014180c100314208410030086500240724080c0800040081140200203900320449007000c000410b01548607001c442c0c000d4460409182d0384a20030303a1a45015200140010103041c0814002208a1101c1100c040411040210125803c00003860042090684641c5545540512205075003004060003240f002d840d01c12818404d507120960f0394008501907603ca9100001d907030030f0700e4030300300c1030031000000003003007000e0701009814001e56a07000080c1c0d8800a025001540160314007a10401d03c0313056268884001e6800c035480c40a5031600b0951098503c2c1c0340c00c1250602c500841e01c544001c1a2001090b11344640c010a801004140550080070074800c0410020380380f4104160040c0c3d00c40e904403400350780c501c6000c5030b44030a4003402d03884120510011003400411885054041d812607484001407a000d90340d43c2400f000d81e5002d07200039405 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 610669010 1250 610667760 610667797
    0x12152e0302060f07030516050a02040b01050705120a02070504021b0c0d0f02090606090904141e030d05090309091005131103130201110d0804050114161b08030a020705060a02 76
    0x1a0f045001801041d8020b0074113605100401c2d2080365441e001d840d00302d40d01d0b002034845800710318103807052100c400320a203021801d00402e40d690554488000f0f04d52401c50710f0214882a00700e20070001c4030083c0002900c10f5440d060401034820202c0f2091800303e03014001d115a1006606048000e032042c05d801910101d200341079030302404450b0388040c0c40550010303420403800725140c1382c18011070b0081c0e200303c40c495000340703881800c1c034202400d102000091203040c82c0107058444000040d5100d151a01200184649a80c1036541c6103218080c00e907a0050203140c10801040f901c03502d0741003221416200806101a1510340c10201ca014889034021042e090011070603809108081610340303441030400c40c1041803100e82551401c03440540d080d00045c2083c2c200010403a080c003590310100c0c4040700c4500c55090004403200b0717440d010000001009010401c1020007140003120a460070380001c1125036030f00f00309881101170752007107070140c52074031400001c03811007403c174803ca0f03000a82101c0200310 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 610670260 1250 610669010 610669027
    0x6081c050a080901150e04020315070c02011b060501180f06060c110112060f170304050a050d0302120307050703030e0f100f0605090906090d0e0102070512152e030206 73
    0xc030301002401c42040b40d942e4a00c054860b0503105810001b90662458901c61494584100b40c5403070308440c0303401909003c00e0140095240c102124410060382400d1401d104a2100d6180e04001c0320724001500003410040000350041003883c40d51003000c80058140f00d144c421070b000006844d4903224200c00100c903038040002042003030301c00070284081454039210300840380d1a150140c40c7d031904405d09060601c0b004003c0035007125400e1034010fa8400c09035003058035010004203c0025407055038024425055500e08061080c0440c00841c024802c2182d2070b400c00c00001480c54003c0301d400c0300031900d000c00194802c200024605901003107107004062014090f03010718081e1100c440c2801c1020345480b40400c40780c0c1c858100358424a90310f40244905d1034480c44181c5041c1c16010001c00b0b000d09584010126603000c12044180c1c0d6050303440c0c03d0906042d00d4094506103507142d50300e0401520800b8003200d0601082d080340d40303a143d20564081c1b005040c4c1800194482d600c0300a50081701009003a5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 610671510 1250 610670260 610670267
    0x714060a120e0a030e1008061302090316030303230907051e030307110f090f0f070507050a0b01030b01060207080715021c0e10031406040902210106081c050a 69
    0x1c20650910021504150702100d40b072501002c0f080803004900600c0c0c42c0740e10390609220f8140402e0745031500407071a04240011034681d40710b00054012035a00010a8203580d1000c04c8446440380700600340111695403800c006001b456040449007400b030b40c071101c49459511781030740c0d0b0340140c08100c00307412124544010040d085848071040484840303001c10481c0980d500f4006020554040c03c0314030f1180c41804100310000302031086e01c52140d1211810310503a01c001e080104d038000c00c044400c3e1440e40f586581a00c445c090420028240d1044001060400c0b000390f103403604a82c41500c00384001d0b42c8030241030f0707201c0c2d056000e0500b09601c4042c1c00c11114041c01d84141c0d2161a600540310314080c001c0c4102020000020660046a04045044072500304000b500085030828681001017461803080421000c401410003803055031941e40079015540c0328500b0061800c1c01d060944409051003601c00d005c1d1242c0c3c0304520407030180d925008945041b2181c02004d0410540c0c3c4d66207019403144040c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 610672760 1250 610671510 610671527
    0xf120c0e2511030f092106070302070f0b040f1103010e0a081e0c0a03120c20101d010b0d020303030f0c0f03010b0c160b0313050a020303130303020714060a 68
    0x1080b408001c0b10100800500041c0440002400e50940e81d0807200d05000e00000900d030300020301803040c01451000b400c041445500511140b502603594940c50511400070a0041340c080c00c8902c28100b0b0004201c01d0500504400c1e100f03980c514140e401103c00c05080701c0302c06080b0034081d007210f568040040c0e1a08000d202408143c0b0854954000003545944590008511a003c6501c948400014036410040c40c50203034036039035000d101e01000780100030003d4148110a6084000c01c8000000000c01804640b4485640080801012503080761281414801080d100310951800a8501c40b506011036851031240c1c0140c0114515240c2d81000e45800000a140042c4d900040c81580b4504401800460082c001d00400944641080c0304003070401004200c450010b00d40d040c010001c041c0341c4000c0d42e60080000380c0034644040319007052070411a50700402585808005003407859000d074480380c01c5c2900e0007542140d400d192104032145950002c1c2d11410b9000b1000e00c8270040c21403041c6c100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 610674010 1250 610672760 610672831
    0x3150b1003200f1204030801170a080f0f0706050a06210503120903130f1d06010818010e0109081914030f0a0605100c0510020a1b0204060f120c0e 64
    0x22030346010b100c44d51a000c0030030300781c80803000a40390400400caa018008404000320a000001e05a04005640d410031944212840402082e40105585156901160a80e249503800c0703d000c1c0a2841c000c0c0703480f0000c00c41ca008024007050750040070354142080100c0095001e034440300031407400b220103c14650f14140242401c01c58402001940020001c42030b030280200750500b501038500d1308144418101030552421a904802d00074100001aa48070411940100104807020018402240014090310013460002815803c00c98500100240b603c001c01510002e5601d0000c82c4420794021241051040d40020108a00748089078140e018031080a8100300301c010300064580d40d480110301c100070340015070800300d1028109103083c41000d110308000e0704020b910840c5003a4480360040d0030008000c002c1040c0e208200802c500315205c07507201c40d000e0146a40142117941d43d80c031b803441c0303030755100d920403103841c641c010b0006580391041c034126020301d160700201c0070701c0040c85440b10003040d1a40300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 610675260 1250 610674010 610674037
    0x5070803041e05010c1706030a1b0b0f04050a170d03270615050118090f020c031308120412020904020d0624050a081507020703150b100320 61
    0x210a102c8014550320300100d180300c1c400104d0520a80000900420a4840b615520282007002c00c400781d038001c0360040b5003540c0324150407540e01c0300200101c00c1500da5000f020014000007072404da00c403c0400600203d60b4229805400c003510b40341e02c0c507084411912800302d00d5110b8244000c10500076080140c038061881902c100e40000e00084051070290719409035034042c0c0d00e8844032548000074090002034082800c0c03051050303c40c1704a40e0f030f202a0900c14507401c4d99a4505031001450680c045803440b1469a046135240c20f810310b83e00b004110244641c004510445440b9041001c0c0b060595003110074203081c41e040d031080740d020303c030300d41000601c12688001101e440c07a00003159441f0300480500c010f150b103010f0044d205081c801007121074000c607225918885080242e08000650010300e00004c003021380b1151115a016403400400d608018401c44030040d43c0480d4040c264000104014200c40718258508102000e0701210810a10003030910b04651503c0c0c0300c20440700080071210b03075045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 610676510 1250 610675260 610675283
    0x51e1c05010603030e1e010519020a020301061e08010c020d03110913020423060307051608040b0d05010909020325030206030a05011401020f07051504030212010c0216060507080304 79
    0x6031541d08460785a007048010550103d10b10040c2d06164512000031030000348403800ca000b1450000e80320b03014100c0d554050480d00d01c2c940010301d10901c142c0035507684c007800a01055403205490914a6500c6440901030343e202140019954014020001d8450064000d86141001a8001c4000d440f0100404109142c05c0000219907225410650b1004121820043e03d03103090801e003011000c4100c0f840250740f41e40d58420005540c500c41181d8005510382851617441d45440c4100301511851070014011160104001031003000d62002040c0682c1c1072001000142e07210001141250208000a50954003000040c0e40155207a03041d8010945010b070719910517a85e0381d0010361390798401c0712181c03d49c585800041200d1040c4040d81e044842c82400901046a500980980e58034543d106a0303108401c01c0d01111300d0070070b0b04400c6501030b5401604040b101c00400c04814060110040c94030700620800714003c2440c0da2004010090715520b5442030303e802c50301e0301d40b52102d4101910070b40b040001e84 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 610677760 1250 610676510 610676513
    0x100501050306120f210a090920040801021201150507030807050f0c071502070b03040605040f08030403030e0c060a0906050903191511070809120109060f1401051e1c 72
    0x20000d09280e0b2000d075000b007003480b1050805030740c00040d800c0d80c40042c1720140704261050b81c1000310001071782c0341c01100103625141c050110340b103002c5640d1400045103000801248072a010340007880c3d41002d501171303461a03981e1910700d24a405081401e00c40060002e00c40600000d108003e003070f800c401945442c0303041100e0500c0344119070f03104da042c10585502115040004020700c2c8141c1c0960641c5001601043d07103440e4000b40180720061000f4070a9603180000b808100d44003040141e1541c100e101d00d5200e2406290250082c40c0c0c0d00c2440480d84100031408c1c1c60b0346406000c42e1040f440560303070741808919080c002c1d105904030703034040790341400390079080500e1000070035404905901419003189010b400a1404040302c0904401044a1a0405c00500400e00b110704807205c0340070a03200e4000c406c1d11010104d006240b500002010b441c140303840600710310060340064003e01c1b44d400451080d0b0b40d07501c0811820148450810009003041e0070300c0a8986405121042030740c401c15200020640d09 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 610679010 1250 610677760 610677763
    0x70e132f04060b0403030315080a031101090506040b0f0a0c1b03030b090718080a05070303110c040e0f0d0e030c010c0512040303020d0305090312011e0801020c06090f0610050105030612 81
    0xc0d080a06010f502240400034164580500c00d0042d45174005d04140c0d6040082143d140c0c50950710181c14002c030049440c020300802d40c00140490340040980d01a03080c80d140001c124a801c0e2042d19162003031101161540d01c0b40e20950010307001540f1040c9032003140d0507407201603251407401034041c0340e910040e0500f00c0d2036242d115440368445d0303510512174581800450861880d250026005a4000140c250000c0c000190700b405480c2c0604140790b0312500c400940d464114000c0c19250014207141e803c0515400000d00202c0180d1014190f070843d4101c1e0104413a840c500200e4245d050b44039400d089401d50140d103081d02401d0040054940503040361140c2541070340540d00490059100d0742500c0c2c180c40c0d0511403503400c0a9a4000b9520306458400100580c0c030042c0590300c24514084050483d40381e0b1140d500d0001d010b40c40080d5180c42c0034001150b140d00040f94000003c2c020305100c1d00702500e020580c14840c141020300440c03c107003098011540c503000148400c2d00044034520b1410348500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 610680260 1250 610679010 610679021
    0x70f0314010e062d03010e0f03390106210809040c0306080a080702190305100b0f1503011a04080601090906090c090903090902030c1b03091002070e132f04 68
    0x802c4d403552003114031044145801c40d0070007026001150441d5411403a44000442103400b00e140c03c0000341d01035000081c060100c055050350204500c04003020001e2a0075043d000201216403400c03100c852101022200d03810000301c141d000b8440441001210f0040ca0b00d0b61101105450030310380018866210420140b8040c103001b0162100c0303501007005021480d210700750802c481001c2c000c000b0458559941c1c0c681d00c400700c80b10201600c0c0c5a091034225515840148003600c54020494280312001d200489409d500078060074028451030b0000c21070701808801158105c03881400144096031815440d40000c1000c0c600c100d030116211543d40000c50440c11102c40980940100041c8203042440c020348507461950204900c140140200845c0e4075491047c0d814540a543c40300300c107005017400090961140d0122194880d0340e00d1445802c60303500164900c15203420388148007003034860007050160303001402c100420400071503048224400103030342811807180100c1c0f0114400000c11000030103554 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 610681510 1250 610680260 610680319
    0x61505180303120114010903120f0215010f0815010518130f0c050102010c030902090601030b12011d07060e0906040c110109031d01050304052e020301060305070f0314010e06 76
    0x30a071006203d00f94178a28802c001410908000340c82a203140e0b03a100b0f0100c07005009078103010010a10850301c0c0e00911050019018410101c1200d41c1c440c103480302107070800d0042d0000f91050b0f0140c0044003041c0700d90365041e2003004100310945c010b00d0b03411910b000c2008150312401d50100c500711000860801ca000040340c454200c5458031802c10b0002402c49041000c00d404242c2440884c1000d600c408d400340b900840c080c6000f140f0011b680e008224846566540d218030341d2318150400c5d1184481c0700c904c1450254610a0303c0e10541da030078040380c42010f081146ca07884034001000c034003249001e80c003041540c0345908024000b0100c0400300f6003150030094081d00441c4031108100c0032009000c080d0001d0020908280341182801d481f11a0b540009a4011400e04910610808030b4240140d0032000f1054240081d940c030341e15144000c014110a0360300030b011403804e25107070142e130703001e400f441701000b2048080c0d01980c0c1c0781071045c030084003026102d0358200d200340c80300d210280031b125125031540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 610682760 1250 610681510 610681537
    0x5120a0c0809034b0c012d0f1e0501050307290702010e091003030905090123010306080102181503010305100c1b0f0510061505180303 59
    0x2102005000740560700000c0010409400401101140c00d8202410b503440c0504200300d000ca201c00c51031040e0095440303400300384031001c00c2d0240c03802c040201d400510380400c0314030081c00040483c0080400c1783e03100f40c40d43c01c4101503080c029903030250709a0041030654109600030900c1c000b942003441c2c1e814026001c007a14a07840714014866801c0400c42c41e401070a00350100c5d000da441607841c0c0e013100b424902c0003002010001400b1015a031041c402001d9002e80100440b104c0d080a080300c400c030390700c10310007240170800ca803030002410314040c01c0ba6412201e0701c0072007041030394144200196801131007016606150f529403010403607507002d2000c0c02c07174051001c1040c040031500d0000c00c03145002c0c1c100b805c44080c1d41000144000350011441c40071b00002228045002001080280c450a00000070702540015140d0362006000c41c00e25076101d0180170b4011384a410512224640a44603a4040d442040400c80048140c091003403009005801c15410341003a004001e81c0001e065900112601505 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 610684010 1250 610682760 610682771
    0x230408060f15060702130902060c0307030201050f04211814010e060711010503070504152703030e010c02010909050f0610180303140904111c05010807031205120a 71
    0x28907032801e030000003a14034803800e25190000540300b4850000028003803c10030501c2203242c0d0b6590400740c2100c0c6d004240c16115440986a940d50b40c00200d4280d00540c03c00c07012078051038100d0b0000b1b000f0354222104c0e000c1098034400e02c480c5141d0241d1580d0030480b9082908040b0210014543c000c1d02c80c42d6031006400380944001000152940301042c46030500b00050800518107070f888541a08c020300f020b58aa80e40c1d648140d03024081c0d648808110200e01c241c2c80c2c0303041e5000764520302c1c03041c001400c101440e04400e915070a04a40340001804600e200500c85560340c0980138828007648145131001c007141c1c58000502c251a01601c05e003100030208014403d00d890001314804401101d841e0140e4401405459010f42c184a840041d013408600842c44542d05003000854041d1300e805481030151050350410070409a2000c0100200c40b00001c100302c2130000103008190480d003502c0c00800b045420f45e01d945880c1030140500500780041085140c4141082d406aa4854132802400089 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 610685260 1250 610684010 610684021
    0x40201110a0506011a1215030f030d140a024e01140d110d0204180506010e0612100c030e1504210503070f0207090f06090b0406060f23040806 62
    0x103c1d15017692940040343c402e10a21866510300044180d0000740d0703941c450703205020440400d00744402448484114040003582d0428001a50820303150180c004410501c10399582c100102280180c42c03801d0200100503010031700100d0b0720300020710700e0340007400740c25a0040300d00030b0111031150803900408117034541d5004014101040e0400010600d041d10002c90f4240c09990b860394801320308400c01c0c803403035681c64034500759120b50b88410801210441800710000c220b04213640d80740801d220741c0994414030000203210f82071640907046d4101004006180300b20304040c09901515103c2c2d50141050f558012400010384100090944c003071100c402e0042a04180c00d0456241c0300d54040354081104100c41d4040d050b03441004c0b658001c03850701d0030032200c0190350412400c11f0f80a900000d40103003003041203c1c8444181d03001d003048500400c0c0c10452042c0d501c090100355a43d40c0b10b0040131580d60441d0000c800e0140400340d402029400e5080c1800b40072903584455a0803640000c1c103540e000208100c2c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 610686510 1250 610685260 610685279
    0x40e07050a1215020f03011e091406130b1c022b1a1b0901090b03070201271109090c100f0e0306360a06090302191505040201110a050601 60
    0x3800e101d0f0745020761501d0420040e0654070312044c4104041d2518032042076018100300c00c0b690029140700c55040c040d2400c0381003002d009003400c2da40184140030300800414070304182e11501b4508180038105d42c0300d00b800384024102003100d03140f090760010b00405559407451001d840d50203645141350701e01407954640d4108402640305002d030308501408204c00b4400c44485101140186011803031300503595403951300040354043c080750720500b9604404001e121046406400061500c065000c008540c8036480400410360f180c0010050720742e80680d82501040e0034a540c01c0d03a44030701c4402c1140ea01760f5041010440a000902301e01000440b10042038032750300c0d4084100c00020038100d0090005080000700d400010703541c542c605110065000c103503492042c038415801400e070181c006460100501382895405001e10040c11030060060f0405c142c94186000b00c0d0010464000031030004280445500c0d80040a0290003a418070449021000381d00301c1c00c0000e15110380c803682c0a0451945000c0783d40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 610687760 1250 610686510 610686533
    0xb0417030103050303060f0303070b01150210150506070c150305040314071a18120a020d020d021f0902030124050301020c0a0620070c0303080106050408030702040e07050a12 76
    0xa0064080420040010400020580c1e80201e81225411840350500c400249144a0341c0c0b001048200454000650040c1100c0782e00100072040d02621511488002044205d800b0715590400c0f883d4410401c2c05103081c101e0107840380791711840d0b540304050f4a804d818880c003000c0c0190000025218010001003507440400c2c542410f507009692401c2c103d1665400780e030003911404074044945040700082e5400e00b001100b461103074485042d04c091000103040c0d0b44083d4400407915001d8818603903080a61440028407442a039650f60241c41d4407100c4441d455441044544ca4421071900d82c844817001d6542881b500110007030f000261701200c101c1085180010041d0b40c04984640d1040c1f010b180d00c02c401003683d00700154801c6001501b440540140c418400400000303000041d80402c41c402041251a807035025640a62600e10351b581e41e0722411115442036010f1000ba86c2c005101e00c00043c00c00390044031280e000d080940c0c1c00c090305c8030007046422540b50304c05202d0400280350030f0280003400013030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 610689010 1250 610687760 610687793
    0x3030a061205061614130819030801030b190609020a0306050a0f050d0213050106080a050f07120915020a0201090204050c040509041704082d06040b01090c0306030503070b04 76
    0x1a58007000e09440d00d546948005150181520071940c810034440d1203000c081400c2c03410001c00f6a1141454070201840d40d419000c0c212240c8078060700c3d142040d950504030400260f05540708400d036800d40c1d0300d201060031702500d581c090b034804a400c49004801030240c0c40140461010050700ea800c040e0340142034440d03039800280030302403d00d010b001c200311324a00d510030b6400c02c0e104100004110f10100d07060b0742520030f09c011400d280c1800031540b03a80c030244e541c0c0100d0004105000c0c1c3e846410f0f20070b0001c001a0b81c20f8000ca290142160034100250b00100c220354007602124101039403a203086070981c1e12945820005035900c94020b011843d113403146030b41081c0318440c86401d050610002c100c61030700242000c0c040002e020541d000c50b010100c100d4014100a85c11340300c5822200f8449034212140384168104220300d8014101000f4002030340612840d040030074070841e646000000001014802e00b00e4041640b504004400719804200a01d041c0d481348503445080d16040c1488500c034400d4102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 610690260 1250 610689010 610689029
    0x1050a0902101d041a040507020d14030709060804032f070602010e030403023a17030f07030203100506041211010c03120c03091a16050c0a230303040503030a06 70
    0x744820f44500181d00900d220805032000500c1d03001610401450010200301a5481810101008465540850780c0c286810341c40d1111240c04040b94400d202d14001110f1400000d2244081080080d21560b40700c2d030003034020304201c0d0441c420b02258861080c0491070764440751202565050343c07403104001980003464584001c00c401165107224585a100360710004c0d03c00c21070044031421980384840d203610030184c030000c0500c0c1001c0000c08003980702e2091006542d1301e11503400d2084000740d4281160b03ca85000c80c610b40041d661481c00350000d41010f0801c5050140d42007020030503072100e00c000c2c07028041e20070755440c42a06510b4908480f0300da000350f690400c405130001c00c00181d00805c190300c211480542c0412110300d003200841c01003610060103000e6014081130440c02d42c440c9111103004205001c50051031107140b070b07015103642c802c8590902042e400740d0b6001d008240c0c10054070a08c84e48445040d803070620f040191500e103270400d80e4242c1d01d981000050200e402414410381c0c0003400942c0303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 610691510 1250 610690260 610690277
    0x220f09051014181e0a20060703120609020a02010506030708070501080c0d0b061803010b090601120504141c03060e0115030213080313140d170a0203070501050a090210 73
    0x2030300010201d00585600e985618103c90000f010605009036066456980802004032419001c0c00b5554042d400054824480709485124480401c00b00b03502c0038000a0021403038400c1a541c00c55411100041e01c0c440706540307000214a000c081e00041c0040516640007182a042002c2050f0800c0c00716400300c8201c1d0300081c002c011070b0342c002c44402c0d0b01600c01da400c0c4e920703141d000f0004405003206841e00c0b58464030000da0680750001d100c40004401100754000c000103002c0e00c0a120200c4820b4480a012549a040240b0381c102c00d600041d078414404c1d101c021302003030100b42042c40e00302184c03500f0004800102e20001110391511490005280c259041c01540d40341a145104164000b2894820180c0005620050503042a5100000c0c4140c0080302d642e84100ea11003c95032145009004036000030018100c035074508480c603040171580011916440c038070404407200c5240c0c04020724074258003080c4204030114030284641449450b086001080300c2d03040303104000c0780b07a00541402007400980d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 610692760 1250 610691510 610691531
    0x110a0e190f0b07111005040602010e06010501080a020a05070b01090617030a0c14190302030c150c041518080d030c020d0e010e1c23030f09220f090510 66
    0x1101c80044461054040c0d94900c840c3c01e040c0004403071010016003104a44d03000028259200d00104100c5409a00801c5000414017609855950a00c01c0500051054010030885c1000c0da004054021b01070810703501d48a21a61b44205580090740b1030240c142e44c9032400c0103040380d0441c840701e151034000090f62910030141009032142d800754101902c0c40c0071122400080d980100020700030892100c0b14600c60090a107002550382c0d01c401100c038983d001f484891030007603444401c1e050103698080c8449003801d0406c00c0a8543e40c04051000c01000b01000518000c6540c420310800640480d02c06009443c4900e4400b07001d03142d080441c3ca01311b50010500c0b60015a002e884190060030901c2d140c1c40d0400041c0c0000d4841c401c002c148416902070050500030000e0642109440440c101c5800361140081418952680652201286002c404001685032450321220114a0700d040070641e510108035414100c003180e03a080403400d4090f0341c0d05c1202e814007504000c0100c403031289107818003010281 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 610694010 1250 610692760 610692779
    0x3040e090607021c021b0402090d050c040b010f05040b21091005150906090411040c030204080606010507050604031211180a051c030c052407230406080901110a0e19 72
    0x2001100e540031b601c0340b882a8020358403030301101d00e10131008001d9849003081d4180962644400c0d0303641c904c03c03440d0450585d80c41d4017902c200e1882543e10388030b00d03041c5460201c0508143d40711f01031201130000c00b00e04a880e4043c1070b000c500e010700c25403001491803041c0704440108980f00501407151400e10004040c01550703030481e40300c0c2e005d1801d0b1205030b040c1e1034600d02a10303046a80ea1103a503016092040070030f09541d1541c0900121a00344c001c032038450f29203c0054446110f240f1000d0a41e411400004003ca80500030030030401c0c000004c0080e80b41c3c0d03055861512900140c00d540c040c4102c808180f0b002b440c000c8000c00c05014110b440450582010001d01000c011080380242400428001c02c0103200341070112503500150401041d480b01c030307811310b14030400204a510102090005c808005041d001803107040c4404006507041d490142014000d03100b0400080c12907a1940d01c444000010f620140040d103c1c03042e040e2a25101c0500080c01c204d541c03410225500c51350342d031010040240304907 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 610695260 1250 610694010 610694023
    0x5061008030f030a020c01060806010603022d03060108180706171503032d0403050309011103181c140f21030c030403050c0f0d0e032d03040e090607021c02 68
    0x562150050b0f1b03a00d0100021400750480d07500c038440b18000d50f000050110f825030018160510036400c528540c00d0150f15005607003101d101c621403100400e000090352175014404480c3c110400e041182c910f2980996405c0c9040c1040c0c2000c1d0005484c00d01003094081d45c2545650400e2118150740e0750042d992003c2507403070181c11040c0c00c82d4400444141070754092a076407440040e42111210766134507124113040b1390300c1d4024280c19001403900580d0007416200403050340c0001c8542e0f440c1500c5072001d1002c001608003000340c0b4001c4483c0b003490000000d074030308880e10031100da004080c1401083c0c040c00305080440d0054100b596144542082c0080002d01007129800701442160580b6911241400c0b100c43c040d042c1e900c1c40911400480c00b900c402d0018201903113110566411038070348500303001e054480e035a25051920208a41c0601c04107048601a0700001103400000c50b803c1c107645079164031407100305480880e0b06400000030311462a138107101d02d01c03009440c600100900440410000e5640c031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 610696510 1250 610695260 610695271
    0x20906090a02040b0d0e15010b16080c030310142e0e030a0510180b04030e040b060403031806050408070b0702010c0c031a091c0e0f090405061008030f03 67
    0x365840c0021002001607050f140900500b5480640b1203900003000d6004114500e9151102d2103400380d40a008981616600c0c1628501080c441c142144603000049810382010121591281403042200c208070810255218100341c1140f100d1f810700d42500c1a60030020504054000c68590050f0b81c1400c851598000c003035085011088084900003000301c48698800c40da4560500484030550188480003418220100d1607400800401045814508144400d40301c0103141d1070f080000900403a01a6000048000340944042000c9840071b00003030441c1d006810860100c6c801800000c0d00c0000380c4d805002400050800d107187c03c1c02c1c2109256501c91038402c1c104034a0001441c4800c591082c101d03941426440901581155124500226481072204052360860a440700103407a0050020b20714201d00540400c80a00c0b0310040412251010308030059500991410660102074441c100454804c5000740c0c05042541440d4042c00906c20095001c02d0460f4800d1001e0a42d241c0c0b14403c40c0d8120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 610697760 1250 610696510 610696519
    0x93b092802060408060103060c020c0f040e01200406080f0403020604021e0306010f090b101d18040c05100c0c0e190c02030d110408060414070803040312120504020906 73
    0x103100000100034100e61840c00250805400308001940741000a0031a060301d100d80d000344000e1061030303c2240d0710120503580b07948c40080e0440480450400c0d80c80001122071034000800d0710f160072050500c0700899010a40e5610200203010400540c1c000f002a400840c607034030300126800c060310001d54860300548040c0c0f140c8070b0000e550003c0c07507110301c813200340382d2019054a21542c1d4a0243c3d144952951044041240c140302108880c2e14111030780c0d2001d10242d440348944101c44c12143e409000d150045107811103400c078181d000050300050400d22551040e181824503500300414002045862072000c420302001501d4000010440080881611004260094140e0b508604014419800b103c1000d0140c5010300000c030a41d40800200291610b82c20140040304802c80703180b0046c459841004c009810940200340000c0e0820525558001c400b01110642501d8050960442c0d1080d4400c075684180305038401c680541101c036101507844401c07410000341c603054010406000000b80300300d104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 610699010 1250 610697760 610697803
    0x204032307030f0602090108091507030b0105070f0c060905090c0d0c0311070609050d051216020f150708250c030329130507021c093b09 60
    0x10003007280400650304581d401003a0021400c0c508029072280c0142da001844200000c0e0200c100058048446101c001500c115540e64481c203c00800d400000f050400c0001c00282010a00402041e15400d0060760b103400c0b064030707040014281c01060360019008104060401032200454425181440c00c5d10360302203041c030407204d0300b10018800400c42c0c2c8a4890042904c409001c460340c01000c1c0301e403151044500c0c2c03041d82d54007506c0c18010040c0f0304e00510113000015243ea80340391320062500c0982d00480381c0c00c00c1d5030b00300241043e00900c0e02c0c2010300100410051807941c01480035401031008040e555140c0c00c100800c1610170b0225081c0b1060100714080803041500c6a032200b1010440350800403055000d0301c1e0781514280701c1a4100740b01c0c101c4031070760f2903a499a6105a0b4058041a001407446020705010f059010040112440501092650018503041698440d15600c0503400d812441c25a500c65090314202101d2440050540c0e07440030440b0f20400003030320030666100ca8803869070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 610700260 1250 610699010 610699073
    0x18051f0e0a0b0714010506040209030309010c1403070b090d051c1a09070314091603030c150612031101091203090609060e0307050607180b0c0c041d10020403 69
    0x607a60807691201c2000b00001400310284100b507070b540d00803c10690001c0c03021341c032004104001e9010744007403154950070400a644140d030180122070b0250f031052050b91540052076800fa400e540100500307413148800141048200403007800007038400701d10f50030000e0620309400300001019140000c0d070641c1d01c2d643d0104003126400c04100d00101140144049001e180410006000d080245002d52510702e00d0808034400c1100801c050044c00241c0e08039108503031954404a5461740046000e0700c901c06000650080c5007528010000504580391404d01c80301d03401d2400a01d81200110022680c0e45049072a100113004040c6c5041c02c41d10034030300441d980049052941c02448079000061401e0300e1f150260b455490040003914651303000e0300941d032180e601c0e2a81658105031280c02d0b500070f04464103050007450000c0c4040c0402c1c7c4200d404842c1c0c9428003001140485500e9092003085550180b096200034800b00004407004150901c00c0d8105860b66880300300b541c001a00300703e8410882600307000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 610701510 1250 610700260 610700269
    0xf070c030512180109051606050f0d0513080705071703121801060e090105060103060b03130f032a060e070f03061a1305060307050105030402030606040b0a120318051f0e 74
    0x44a02807020001c0145e0310662501c00c1ea100074110550b000d10035560310004a59014105650110591000d15490076401e64140801024018250001c08400d148a4402f00705078074080c080aa10400042c5032580c1440c201d900c24110611401c610b562041090034030031704055511035000302044d40c805400d0841040440d0141901d50480c11091090340c08005442a05401c442c2c0101800c0e2000c01c6104d407101800d010301e00c422a40080703070f402c2030103003140090088c1c0380340ca10150081c5445885183c1402050b0310510f41540b40242c91445016207030244180341c03051350440c80d03612008203052450b02d0013080d4010054840079160030380e507440003c0b421a01280140e101034005005510792406110600001c01c1d003640c40303601134452010041030550048003100e02030303078008008006d95511602000090002c2414154019072a0900040d640180140340074680c0c2c03294a400110307030088024107071981001d81c007491062a1003011205101410000703450407088524107880810480d80219 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 610702760 1250 610701510 610701541
    0x606170403050d0e031606020405040506060705061b040f14090c09030a170d061e05030105010303050702041a130f1401060801060f030b0d030905090f071e02070801020c060f070c030512 81
    0x22a401114106c03000c20410294010700c10365008507000c10a0fa191001402031034042d1000044c0f171795100c1c1d00451b9640d03103c0758180800c0c0b100440340d10300d441c2e118021340b00307851b490394007684c1a110407205403842840c0a0191031f0344a203c0088480c00c0c130a0000001c0c0e80c0d907641c0a00600110360b41550529690420811100c125401d94010b2000958400d0084e92000b8550304480a0304a01d2101003028903040c0100d038101e9030076640c1d103400c0c50304075001c100041c00c403205001d2a00398100c1999139070303889184400700b944410002c0010000044a00b070415103843c1d07440c465002c400240140201170f000007605042d148145041d4190548910054004207907481c034503648a03840e42c2c000790405038404140010740e0b500740c440a8080c1c80f0ba117209408803d0641d04100411945c89808400404405090490b00c2003071040301c001603910062035007241d100890381050f54111904108000040340402504024103141038402e0003001d880007803881c0a00055a003012807001c0c0404e1300c40542401a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 610704010 1250 610702760 610702777
    0x30105060c0c120703120201111c1d010507090803270303070c033e1201020d0501030b1605040e0c160209090f070909110609040207080c010606170403050d0e03 70
    0x12215200c103441190f80e9591248811102d22525061186c242803043c003812240d0b01c450740c20241046080304e81205281d50800707a039140369607030719030403a0b9180024040d010101e807424000100c605120000030140340c0160000502c40e4400c1006410300070210320320082c080c0e204a07103000c01140b5140041c0c19071045400180200440c900c000c0103000c948000007403414000c0300d0320800003800401c0580d54042038442904002030b088040341d00350800c0032104850005441c0018a401c4e00b001182040301c100ba0400d6480040784003c01181318110304440c655810103040070b5040903e8554401000c480c000d007098a060390200f00304844100341d501c406245076004080703408a290420b4056640d8694140190741881100e074001003003c1580300b007003a00c0e600f00d007141c002020303000c00340103d5511030301d2400d4019500300000b002046040f00034010f05600080041180c2e483c012000381181c290303401440c0f0025808060100183d0800210340c441015042c0c0400da6040c0a400282940560342c031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 610705260 1250 610704010 610704019
    0x5150117150d03050a02010c170609040311030c01050405010f020f0f07150513030906081302060310121a0606090a090f0906050a0c110715110a051608010b090606030105060c0c 77
    0x1400b100705a009006040680d441c0c0d4020414a004543c2c120380600000e148240b6003484400424201d01700202c901d07034450700a06042141441e6107490602c1e6600070141030312640d42d07500500080000038080c03049100c002e0740055042c0340c035904a0f035440344a04202d620540c4c400080700300c10000880c251601610702c8183c10019407410b4801880101040001140020080c1c0c101140c52406011f1041c01514032070700c641140b090540c01c2c850303664030150031100400d1041e040080e98030481e080505e540391240019948035541c1c000d8850740700c0000b800c078034812003041c002241140c40d01c851400803511401000701c1e08200035541d21009041e02d075800b070046400c12040107040642c0d904490408080c580d03580368030b48034034a0300340e80300c282c240100c5404104a00464540030700c244800f1244210800c00d0392545191507440368540614081e400b4545c01c450036080001c03034020700c01c0c0030b001d19090f0f40c0a412861710b100012201d03c014054a4412070000c035564109090402407540b007c2000b41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 610706510 1250 610705260 610705279
    0xe100c051903081810110904051501020d09060804020d0f0f031809020f0711030f030a21051003080d02070b250512011215140108010515011715 63
    0x1103000c02030990034000b40c003c10f689102141c030131510000800c800c2e0080d20090800d404c901848000907001c2c036988600510824020301000d41d48500c10b1a00998421b00c60094001d4280006070528a02001d05810300c080040d08009180d040070055900c5039048840018445e074602d44404c0700082903001600c0075848201207010150000c0e001d0403c48070200d03000b000d55560790513540a81c0310f03240c1ca903484040b0a0180368002403c10840080304d54004055414040380108414655040070501c81e0001d41c0b141ca01d02175651040d840c0381104030344841e0900c00e520b000c42030170b621141c051100514a140004079070031031900301c0d03043c0c07940581c1c070510004440c200781804099481c4e0203840c08a00100001d02241254080c01c2142c0300d10480900c0b80310aa80381174011000880f90034010b0710b00441009484032110800d204001c00c208540e24864503a5040034586804c5460042034501640c0d05400001c8446e0f8201d0301c8883d82d130100d001c081540f996052040c941c80c0c0d44c43c0b00400d41096050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 610707760 1250 610706510 610706533
    0x1903080a0e0310060b04030b1003051c390804120f29010314070e0f150603190506030c0d03050a081e040b040f02090a0902120a030e100c05 61
    0x1c40700c50701440200c08840051206450100480c0c2861099141c1424200400c20001d00b40a55095000100320103000030150f0365180c203810544140c81c1040c8651603280103100e000c2d00030034001c802c0500070015030142071201c000d1201c58201139565401a01200e0032140c1000501404c80c1e0203491b910040c4910003102e89003101261880c3c203030031a840d011201c1051480032100081503c0051136040080d80c592940d11a00c001101c0608103149902401d84003013240c110404507a40a8080144045031516015903015503406446000c00e00c110701c01c00602807104294011442c4984811000040c1901c0d4600000c1c03030180c0080107613411280c0340141409140c0c008024107040d46180d11007010a66840444650700301d0586403c0080c0c1480354046404504400c0055500c1845880d92030312a010980001d01800c030201c0703d5891030381c0c481d59501b0460500302d1990040000031801444107113941c0c0c0d0042d01c40800041c00341c0c001c1c0358032448038004510488800000079003200a841d1290340d00e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 610709010 1250 610707760 610707767
    0x306182a09022d0d0609140403180e0f0a0c0207080c101107080106060f030203010f060f0e0a0e16020102090612040201090902030a060929011805040f0c080606181903080a 75
    0x81c2043d0a811850a1400036086c2c0e0729000c0c04580740044c4586000d00e5846540541c2d031300d00071032941c0d01d424019101c041040903c1c4100c4038043c20403c682e00e0440c1c1b410261881c180c80c2c00c2c0503507800310341100000304501c480c000780900e8580c004540072018400c1400c02100c500044088a48140c46070349000a01c0c9001940440192002d030f030380d60300b051541d4180607416807000b0b20800e41100e00d0020104020380c0326a0200340f4070052890545420010240000c2c00364440d50000380c0825254018403c0d02c4890034000c152410440c0000d600b07146070301c00001d45a00074900b80c002ea90b54001c000500f10780c854180780014001c0300d84119180d0405408544c010300480c080d100649181411140c03418a800c030781181d0301e07c401e00035100c807070005100455106d10980d041c1d50444e21800008503c43c1d44501a0307815803140c0c2d003400242e594100c40d004086442c0a058140100c00801250303448110020b01075803485000c0ea0802140103151140a000d01d4443c3d00103000000b0100f09440010360 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 610710260 1250 610709010 610709017
    0x100e2a040b0d112e020709050109090803060f0303070213060317040323011b030b040f0e06070f050d050403081e0921040306182a09022d 60
    0x1020340c0c0c00c0040e0240101403101910500303001810101004441419524003402c400c1c42a4141c0c20000a10b49403034600306110003201c0e010b040c09604042024005250341d88100e1b80100702c59441408070458684500c0c0ca40e10010788118003440300b940b42070078a0385040040b00d00b21a07000d008a0581c0d0011103040e0001c114601049845c9071680509402147d03180c410368090300e40080720b01c0300e10101c81280c0c20b0b501000c00904000d5540381d401044c104407001c843d11031015166140443c500900404000813190070000d051480fa14040d043e030044200007600644c00440c0c1e040c5031810500811080c0c0340d40c000c008004001d03605000c1048201940445142e01a440315008450100ba1807441d000d0200c2040310b404002e0390048000841c00c4155640e20001b2a0390880c8580c80c00c0e4407070305c92109030307501000c0c90120380706980c0300c040c01c10140c100302914084031101700d02024140000c50485000e40c81c414016255000300d503290308841d820714034012002804030a00750300200b000b0407031415007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 610711510 1250 610710260 610710343
    0x9030312090c0102010207020f0d0c170109050609010204120f030309170c060f090d14120403110d110a1101170115030b030c1521250e03100e 62
    0x303415214140f54014020b58030300c9540100031160028086050000c403590504050306c103074085410003d03c80d0b410050080170640f100b8004201d0305c0e080e081552802c4400b4151440580c8100300c00c1258882407000104100e80c0040c2100c142c0201c0e090850103811a40710161a48401c3c440e18201100410028280707a4070307140540d80181d40c0c040c030100002404071054244c03900301c0e0340214404c074401e0880489440f40000c0c80c0782006114074803045c519500303c80c100d000c20911491a940f401702040340c485e0208292810704d45190101000d5a11103486180050401ca540c05102450303a004407800c0c030400c10f03844c4102c85590b81d2a543c0d0029843e4904c51000480d01e0701c000301c030f003a007004102e10740004000ba010414109681911250f0b0303a0210b071100d180d0030804106a0403907201140558043c01c0d500d40c1c0d484103a8041c148410340005803228401c14003030300d03c105205981b40802d40603c80106000d0019082908403201420880280301d071103460300d10100c40d20320141d0f40100c681c41c142d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 610712760 1250 610711510 610711513
    0xb07230918040b190e01091101110a0c0b131d0a051005061608070819020c0a03051009030e0307230616290f0601030e01061202150903031209 62
    0x20320a06000030310180940e03020b003030320f480103000803103184076140f08004c0c0110048000a0800d02c100708982103d8901c2000c890305a40451041115a40902014000d00a100c05450b00c01d040340d8445205c0c403024407400c03002c03800c0880e087e1001000211244d00a10030047c083d42c00405190001c0159503040b140754440d9803030400410010482c10020006950300617000c98a0003441300040500240030340800c0725882e0041140600040411000d80103484090120f01007020001070b01078148040c1c00d003a00e001e1428148100f01189002070210700c91480d03075a00281c07185241c01d0455541102d103001d20f4151042c8000080e8002811450202c03c0c04881103070a559091001048031034031503c00c000b10325407101810000030954801d0034a10a281c1c0c3d0610310380580c505481d01c449081c04450065010340380b40c0030882030396098003802051804140c003c01049003880340c6800c20014003d000f90280402c1c104c1810310004400c00c07181c140350b00800303c82d1119103c2c45000b010b980211007000c0c3c507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 610714010 1250 610712760 610712779
    0x2003090f0d080106140711120303040c08010902010c020f010207030819020f030a02070e0c04030f0b04050d11190c030c09020316030b06040905090a12020d0f18030b072309 75
    0xc5803051a2031410383c0d1607a50781c400c4110741105e143c05550000501a19401c49180d0101c0341540c0341081e04807000d031140c001d91f40b41d1034181401c1f0804800c6a2003008241d040240035030050381d209290211041d411518400c1d41d601c0c2c400101e142041c69040240074040c0060841c8071010700c3e6031050344803d440d500310f440e11f07100018001d89074000c1c2000c441c0581c0c4508000c0c8104250500100c0d48151280005402c090340c0361144200c040c0d6044081e102101c070f40c0144000e000013444100d501a4441c1007612011000c603030340e00ea0b10150701140403c629800ca241101b08681e813800c440046410103104d081c2d264441c8100f200030f500c151500a51200501941d1941d64020300644113141002424a400e09180c07022980c068100100659040c0c0112102500050110311005018500d203074000d20203c43d143c0030141141100c0880300051010220b04203044400840c1240166a40600c800d6515210f4003020740352914000400d1188684000300c007800080c440004c3c00c031000048666242 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 610715260 1250 610714010 610714033
    0x30109052113060e032401060e0f0307090b04020d050907053c0f060703021006090b0a0312020321040c061b03110c03070f08010f05010503102003090f 66
    0x1028400d400a5403400034110b6020000c1500401d0300070340507031002e0162200c2800300c512920018002280e418166140380c0018401c040e80410040b110714030a0300c0c0c21016601c0c000c00655a201c0da48a15101c0c00d464000300050380c0c480303805941202c1003c01c801c2c45182055409107468503103500404c0e01507603207843d1a41801c1c034803080c2e0400040305001050342c5041000010f82d02c0b486940a025005101d40c5100503064a454000b4149503000b40c0c007500e15040010107000980e04240d10100200d401d01c0d202c914645e660207503500840341d00912803100842c80c03001c1031381540601c1c1003000014042d454043c3d5075402c2d5502d00c030310032032207144902c18042c1c55207001c3e20310012101425030703c45901c64050307000a01034010052002c000504552800c184034000030710b043c805810220007c607105070104040c180c01d005280301c0d03907038600c8144119814480440d40d100612600c0503801519070403c3c05107a11803c0107207810f4210100203c1d83c0e4030388a285035990b40c204449210451240140000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 610716510 1250 610715260 610715323
    0x7050f07020f031e03252a0e01090e1605012c0303030424090309030206070521070201140a05030622050127050c0301051e1c05060705211503010905 65
    0x6d00b6540d100d0620850419454104002038100c4e02c0d8503040c45803411808078031040c4011040d0f0081219860220758910f01c0320380581041d00e0007800c4540488544e10034400c0c3d030380004450785c2a5881107050424020305039004560400d041901c10f400d404000184070034400150003800d400400090404031f02c0e8070746403010f0101e881d00480078001448200d0140b0041c0307451300040c491305009800704c954510b140c1104076440c04205000c6200340c540000c1c40011540c1181d10550369510541410303050108801014100380310040c5260311a001000041904540c0304031a88400d80d01044104280c0d0f03106e000311600b40e00c200c5a00c07c07248052044c2e44806540c24003035107204200300f082103070541e440c25091001c00312141380400000c05400b1109440c640310310300b100d44135050701031144a140545060844c10b151000c4c043d4400c0110400480001420043c0750651143c0301c06001d840d6552541d0f201246c00d448032040075415401c2c50711500c10b110000906c5010140c40848610f4a80c14586401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 610717760 1250 610716510 610716577
    0x60f0f080319020c0a080105010602120421030513081501050f1807020f01090f0c06170103300305011e08060a0f1506050304050607050f07020f031e03 66
    0x2803945078420801d50794000001c00d14520100c0c001e00444452414180018980b48a190003a101d560343d503e004003c8141e04205000002035800441c0d0325003410040780840d202084100c06ea0440900031a2204041c85070302119400814081c3c010015521810310903250144151030594440300040041000d1409030356000b0300318802011a41c41a0403c030400034044001840c4406600400c46658048282030080f4205070b0b110342202e41c42c1710641e00e0030b0040c0c582d160304000704210511143d181607208807000309055a80241ba12140b44100034001850fa0340320300d9010082003607d1055032100d030f405030840d0b8140c0c1d4442620314030340c4402c045402d0702e5812074803513038105038810008108031500caa0300814600304003020200c0c0c082c1c411040d2007004483d941c4040c1c0000c80000410051010620101d81c101600385000341c900320b90b4085074000b9001d0b0420203071090310f034081c00602c65a410071105240038074410352880c048070030a4450b601d0350030102d5084042014940840c89203030b5260580d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 610719010 1250 610717760 610717769
    0x20040c0206060d060e01181203090b15130c0503241c050a0b0412030612080316120f0209040e0c090c07030c0f1103010b0d08030711030706020a03060f0f 67
    0x401c040d555800820805011820003665103036601c08a00c143e082e4203000e40c810090315018070b900082258601306030040384245654041503d44114800092001081c149c1c0020085401e260020403000011745224007030140140d03040c1c908600c1c0c20201c0d0304039016511078007a090041080c188522913021241c45a1a003207948404040b41c10000b030600c51212a60b16030141d42129404040d0780d640500c000000c2d18181c81c1007040943c446441c50f4580550000b41c04000c0d85c2691a004e41d0f51005017900010300003200782c5d60180380d4841d080c2d1055070f0b0005402c050f8a4144a0745c0d40400c4103000952020100302c0c051070800f621501203d50004040c200c0c4400070f0443c10096540824040107500a604214100a07a200007100454180c1c003491004502a40ea01140340c2404003c142c21901c410109600800640c1c81c1000480c0c07010055903809500d90808a1180080590160440c4100c80b401805140f010802000d00342d4560300080689000e00c3c9100c0103540c4440e100c10000303205108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 610720260 1250 610719010 610719013
    0x7030c020d030c021905060f0a06050a180b150310090e0c0409020a0e010608061f02060c090109030b0c0d24050d02130f0e0d050a0e041a03070320040c02 67
    0x44410454403a900c040120b0fa41841903c4c0180150b8200401040c6030b2541990664880070901c00410b1081000a4128000501c10400f0f070b882e003c0481c00a1881e071040c00315400ca903000811203032041d42c006041100d4014081c401c0400359400e0035129400950711080ca01e0f29804010071110414840c00c2c4501e55220014101c807a007800400000e000304480072a00240c03074210000e400034052039900d010708120f4031140301c1da280100078440230907641005204414000c803000072615030049180c9030000c0302c113441c0c150360b54042d10060f01c525009501c0180001002e004110580b8013400160003001420340c000c0c4452090110300e1003001c0310300305028400030550701c820040e0349481051035481d0707880030b0194041d00f00b00080010407181907004202800f80c65040014000c5418000070902d0040750030b080d802c0140c0b5a030000e03c2c05510132010b07070195542d04002241850252504203100c0001070031a0415901e926004440001d490306c1c03110111200c4500f40d6007480c06019440100101c4d50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 610721510 1250 610720260 610720273
    0x5090f060402060f3705030403050d200a030920100f140706090b060405071d0a0305010e2b05190e0312340b040618060e0607030c02 58
    0x2001c0208a500410391950344c024100604050640c44e2502543e901711000d040d030b01e99103500c0035000182d0051424007410090108200000281c0020030b1320080da00440c000074641400d1204a1050814400782c41120200800e04203072040d80350f048208164400c407000c84100200008440d40c000010901c1580440c03107c1d2101a814800c4250300c500b5081842c0040d0381009501e07880200d07a00415098581e0f41d01c9845003c1804600c13414180c1101c0103440c100603034a0400002403000d0300e8100080741101003070421214590710726403000f001d590000c00802004403800c0c130444c3d981e130490f814500034500d81d1940004c40344500240341c45241440e19020b01d0800c00403815240300358403001a10a03c01aa00c0003011602c082140500141c1c1c2d11500d25540c03081803a403160103032004803441c150322222050180f2401504640f454540b680200324134200d46441c5032001c081c0038600d400030b5001803501c2c00b81c410b106640d0808403601e0702c1c1f90140c03045078581c504120140e52100d5290300244e880132 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 610722760 1250 610721510 610721513
    0x90111070602060f04050307020d030e0108090c01200c190f09110d020703031b020102040f05091302011407061503060b030105090601050913060915060b2b0216031205090f0604 77
    0x125101360b2061150050f41c5c600016627001485101d07074010b047e400201886584100c9581003030825400c450000700030809400000c000a1018569101e40b030100121005050000101004100d640140c014002c0948109040c0364142010725407003001e07500c5000041c001000b8026110365102142150301c990300c0c164488a090000e50311000341107040503501e00c0030100015940c41084a803422a03800565600e1038030a60b03208803003564104501c126140410f00009024400791120456820b090141d00b2042035103503010389000d600300c0a000306050482007500c001c0f81c4088902a00d114803820042c0440c01c0c01414205c43c011900035409030712190040c456480e00d80401980042218120b40d107880c102d9842d42c1c191100018100e4022003071980e602c000c02040d014407c0a008154105030800a06002c00011080008012180300800500d410700703004050f0100ea0300f1142190301c001d075010b2145801403a0380140204100428940300118a045001103001d020340f0340080e0003032040b034645 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 610724010 1250 610722760 610722781
    0xa062007030521070e010801080c0906240c010b010807030b060d0f0209060c0105040210050a020d11012903120310050f18160806040204030816020a030c080309011107060206 76
    0xc04203031041d010b9910f82c0844400c01c8090852180009580d604603040c0d070f0800141c00d200040e080034502d0380000a011611340c5410760101c2d4814001c0720b504103001c400f40c10b0750060180365034010442071f90000b00d851480405400a046015007aa204202c5680e401000c40843d0308180405600079020003c01100491b917400001d410404403100600e03150300000001e1096201650b010660b035103400030030044d0724010b141108128460b0420a2801e00058802502c13281c1070b03692039062181d034078110047c05509521071f10500b40e1200720003100f04e41142c4d881e940d0781000940c0038864490703964040c0010340030109032030080022380780c0c100600d81420200001c035511401003503000661010030750004d01080d00c4841c09190340c03880410b901800303c1c000411410f0001c103858012030042104000141e2100d01302c0b03000e80d50500140000905a200140e0418039a03440603040c0042d0400101d412103001c0000d08200109807100c1c1400e042d004622500c50145201305005a0072041c0040c541c0c281c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 610725260 1250 610724010 610724017
    0x703080f061507031e0e150c060f0907030f062a050f07030512040c050a080a0201020714030f0703030914041407050f0d020a0801150216061404090e0a0620070305 71
    0x460f003040324054080c0d0f0001c0c121701e2a111514800104044114030241c2444480b10700d1550740181898646900e10f0506a41d0b89030242114080784c0010300022003130b420600265000d1640225034041d45040c80c18820082c020003c0410254000c0304802c2e041e0508aa82e00c20f0010507039145c60742882240900f1980300c0e0405803040d414070400300541c010102c82030100b544618812940d68030404e052800380705400840d5003000001c0d60041e40301a0160b81c0000e501012504200c08115103491070002181c1000b864400800300c9208260010013050340103500902074441d87c03201d240300003442c10704002c00d50380f105003c0112030b84060082513903140304000031b285040300e10101d0f030720f00358421860788220380c009a2003c000a040c1c00062140c0001841c2491801d0782c1c510050410504950f0b100340001c04a1081d0000e000e60306148003141042b4506680c02000306441c00c1041c00441480703a03403100b200f141c045480303078a4224204072040c1540786400040203020100d40c20403800e50740a0714240d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 610726510 1250 610725260 610725263
    0xa031e0e030715030e030f030a05190c0c050c0f1305070e1302120615180f0415080c03030324030102091309060e0f0d030b0a03021002030703080f061507 67
    0x409940421140c408000d80b900410509a000d80c0c6407000200003400c03602d644244520700c0d081005079016001c900000c0c0c0b500040c800c0e40000f55902d410703075002070620300401909d040d181010300e603840194100b01d0120705207002d02d06a4918519031003c001c042c030318000501364451f020142d045142d03025580318a500a072641443d45602e50000b0000d20310369103600d0b032021200d0300022044014201400225045030b000d80381803402c0440070104041d2401985008081e41051360507041d41551160b0300140402c5000c0d2080212100a00348101c0001c401d005804552003040b81050003810000222845141a20300500107030603a003900070b06440c613110125078559024801d10360b013035944200364100c10f410450001241311440c6080300580780c0c0041002c506402031750310111490400710346000e203400349103070008514030250f00003404120390b608040e410010401240c0c010ba43c00200401c503041c060b0b10b800c0d9080c2d98464500300300010844201e80c0000601c54070150a0710400d02803c0d816 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 610727760 1250 610726510 610726517
    0xd0c0309023307140a0c090e0105060d0219090203011203090b0f03011e0312110f0c010e040c120504051510080a02010804080c0f070f0602070e18150a050f090a031e 72
    0x34420581da051034407045c0e1700140c5100c000070780108518034007031140f6440d00e5819070082c4180c1c5801800074a034101c4070701e0040e0240c81800a00d2103220700500400c0043d1804610464403541c40e0f82d0800c41221410204401007204201c001c650100c1003403d40f0019600c07504540d185070309000c54900480c03402d20529400c00c80c00a03000c00001c00c084615510700e5120fa5441c585481028401460b000c0d20703180240181e001001e01c0c09031640c1c00041d04c2c0c011034095402060010015404132807102030b0807501701c103851a041c1403200304280801c100282c4001c050250b1a2038441e00428000e0702c800380f2480c101c1e03a000c4485079005500a9447c10780c80341c042c05000307052180e4030090300c3c00c0144240c1c2d00d10164020302c4c014007818600c1b0b02004054400c2d8401130560504180740d00c2c4590700003a000c071070069500403501c7c01c88041042034004000301c443d54030721780381080e1a000c005006d0556950603116100c01c0041c025030000100a60215055598182c2106200d6a0304100c14009407608040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 610729010 1250 610727760 610727783
    0x91302090a05040c57110111031b0d1107030b06041b08480c030a0306050406050609010f03050c0c01090302030405040501090203070504060509060d0c0309023307 71
    0x3410380310301c101c1c00c601d1155845c050104040000c0f4441c1540e4088442c00f02400d1081d40154410208640801c0369500206c4200c80c00341610068505000751000c0c0000c07840b001a0412038120140d280c29036501e5450300325007910441c0801a140854000600061640409030801c04034000024403504244043c0000600c00b01a582200e0300ca45040d80c11804140c0b25428019080202d00803200d030840d405140d01c3d541d00c41107140750314588003031520750491110001c1e80b06100c0c86080407201900c1900e01140c1d550000e40c00054050500340c4a6584250f00d050b20020381400c00f10308507040580c0594231104c400d03024941c01d500901001d4070715200745109101c0d510300307070109218110b041c0b400fa800464555282c0750400c810703100c2c145c01a9502c64010300c00d0107a9103410205403002d40710790342041c5441d100440b011940350300503215441c001d0b508088110f01718a03019802080828003c1c1d507860a03a10349084aa1082c0700c1203c8826040c401c05081103500500440c06840118442c00e10f0300c46 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 610730260 1250 610729010 610729037
    0x50f1605060a05030403030f020c1b040b010c0f0c05040905060108070501050f0a120b0a080a0204052d09010e37031d22052202010c20030a0602091302090a05040c 71
    0x300d0b00b041c0000b0215501c5461003c81d40f282f5884d40e000010000c44052000300e03081c1d0b0000700240e0380da000040a840c18101440c1c100244500a800034210261040028a81071704105030340302c00038031030340c0400d0241c0d00c404502c0d0f510030b0080f94408070101d050146009280c4c402240c400b106406105001c42c6d0321584845103650350b4500600500c100001042c0340105401000b040724005499030039000107134252544000303403c0c22520307444502540c201109a45c0c4100342c0303014048040e0301e44420300481201c0e011f0f0811143c010f44612158206030080e036249410881e1140f14203000140100c9c02601d0301070b55115814102c2079080342d0141050f03503003140824102c0c40c40b070704800e0180c2d4401e0b211000c00140b44c0070303d12188058180d204483c0d280c00204e80000e0103207400064084c0c1020f0401020340321403803528542e15608000541100c18405140c1400e1000f034202e0902c080c803482c81c0340c0301c440705502c0380e000f40c901900008000b040000d02c4c180c204001064034460034000d01c07202101504c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 610731510 1250 610730260 610730291
    0x3050307020a170c010c0314060120100c08091b04020d23040201110703080d18051b0108090708030409091b0f14090103080909091207050f1605060a0503040303 70
    0x91a1a4080c0d842c2c0d131900c48048071319080d10301d072901410802d460301c00e10607001400800725541048080c02c01d00d403100c03000811451224100110106188142030400c6d5007120242d01144080006a441405da40c5032107081a8645e030890b05071031440301c20040032080d0343c03030640c0c001c10028950746030000d446425207a08038100d030072620b00950103456101c100429940c10800520751705408901a100140c20755541006502805280b40d1b400ea94a003590450340901c010752002c0c058220003110b07461034038001e241c04000050040d0314002219040030404401000916409690360320001d075081600b070041060081c0702050301510200b010018041950b40f507100e68401910b4000101c100403410800310056040070134007c03a0254031038800401c040380d22241510402e840440303d40c0b500e40c48004d0a070f4a0124405240180e5480016003001003180001c0c00051441641054030900c2022440720300c41e036401c610926401c4201045028207043c401c20066074418424180020000c41841000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 610732760 1250 610731510 610731533
    0x20316030504050a060302130b09010905040e21041a030a060b1204030306050105070b150a150c030810030c1514030106200607090b09010c020910030c0b0f0703050307020a 75
    0x103401081c00040c2c00c1c48541466907043c0050b0200303041c107624298070001101c1501119104104c1c45d50303400b1990f440c02d81c4c800d220f11001054000c0c030500100305082c1226440f503441c3c0d400280030001c0c0c90801e18006240109403021644d65031982c005107100550031101030360004040700409aa02c8802003070303000fa03c3e40a0602c4962011150100349824600602240c6040d00b2142c1401428030840d400680c7c10200e15034400d40016822101c42100300100b0309840054101c510280320700b010b50904940c1c8080400c41880c0a41d8602d4103e0722081100c02d090025404003500011480d0b505100c130702440340c0e022415958511700642e084040704241903194100380c0140380002c00d1000411800120050020100141c98014283d0340c10500d001070202e050b988102c0041c40000715894806a0103982c8d10b00e03130950040e140c4401c0c1d24106c010030100c0c4000d0f02044480f4203003900007003907038031105040c2d600744807448100300d19107060b50f24240d6103600002c012008501c60803404600248801c00b00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 610734010 1250 610732760 610732763
    0x1903021005070201142d0c0309010509040e0a06020d0b060306030c061c0e0705041d0606040f0e01020f0309010e030313111203071209080f0c0d021816080106030216030f020316 77
    0x5240b0700003c00b10001e44401c0b19000c032180f00c03020a1002c40121f00d80841160301000007400e00030354544009020801500504401006030702981c611841481070700c1d0020460010400401c00000c0410400c1008901061720083d805500400702c0c1c0b020303420003100400c241d24040318441101d01080c8001c2040d200001641c403000c1e00070003401c100604040c080c11b19032081070b6a01518803c1c1d1004207503a14580284800d10407521035120520080090b486801c8005501d80250b41d82c11525900490690054984410a42c681140355190000200c242c1c1d00a55103013080049000142e1100c0c0e0001800d40100740d4080d40b1080c1e038910781c0c2c03420001001c2440c4a00c1c0b95806007040d01c032010340a80c80702d03840384480303402c041c00c0f0003505000450f00d0220040210b981d0640d03c080c50000c580e035480070500344e02d40801050103200c00d00174285140c1ca240055070791200702c0c0ea038070303034000728213a020b00070410140000c440200030000703000d01e00e4501500c01d60310440c0d0a041141e4401d0801c480500030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 610735260 1250 610734010 610734037
    0xb0d0c17010b180f06010302040918021305090d0305040c05040c020d1218030809031e0d0b01030b010921050607052106150c0a060f0605190302100507020114 69
    0x1005660100c080c080d403000400115494a4031016000070224043e42c018801000100c00d540050816030003513042c0e07006011404002c0040401d000d4494019905c81e9500b44c0c842d00c80c030120b4032504406030207540d1041724880027800d20140560740681c06042c010340704071601c1c0c21005e8042a00c0c1c171584100308511701d40303a004101e40308010b41d010309003000b00c4118400303060402d010f20086000c4003006c1d0b940341d5454a4141185d0b42c071060103230708600034261042050011502d080c910143c500d400352000203d03480c01080316030301b042e005504a5581c1c0001d83d021030706c901820000780410400e424891035600d03c000398003900ca0b598007070a000b011500000403500200d0b004041c00c28280c1e402e030b00c151048030704d10a1418030b68005851020001c108032a81100021400341e1a6005d00031902c016038050700902c1802a28014240584030341e004480c020b0300441620109801d03034140030b400716600a4200440f03501c507024100c64640c808002607040c011101d145280c01d60221004100e140710016 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 610736510 1250 610735260 610735289
    0x7060f02032508281409151003081c1508160e0c070317090a06140601090306050c090a030f03030513050312191d0d0216090b0d0c 57
    0x2c2600c0c45400e03025414010070b076003190302c4125500030308041d0704140c1441840320340240b5042030b06101d80941c4d0050072181d00342149401110110403149004103640300a4a00d00e124160300c401000500300c0d0412481c20201c00b040001c6400da10007400c03501403c01007168084421080030064880c3c100b10b821400c034a0795010018001f052100c0f14058596070348030202d142c6000b88288003d6000b401c03030b03800345030002201070406010744410080c00c281d4801d1f1461b1851301900480d03c4040c0260155020780c01c1203402c94502443c2e0403254440d503016182d145110f07046856010003018010088600171a0030403807180c00d90364070b619030b8000714498098030300107504516008040c0c0f80040c01c5c1840035209030845400280c0040142d4484490022000b056079880340c3c50000500360f02050700c100b07a40303060158070310320390100900c81e00080c6c1442242c408951008040f030f0345905880102c40642c20600c01801058215041160003070700c020f042c542282c4003529400b0766445a540801501e402c0035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 610737760 1250 610736510 610736521
    0x12150402040f060315180210080624070b150301060305100b0906010507150f0e1605061912060306020c0304030309090204030807060207020111031909090e03040b07060207060f0203 79
    0x2030040926402c45200180146495595001010500c420b8000c0c1c3c215222001e0f00050300c0d20519400d4800d40007080c0c02e09444d101c10000d400300300141c0b1114061078120707074103c3d41207501c1d00100c0110180c08084c50700d0005107441d96244448041c2c0030390f030800c1d070641144555580901504000d180180e015054030300400301060100c8403014802402142ca450400c2010303a0040151201b50350022440c0500b214115950310003840408103c401d02850b01c10350301d0100360005403049071030041207107400085480c2c40400502d80140010381001c64407103680c0d101d4503485072881d03070084441c0040201c1e6054596854005a0300700540c4242c0da5800031408005140c0e004820900510b018141189400c0c29521510101c3c0b02c1d119000d021150005503243c11a48500f000804e42d18144082c0da0b2590350b41c40310700110410390401940040d80802010514142910420080b02405c100840c0381c41d180003442115a0041c100c15600341d5800d00c03080c80843d460703000b01e850f40d02c0ca903140141d881c82c14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 610739010 1250 610737760 610737769
    0x1050c12180a020126040818030c0f31140703090503070201050a05271518010810090c0905040c030b01082215020301050108060306041205070212150402 67
    0x10180220281181c81c0e00c42440d10109007100703016020b00c0c0c020f50354000041c0038100300a88403603e442140d090820001808480400742010a102d8000d200d0000c2c1c4d00700c1010341d09c240229200382d0050400320403005501e000907068005442000c018015802e501c0003804080802000000440c0e0300c802d07000e030b03000c0b40141d038440e8048860700f41002415410744030582d4a015580c0007d05008000030307178820443c0101c0540746a001940120110041c550800c801d450040b025014080d2005542c1d00007881040ba0aa5515104d074201c0800400c603890011030b40b00b080544402e005201d00ca40102da110701c0d03802842d110b400c46840e640d41041c5008140011a15110b512104040c60714a0956560b0380c0203001365000314010402481e003c80c460120b51001c1c0c5080707002030407003141043ca00d08003c0650040c0d4101c9078241c07030b4144a5034866007815212041114010005449021210b80250003000904400ba0000d0000f420b001c0c0e031080c003149070009106e400103420543d8001c000840c0341 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 610740260 1250 610739010 610739047
    0xb060f0d0b01090b0d0908040905070201141e06100314181e061b13030c081608060115020115080105090c010f0905040506030f2515121d01050c 63
    0x40030328040700540d21380803039148280684d045081c4410348a400b40c02c1408040800c3c1e60103020311140400c180e040010020740240307480d40302104600703c9400040d1000180560382c4a000c2204000c1181c9540c0700e00c10050500000b0751010113041e910606107500c0f4800b985c8803403194440c03010054501c1102c01c1e129240c00d4022003c03010114190000c01407425010950603003044d4180b1200002490380c11003600c40c0e0107181d6415590030090500001800080207a000c1101d024000341d0780c04070480d1260313100100441c010b4560680c0704000400a92445000f800410411803000050b00025a1841040004281e0003140142e4464040c03122400d070501074035811003002d0030a00c2c2e0030b1048160240040d1aa485a148140d5940c00040c419480901500134040c0544090b15000090031601140e1130fa066038041409044000c3c021500f800700c9000c0c0d00341c440755902e40c407030b12001e0450700340e0181115510b80d100c0d501e5030940a4030303810824015240100c2d21006100e071276098a02c1c81134071500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 610741510 1250 610740260 610740281
    0x213090203040b040b0f1e06030a12050d05010b070c0302060a0c0f0606081b010e1009150f120b030c0607140d081503070f2607080606040f0c120506040b060f0d 70
    0x1b8201f80010030340d0100940c40364200780c1c4040c00c00d40c0e07200800607042291840015200460401510309660b5000008041c590220702c001c00c035a0362507000074100b6011744807000b04401d18001040c005450b001028051600080c40e20700d5005040e50b80d81c2c2807103180300508540d041c1c0c542c50107000703c1000344015001400340c104010290b81020b40020a0300d085242c400b4000d08240b09286141da01c9114110042d00001a030040304428803000145011454070007071000070708031180003c2412136030041401e0000700030300a20844240e2010002294070404003152051925200e400c444c6d40305000d0030454104d08d0321445d420b0310700111800c500249a84e46a4481d422490b02801a40d241c82511015240c2000d52448209228520f05485003010782d020810b0340b294020002d0846800100e40d44645c0c0c2c280e03800e0044030b0f0704d240d8030782c00e0704c50034a28040481d5419030840400c040d2036000d203030701c420001c0021070320301078003000f042c010342c02040a031400b54000682c00f070034888103014281000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 610742760 1250 610741510 610741531
    0x5100902210609042402090409080d060e040b161e080a050a0204051806030313121217070c05030412030201021225050706090b15041113090213090203040b040b 70
    0x6280c9681d0356600b03a8544007900e1034800f08507a002e50b066000d1b0b81500c1d51000040c00070007005803542888016900165030800541d424950b002c03e1411103000910700481d488010020f241e222000c680e410340d8540018801001203030700c40e070425100b4000030305001039915221629282801e210074070035035074024408041d072401040200683e4a0b10b00d40800d10b0113411000c20b901703807900c40000b03046110340552844d22170031140c804901d091079200032800052080201c42240782e03140e1030940b040124250038482c94200302c8001840f1a0060910410151207841540c0c0340039203442e808828200103d1098005030760210b408246e1046200000b50002c4c15400c5040303035152400116400d51041e070110b0020404040384610400180740c0001c024282e001c40090050718080e040e1031200e10070540000c3c812401d00d038204015240d1402141da0440008042c581041d0500326408085d6021245500b000e0084240c000384020a52001d10300940c400c03034000b10345042c1400c00b004150b00140044504 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 610744010 1250 610742760 610742779
    0x40b090c09011404020702060d050f0a0501050103140a09020d0b190f06030203071203050f180f0a0302030601120f0b01090e0d020606091504020702030d1107080f0709051009022106 79
    0x1070f50300400240d01034004840259488500d480405ca0320301606024041c981e0070701c0103010700400145289407145402e15420441d40c0c0e40c0b68011801c0d6002229001c400301c9c03c40001ca00c0070710094020380700303180c00a480e15031801526542e46040c0c040031507848150659581081c4480041030045914440011a041c01100d0660300041d446541034410205070f0143c01e11240e041601510543d8459a08000300c182c030380307030b04044c00101c82d500f01b40114481c21200f01c0c0742805146c00510041680d07009001401240e09180302c0c010044a180c40954040401c100d8400000c1c0055654074060064008085035807105240141d2502820f07e1842065400050420400f512881140c5a0083d246801920280f00300c00c0458024450058082c1d05801240c9802a003560852000c2d0707101101d4104442101d56101207440d100c0d441c0715005000ca4100180410423038015402041e049201490605030a41e942e08014040b41d105004a2415104d2180c5690140100e00c24030740e0b01038800c0c2c9881c1720 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 610745260 1250 610744010 610744019
    0x609080c13021b120703090608161b050a0f020a242016050a091404230d11010507030507080a151203080a06051f08091203040b090c0901 60
    0x6100104161a00086501140000c3ca401031480359010b2102c0340b80070383d601c85002e0101c40c035040c3e024000580104030903040c0042c02c140308024240c401d0488112401c090303004484115203496400003007680200304a42c1080c04184140201051b643c030908d078800801c50203205000c1d00d295294420030b400007907031940703e072074000740349481060032554a0150025814803041181c0d81d41d5601e4440d05502c40e007550701c400c50701d045043c041981c90442c2c204444030754401070703982903072011040c0f05440030004c008603001680c0100c1c880c3d07410108070f206030910600301c8132051600d20701c5402800080c40141c5082c80001081c400c90f60421000e2a0602003032520b040c0280c0b001a0140022046a6607044c500c01c201e440840c0002c040c10140044046d0540d44d800c00400d0b015087e04c1503002a4901400007645150007540810300e07040407160413200b500d107001d0641d4540d00c0200304070080c2c00703075103284092104008019846180310740800d4a10f800c01d950b49c18035086108149a00800c2064018803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 610746510 1250 610745260 610745269
    0x510140409051308030118050c09030c04020310080d0203030114420a02010f1515110304120f05010b0d17130f081e03040308040315090b0403090609080c 67
    0x4060303030314100c40451203407180004100c491110f103070040c1c036001d0f02000202c2c407102c115400000b215000034080c4465202d000400d06544100313121030b0b0341a8086081001c10f030a194026503440211525005103072507071000500d003088603003010a801a040000107000c0403a0380301210310801d1083c0c83d0700c1300e101074030326684800400c0e02c0580f11160240483c01208403000101c03041d02811040d00c40360f00c400407500040c3c0039110030501c10b144141012a1021071a80610b909011180d01c160b1142c3d2102400c28251b424082e4060315000f940010400840c200c02020840300d0300074451300740300030ba5003c14140103084500009915214107418455940411070030361403100409101c25070207954600d050802400e40710ba680c13009000c10320009001521080c01f2400f00300c204002105c1601c03c0320400012620782c4103034000181042d0043c0010b0000c01d564120b1008480c0d003540c0001201c03400e07030700d507031300740c1007088a0490001d0038592062200036448140b04008005000c0101110007400d000107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 610747760 1250 610746510 610746517
    0x70507091109061b0115051c0b06040b12011e0f020703021209061b060f0f0708160908030d06080c040b0d140106030821071e3006051014 60
    0x2d9100e042d0200741102014079035081e4003220188040200403040c0040b21441c10400c1900c0b41030310606040030503800302d40840743c02084030b1764014075200306580c5400c00c120003416800c80160304958841e402c2d848100c0244a19010844244903c1000b02e50310035811003541e0000035240486401031208000007034001402d0360b40e0040720101251648444000f1403440c2c080c1c0c40b90610380e6440300600c05613049020648500030a818500c190041c1c1d03031040c21644100050751504005807040c4005015150f1009074040314403118070344030403c0b40c5e5800400789550004521460308980e00c103020040240d00304003070544000c081d1802c0c8002850040001c00220b0012005003031600038246540130500c088d80314802459111100075154030400ca2500c1e003414007883d60302351a495034408a000c843c0580803242d0907a8084403e000c0002951a044803225500e2810030400d04618001030080c064480b80d441c512071450400281062904c01001b2281c66048241c00034881d0449040940c014000100e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 610749010 1250 610747760 610747777
    0x7260303071d0607080315010306060c0b060301060932091f0204030203071e0f0509010b071502220f030b041226060f1009091e0603080705070911 64
    0xb00c0c00030004a090300780c2058005100c60703803000c0300140b49401c0204150165004050340c114071240302c40c03400e0054045030301900418020030305840725440010708034041c0f194408030103000840c0c4565540f0500d415a0024101ca0482c40e03030903407600040300000c0c3c2205408400c48250002d541c180b81e030707a0a4454549041d0320003048000701c00c03500401100e0701103800465020303044442c665680d20740c8482c02082c28540d0600303001321190002e462070100446406544005290028503443c00d00b591180745d01001c3d04803581c2c00740d4080c500c51060f440c030152010310000546403607c180b04500f10000d00400e5000410728114103442400850141d44c4442d50065103c4159003003081241c9080e1502400c11645051408100309054810000550f120b07000d56000d58110160000c0c003020000d0401c80d50b6246030000350185001c1100c2d1b80c154000d088000c0200020003a10f60a2a031541e0070ba5101c2d82060b103204100251000c02c1041c00c001110080500e81c2040005003007034092001688a8080c6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 610750260 1250 610749010 610749017
    0xf11100320090f03030c06060913030e0402030402030a0b07090510050c250f0906030b07050306033d0e0f07061b02040609090c0e0108030a0804020409081306020726030307 75
    0x702c9031665262185140c6554000400b02c9440703e1001406a41d94442250b85a009180050200c0d200b90614620310600d21352607111440030079956000e00009400060080c0e9040c4545890040402d402007034590188800390303030f82c10003241130900b44518101851901401c01030100325800d1681c0011405003528200d100b000c0d40000c044400120132040b0135005118a130301a07900001da84860384e4411000c50344589c1d1003c01c25900c0e40380c16150b5000440b41c01360140c000519040100158400209001843c01c40c80241280180c40d40c0420034000310010609681e0f4842e5400b00101c10441d00d151407180c1d10007031182a080070401011404010490350044141840b403108642d200e80010018000004007004403020034200051321113103512840728480c244800104080700c01008030b640584054a0f40c03445c03a10303650b081c08000c00d002981690140400e00ca0065041e0301d40e29444024091a07006014107030801e0540081c02440707211303992001d251100e09002400d008030603070350710214509 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 610751510 1250 610750260 610750267
    0x21e040f270f26180f010e010203090405101d090f06040f122a02090106050a050403020f030304080f07030302060907050a060305152d0a031e06090f11100320 69
    0x900245580200400320102d5000201d4503a000c0036610120741d04c4034900b110540d13161034007000196504032a10946900603042084146000d003401e81045070401c484040404456680b11155240314102548640d00c03298107005010071801c081200b48410900700010b451a4213040c2d6030b841182d518503400502d5806c5c01c0c0382c13040400c2d00500c01800003c0404540e080381c40c1d40c0f0990154404c400c010120b120740e02520002c188144504142c54041c0c800d5141d06140032b0546e001c201c00200d545610701c0c0d062000f08000b20b5409400d0110322901c0c0f0303043c40101070407415480d000c0d082c03c100814509045e4000d034410403450740c805503c4401c0703440354100000c0765124085401c0c0107a6040081c260003225184603145001504170081110320401140c103100c030400b040c10000302e0505071201805410310041785501036410a20181d0130284549400501a030281e540c0d031605400b4004150b4034141c403800000c50a080845a80b240b20040b0702d400c200c041500a0640762140080150f80442075011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 610752760 1250 610751510 610751543
    0x17100608040f12050d0510050f06220603061701140c160c0f1502010e030d0e03040f080129030d2601030c051507050a021e040f270f 58
    0x80b40521a41c1c104032035880c000c6601d4005084d82d40b04091010300103180c100021711901540680a0071782d580204003500d82401b1004200b2503410034071486c0404901c902e100c0621580381101d06000380001e48000c100c061902d2204040403070381c0e44040529905114440c00c40100711000a030748038907502c202c15120f4a0240d0020b541e0b03c10140000c008200b042c0c0b01040c250222150002101e03c080c0354101103400e00724049003a900e20303010a0031564410b01444041d003815400034120044910110780c02e2a90340c00c1125400040c1c1d521126681c0d43d10380e03400c685845100c03400e800301c0043c86451007200d42d011000c65603580050518508000c54020f0322640d0302c03c02d44d1010601f51403001d40381c025585a040c98000e80d080da202e068841c211202c020400300c0f0100b030940d00ca10b038000b405401c0d5000340b0f80030b01c204103a96003080c5040100c0740351405c2565a07144a51502204000300c00201c9401000f4084525101010000c102112082c0c0ca000001d54240100c07103020380c8803107400b8102d50034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 610754010 1250 610752760 610752773
    0x7030302031b03090a05070f0807120317010f03060f0c201c09210f06150b040b03090c0f100c02060c010627060b04060302161e02011710060804 63
    0x2800b03401c1484070000820f2007510030300000e401e00740c18052404d40d600c0a0741d4081c5030254002600c9028280d400500c41000700d01d41c07a00752000303194002d080c640c01b841030408824000a000343c004030100d282c0980240144401d03031144503102120032008120301d010510002c0d008440802000030712105400c10204001030900c04800d40320103274074041c01310400d04280030b410300d10180260b96000c3d80d624002c1d160880145442c2c0da016410020501c0c2d049030f1600c40401a15080106c2c0c0e440f0003200d04000356103400e0000400c002c20705007200c0340e104e0170328000305814910b0400c10103201f070000d441c540c140d80c0d40d4800e0202408041c0d0409000d419046c0c40810031500940d601030740c0a502c0c213000020141d02c90028a155031256002c00d5154030725440c848000c83d00c207402103805c0b43a03100f84414886540203900812448051004480015031140d454680307408a040c2e03a0f00d42c40100070505011540c000c5586107000d9201d5030f5614941c03920128640c0700f100386128040400c10000041001e02c0315 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 610755260 1250 610754010 610754041
    0xb09010f150b07060e191a0c120a060e010b0414030106030c05190b13080712050d0e010c020d200312090d030522030b060915012312011403070b0703030203 68
    0x300300c040d0350880000c1c00101e0b008201b850000c2d60048003480d4940b00c0c840a8440c594441c1c12a80203980c00e188102c940c0100e802002000b0203c0940d40395408074410212182d4107000b08101d01459aa035402c3c454001c070ba4040d0525098040d030704105d01400003a80010300101504c3c82541c00300005200d800c01c8060f50070b0b503940010101c54001a80c5414600d01846240030f448080d421a0500e603a11008024001c2c0106000b8145402000281c0e0002c0e200d40c0035001d900205242040240d400d80c0c0008100c0c660084044451031a42d1180d00740c40300c06040749410b050011005000f49048602c04504140b003244a200d02c20041d42e01c1210030140240243e403001c0d81c2c0c4920380c000340031401c40c1c090321070182070000f82c5403008030314002102c82c50b01511043c81054881c203803a403040582c0005440408000c4450a1241d0001e03806600c0c1e40c8042001e02544030a00e40c69038120b516140c90b10b81c503606c00580342030098104000030721140b43e80d04215500f45a02d481c0060b0342c1d03954243e81150050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 610756510 1250 610755260 610755281
    0x1f05070e0604090c0e030604030801050405071115042102060408131802030609370f14010509010503010e030a21050c0d06090204120b04050f01090b09010f150b0706 72
    0x22010030701260700c60042d400075120201646500c1d100c0580b817010569135000071030f0014009643e40340140207a04141c1c10080e0006e1041c2892228010030703003041e6060141c07034651400030544800810003441000d850444c544201b001588000502e0f84600075180c0c0b0000304003070b041e10700000301100400761441d6140020712140e0701c0c0070b285030b110120804c0a540b003a01d4035849040080c0c0802e49444200350282d4903d81c180c4514061469218114000f0341e0028003510002545c9202e1100c5150b000e004804142e2608040c200d055070511041014941c4183c1000d40681e01d000d1a10090707800000403185c8000e0a41000d46281c002c000300342030f04544c021182090241440180700500304620041e004590300d9007018030600c4d0320351103a40d0803805144034246588501c1e10034800481c900403007154026002c3c0090703e100f801812125425504420021a0140c065008000c0228020310403140050b680c4501848880d01100d51095841c1180c0900490386900058035405c001207603200740200f5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 610757760 1250 610756510 610756519
    0xb1903064208040501050c0301050607030e01020703060e0706020f0c010f0c08041e0e06031b01120209040527010b0d151d0c0103140105030a14100603050a03030e1f05070e 75
    0xc41d05040d0050076144103032011103056013814017007420300d201c041c1540c0c1641c4019101608081058a04440d05400e0b42d4906040d8001c0880100c00b003105070141050304120100201601440c00314000e2400c02c10740c0520203545c100d0310282d80720b03a034806015a59440035282c418000710076400c12150a22969114400c2e0262403102c03902e200380300342160000c407a024800c0640c0707a038031041856100c240d541d216403032903092903054480c2d030340c00707100d1144041c4070300500141020000720105041381c5096038a502e0182d0700d200070340740c2910b5450409540c204032500a10043c40e103074000c1210a04d120200500007000d00040c044105e02c0ba60001003210401c40900d81840c0d0786030501d58507852009843d80c0041e00f484050002c604136096164126840a0002d0a051075542c58107500b55004511802550107080c6442003a0482e5000d000055402040a454135000624000e01103802030311400c101c541020300c5459034910079040d008100c141590007c18640d179050001c462402214080a900 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 610759010 1250 610757760 610757879
    0x1090f1526070f020a0c17160b0d052404090204020705030a030c0f020f060c130519050a0518070c0c050a0b1309290a030602040b190306 60
    0x141040e6000d0507024880c603484030340f00880074090481e21040508000740c004010f20008002629421140e402507a0260080d128804042c4680d000814160740c400062540049505000b24109104654212044a455490011180c04020243d403840120644582d90725851324040d0749540e0110b130041640101038136512403110340c000c1c00404040c020403000440c64460076501c2800041c91644064224008000542ea01205a001c0ba4001005881d02407800400014503803100414000042a5003202c001034074100410300a0040950b40210b00c108003407240a0909081c02c00d407160004043d2400140195813401e10304808090795203c69000a5140e00020b4911000c0c1c000d003840d040c00700c02020300e05a5036285102a5145084800c01258482d4161905030582e84440207007054003600c05010b0755500e84900040385c01c2544418025a80041c5140340f80b10303868a8201032101c80c5c203003009014200b0711046400080c00210321000103c0a909602852218280380c1550100c40a03110702c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 610760260 1250 610759010 610759067
    0x31204091b260405030706111309020306011b080403060905060f130c03030309240b03060a0e0d081906090b010f030603030905120304090f0905061509061e101d01090f15 74
    0x8d043d07100e1180e011204141c3d61002c600c41c00d0b075000b141d010314030507590103181c0e5503c007000d88401d101c982000c82e943d284c100800400910140903d5200d140610098800d070714201207500d0031640b0040046602e0607141c007155000400040800050740d800d0300e0001451002440c0c25850291100c2661050030b2a084004c0214015a000081d144000741c003642c155031104c1031210f00740c441d000f079181c646811044e40e0303400c01407258503401d41c0580c001c5010b1081d0a40300c110380c0f0407500150004008941c45110410136541c01c01c1c901c0c0e440868600c0e0410181e1f1079528010400d0106000f101c0c442c0f081704040c0c55030720320100103840142c16503200400002a200c0212801040500811212401002d001641015800b110310101107030151110041d640d0309020001c0b0568100d006064402e98540307409a0368071010003051a001c119181c428492a50740c940c0d200341c402d500030990401520490070704c540c0c2d030600c02c0c4104595800ea4403000e4407451706410383d0402c1c183c11110031a0002d04c1d540c0304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 610761510 1250 610760260 610760291
    0x30c0602090102031317011a060a030c0507080c071a0c07060f0909150906080609030706092a1a1806070303020c0303040f1518020f031204091b260405030706 69
    0x40c0385803000e4008c01c610164290521000b00c500c202d1198000780a01c94103800500940042c1140e9425191180c038140d81c960720552117400c100302d01c15190b03212007400e02c1400135035001c02c05032034860300ca40c9040c5881a900d1a0740c0720320314003d0808110308124042d00c07441c02401e840303000e42000c0100384030340c25080f03210611420301407082e100080c0c02c00c1400038038101c020845074025903981c0095440c0828a0b2075404c007070235140c0021203912203800c102c0508030201041405816450340300180c02e00f0310b00011101c02c180e40300c0c07801a02120401c006024410660101411400143e4043c0d4503400a4101a00240141c1010041d280000410001000404a10120003e00c0340b104049440100c03100c10080701c075031140860020900505d03040240c50003188000440c0401801c6982d1480c01c2e820500a03a0000d0384821034158442e040f0b10038056401c1c50390b4651030918503207885000e2080c0741040700c18a15401811461050601150501a00b48111034503640c01c26024095460541c2d44003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 610762760 1250 610761510 610761539
    0xf1003021305060403050a1113020d0b10030213120501060e0115020111040e01091a040627050f0c0325090e060d0308180102070b0405010b0a06020a030c06020901020313 74
    0x107140114995101041c1481d080b800d40c1c003503a800c980100864402951100d0904001900041c1e000d034150400382001d900d240014042e4a40c40f02010a2115041007071110011240d480203040c1801880440585603100c050705040ba804004c028000000c0c90078000d0040c00150010010708942c407001144041c00188070614005030b42c1d000b080103040c80d0038910b80a0103503020307402460000304010803c034440364112031444c3d5420024068a01c1924000404550301a8044c03040c80060180000d800861202c0d01d010b50802c0c0d00d01030041b450902c29160300c00074002c052194030080800494980541c0c141c0e84252140542803141c8801e1120801400030705007031203801814191000014901d09110380e20507071840d8152111881c17521001002129102d6900508900e0342d82402003001285605501da40501d015800020b8a901e2003c10300200b80d1aa030454019940110344442c00603600100303242050350007500058a90300d2840040f82544564032407011240c2c6001c1020840c0001e04203039 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 610764010 1250 610762760 610762777
    0x507030201090e070f0e060c0601060201050703180206070204020f040305010e03041539171b121611100809070819080d020f030901050603061e0402040b0f100302 71
    0x201900207540e0f1080480b0701604850f4000002ca454000700d25141c05a42010203c240c0101004d04011203c80310301c2c139140d001d9025000603034403a818440804d406200b41040c0840480c0d41c0750304541c0c60340108030a0712a254009005580c0040c0340d501072100b06080c1c0340035540c007800a018400005c0f4041381e0700d400c02d00401c4070324148543c4031200c99002c2da2012070750032030720004c3e60400c0040034500031040c600304a001c1007203580c010711940090114030030001c000d100014a241c84011100303410808003070380000c1400a5004644c41140b40c10030205941d030050148840504600e036626009038440701100025070081c104c207207261001908510104d1085007014216040c0507910401c8950312030152180e0b50703002509041d0781d800700702c08070004c090b055041030b0007500c1d141035852080ca49038000c80d052460750750755000b807203c942340501c2003981221f1112941c2103ca004269807040c031280182009208941e01e4402c00500d0b141d6169800c54044020441c1406480c000c90140196108510703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 610765260 1250 610764010 610764017
    0x804030c080d0f1e140415050c0f0f070e100308030f041a060607030305040602120103030210060e0105090a0b0406051f02011112011505040308190f080417090f0901030507030201 78
    0x80d0141c071074440e1582004c00709068403481c420645100d0103403880f42c029107100180310700420011500070000c080c81c0f020020590740341907440e00121980c82c02e1007039401c1900415003102c28900b0046000091240070ba6010710a098100d84413802d59140c943d00903400200000f0020080201080390705c4c02440c131903802644c4503a40d2a021107041d0f64192822151640d000750305000ca140442c1c8aa441541d0061061000625150000c0700b8040e00040c03d90080700141d207e01d1b280900e122a074080c04009000401e440a641e5041400080100b08014280301c000e030f6565a0800c29503446801c044000c20740a450a040c11010850216503100100c818101541c28040c1c5c05005a08a108481c95003141000b0210340da400d001c0c81c42c9203007641d090101c0030000e040c0400300c040b0341303544024445005102c2c8d0b0390103581c0c0d901c01c01802024001c0340311003c0c000d1003010000441c10350340310f841000200c111020b0780c41d603e880c00214051b00b922902900201254004003c000000801c103085c3c03030003600c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 610766510 1250 610765260 610765277
    0x15031109010305281b08120c030409020903010b0918010e1912140c15060103090c030b0717010b0723070515040306020c070608060a0e040803040804030c080d 69
    0x50500c10315280a100c002c000c0c0e4490604c10091201040c000a00d040c10a009074030280c20b16100ca060b8401c41d466100071600c4880b00c10885103600b00000f00c01042403d11039406c0009200b446902da00652141c00e0420343c0005542c9441d0f0350a6210804100000300801c5503401c1c030820302d4400d001c0380f54200d1010f41c60f25070903100380c11001500a00300c1c40c2c002d406104045080ea50741150300e40c60300402080c0a4070b202100e010b078110708081c2a10100020040c6114445821140f014030800303850030f4107141c580308031100800d0074041280140c03034120140c411342c3d403240e280450307600c0720304068092007035101781c000304d1280300f16001040b03007900035892840e02030b040702c1815480e442d01d004118895804850200b10034185001140d00b00c14562130101d003850341d00d80792002603911071602c0b40c96a81050740b05100d40b0f5001501c068200c10192003c020a90030030208100281015101070203140d804400103081007016170071a40507551040a600100b80e40e4401c1e242d443d540c004001001c0750110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 610767760 1250 610766510 610766543
    0x1201020d060314011a13060807030f020a060804122102070f062d0b220203060406060f0914130903081e0402060906180406060906111617101503 63
    0x500900c01040031a84001940b000b17030a041140d183c0d010021036110686882000038102c00900c6000c00a6004081c4030742602e00d24410040400c600b0b40000003409401410f00c800310710f018031071202004103400c0a00d072000b28201207866090043e03c500755120b00008581080080744001098528031560052042e000402400d8042d00200c1c07001400e4500e94040d0103800c4e41c155005000c5250000d0003500c803410300c149012120700512071946408170340000078014141000e100f49070040120385040c0c400c01084242c014501d100c83d10880100d40540c0350b03801d40d0380c2c3e1100400360390b50210010800c21074805181c05844408220340340041c40200c1c9000d0a0311144403010310303101d254010031007490501071508211041d00142c09103c0c0b01c3e03680400c0c03030245450f02d1140380068441503c500109910344880101030b8002d00c001982585c02c451914418044a0207440082d00d20b260514640140000300c0d99140005124400240e1801e005900009966807010841034a0150346810003040c0c61 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 610769010 1250 610767760 610767763
    0x30908010b150d0e0604060204030b0a0603030503180708030c0a03120c09050d0f0215030901060605120f0712050a0b09060315040303020306010905031c020f19111201020d060314 78
    0x20300d441904450704018054810102d040204200000d075807000651400880040785086400c81d401c03501c25900042c00e0003808210b01d03080340e00141c01d00c4103008441c11554010305600014050320a00c0c00c2000214011340d10074400e0703074094005002200d03120024140310301d5990b040c40c2415070124086800c00c4010b9080c0d4050301c036440e0000d440341e82400c4d05e05024030410011000e8103a400010411103040181d40321b100700f480c0c241744011000d45074100584620701715a07040c1c1c0800280035080000b0074403400b036014883d82c0004100c00341c04043e03881e20001d56000c0018040d104145140204214141840c0d03441455100009d446a11031a614502031554a9800351000b0410882c2000000c001a1098000b10381c441c03010703d0440302c04d55407200880d103010100f10740c22840784d9000344a104043d60401004c040b41d03100c040200b0200302e03503c01180d60701242d600302408620502c000b54880d03840e0030303030f412200280f140021940c4040c43c00000001700301360b0104551b072140703024100c0801d00c2e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 610770260 1250 610769010 610769021
    0x1020a0506010620010e07050130020c030702180a060608090604110f04020414090a0209060a05030601021f1b03020309070909020a050603010e011a0a0909020c0f0f070303090801 78
    0x103015004000c142d08012080e40d544255102d01c803918146851a01c40e00c80c1d007805208014140d0600400410381410005007100c0c03036440c2403180c00e1a02d881d1889210240549180e0f000019450050b0340303040603140305e0f081d80310706c2d40003940051078107181644400030f00d07411a1140b6000b2100b0003613152500d100700c6481c601a40c00910a910860104004c904034000c1c124203000010410051845508040740603608141c0c070852015400010303003140390610141442d44600041821480c0030301280c0014054041e20421000f040b40c080006081a4020800000084500c15101a00810903d06400900040e03c08850399150700700d02c00280a010740207403401001500058038480f401e00410a0090400c01800d03a4808440180003809488500003903000e811038a040300390660510008500f880b1400c400007000410070095600c1c1103912030869001e03614441030250345c65250800480c906615482855a00e0051a00c0c868a504000480c001100d100383c40c0c8071909555040c1035401c070340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 610771510 1250 610770260 610770263
    0x60f11071101021609060314030408031204061404080306032a040e0a080706050709080705130f1b05041502030304050d08041a0a050106110c010c0201110c06030405160501020a 77
    0x9114a800040d50600d0341c980301041841100d208105480410b011907450f640080031260303503150248188070031384070784030740d17000c0d00a00543c54249001111666403058081004040500300d01180030025203030003461400040381e628104034206414a14280d90094030694801c4c03180c0c1ca210b4020b408520958001c240c401c16800740100d0318402400040c1140f0b0341300008a0240e42c0c0380c440081c0340400a03024032401041d002039945007000c0050180c1243c0c1e040b6620301d5102d41e00402003565420031024900e0443d180201c1d1888080e51a10090700000690030f0841c4c0841d07617520b03411680040a0000c07150708120306120071011141c1130781c481c0f10546001d4507940100c2c8041c1541b602820350b0031b8000f44141c451404d50000381c00b000000b40c00a850103220561240c0041100540c000494180300c10070794041c211440150700040c0000c440c21200a043c0b00c0060a050f00704d11042c469222019006410282e407490507290207a114800302441d171a0f80d21180342c000c20749500c006543c0c0c41c842d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 610772760 1250 610771510 610771541
    0x141903140f16020102160804050306010611210405041a0103060f0e0103121103030f04120314070305070915120e011b0309051912030507051e090402070b0f04060f 71
    0x30b454188948071010072400809040d5902040008220f507014406203002d01c2c0120f0003952554107007800c01d41400010707840300d0708000221170340050185000c14202c02001c1255141c0041c04e000038200c5246000c0c0e54002035003d898120701e01c92003003108924603c3d0700c00999013001020b4a80c0058801030203940201640c060400006100148180381c0f001c1010030581010210b00c10544809031a40c0e008a8004c250701302c0500a1008206a1006130100ca80050900744000901d4a40d101c1100e0300c010003c4040607114404644903d001d50b090001504103004120074802001d40003414002c0002c0c5180138807031401c04c0c4c0b041c1c0e4481c11b100d03080012020b4180c0124648038030008030090004d6580070f03107c60144e499070003001903481401c0c40041c0d10980c0200c040b150882d8020381212801480701c1c091002c1000740f0b4080c1d0b440b03030040241d0654140c0d40140ca6040f6240414000d0244540c0200820248030a01800203412030074140b0861168609001200e82c0c0c12003581581e24100c0d554044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 610774010 1250 610772760 610772791
    0x70e19080a05010b0909100e0a060516030b01050a1e11010e030c0c0a0501090b13080a0c0302030114060a150c050303010b031803070209040b180a030809010605090c0d02070314190314 80
    0xb0032401e0b00403502802e124011110409404c0d00d402b0225041980d54038083d1811483d0054215090301900c2d008074400d08200303007010230612019000880140408400555007030002900c640205030351095880f843c4001c11540c181e04c00070300c3c1c0e203902440680344180325141c181c1e550391074081c5140c01600c2c011307503c81c1401460300c40b80800d150000c807915400841204000704008604204070008940030b58028010a450f600516003152b48950160b800c0c1102c0008129554880040c1c075402c552500c080c118607a088141d0441d1030b07184040004103140030000c00040c007000410040d5008201101c0c0800030f0500000c4050750301d01c520320000390812209000140801c202046080e0b00c00c07030700c003a0122a0912945084e0514809440c2240072400030400e00140440900c10351010f46401e42e43d014071410000501a41802a5003000b40d01680016100041510902c0854168450031081c5500d41d21a0708010950044e0143e51a00007072600c0110702040ca8804020360142c045510490903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 610775260 1250 610774010 610774033
    0x251508060d0530031b0307021504060c08010e01140112020904090f11190e09010902100c020910060c030c0303020c030706020408011d0303070e19080a05010b0909 71
    0x1105240284541e51048600500d880412002d110081a03101c10f040e90198400c0c141080000c052501e403c12800c030102802000f60301d100c924000780307100d8036002d011612580c07002c0301240341a004181da079080c00c0110090204101c034a4100d40280780d80364680c0c80380b60b0b898481c03404c82e000c000d10540d5400400003a80130810b500642403141c0030850194050310f81456036000c41d0036203040080841c3e807010106465418418511142201070b034007242c10702e2110500304544a440c0324103025007510303182082d010801180003580950312031940644035140d940049030011305042003185060b806100410001a2030307503010080503040e54aa516a00e10001094034120b500d500b000204400f415400c02008824400c10070213401c03030510401c000340c0e0b55803d05039032500359a5550682c00c18107038034131b0a01c540040701206032980312580b071a21414201e9200005410350000d490340010b500c026941c040b070344900114991154a0294009000c0e001c0038505020205400325074042e25600a800b1051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 610776510 1250 610775260 610775267
    0x7080a0803042a03050c0a050a051518090c0703030b0409030c030819050a0213050d0201050306011d040c03020703020114060105030a39020706050f04050904020319052515 75
    0x10801075905202d10342c500340e074209200040241d001030b0307250303482030300110002d1501f22504405008291480002c03030b450301000c108924451281407021410114034001a0954052070540c100741c02440305915046c840e03a030714050351008100354000b0381407811030320a505260048101c960740c117030390300e110ba035007191401c40f210000540900b41400d001c2101e000d1816036406602c0c0101802100142e4400b01001c2c07038840b102d0994060750003003818915060260b0303084815a50310150a0030400d12841003072202004203e0300229040e4824648240054040d52540c00340c1000c92194000300900446440d000f03180c5178040791105d0000c1da0800000d0b203611090741205046101d244200ca100c0d031802e14000c2d500040da080c4030082e0000348852038400175030411140006000c40e040c0360349420f000c49044039140c411401403a00510094011a023151401c116231100406840c54000035500b1904c0c0ca50f4842c50f44010050f8400c0c02c441d101c00200c0c03540500002260014001000d040e200101e0a5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 610777760 1250 610776510 610776533
    0x3040e040503071b1508010b040618030b04030f11210906040806092b0206010b07021c110f0f010c0b04051c020d03140106020c0f040f020c0f07080a080304 68
    0x407207a41c0003c1c40000001008600b00500000c08803248410184c200075000c4003e490081c081d03020031504c000100100300125080b00d00b6500546490685001040300303aa95580f4070f5800104141e9541c0c2c104824076034440b0b19024440c01950301d0b0025044003400441d0345400c02001000ba04e4000042c0b0901041d0300d40003028014406081d0301c0c103065452580d5414144122031545d00340c1c0144004028a40156030002c486112000a25002c3c85d20840b00030b5856005008881441e18002102e0080d565240c0c24489500c0300750710b050014010901d08034214466010040340200c001d0f401446091428040e41004820107941c1d00701d0040007a2641c0c400540701a0050b40e40e40114200b0341240ea074a03082c2103a00c1030306a0000c160604034100d0080444034165452264100b141d001440035030703408518a08042d50403506036502c914803800080c000d003045100600355600c00071340324010b000003040c440021100e800035946420313956030321705403169075820000703101d01410030000b0001121440300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 610779010 1250 610777760 610777763
    0x31e180109180f0e0106030f02130606080f040516170705030c130518060f15010e0a0608040302010b1c0501060b04031703090a1a010806060307031502180a030c0602071703040e04 78
    0x10402c045074103004c5084030482c0c1c000303a946441c0f0003402c1c0151f0925005440320030414040c2044050700e44000242070b14030250004200c4020b40c0003040901c0701c00c220b00340300c0148903144074280310368440380d1480100150b00300001d50b01407100c00007100e140c003141440c041130001d040c0001100c4690090b0008020041022074610004004400400c0040110750301c100c5480b00d16250030300340000d41400380c02c03251301d91904020504154424a484200d00c04081b1041c50170800c205458518069016011501030a500300c2d07080828030103940900416041c409010300020003140b41c485980c00c3c010b100c0c5000141c00055100c2a654034005018020b40d0700044d80c0b0140c1c3c4500301250f992640144524904080306042c26006005102043c0b10702c1f60408021001400741ca031071a5035101c950038117102d03030440c0c4903804102d409000f00c07140f0b000540a40000c0c0107028140d124940b0b031268002c00e000d604018824420049811300e07030300447c0925500b01000650920f8600360300b454801600510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 610780260 1250 610779010 610779041
    0x50903010e060c0901080f19055703131401060e010311030606010806091b0313061103100b0f0702040f0f0507050708090f03031e18010918 61
    0x1440440d07031090225a026000c00d80382c0342d60700c1801c0b500062440402030f0140c01024404000d01070005400741940c071948450100104d07456aa80c0320050420f20086000140d501161201210f00958100c2c45a44102107140c480c000e00400040d0b0340f0100308901014031459802c00c00300d070700484141341c00c1102500c40c45420b070110061403003050079112150302a280700e101000c01402000071500b8054a0054250010012490302100081601c18060f042c1400388810001041c5140c06850154091418001e8101e03500d0901041c48900451984415542c5a03d0003610031400c840c842c0480303008202210009034002d083c030451011a60082010b080307051020011200182c07610301960383c61088400740000c0a117918045081910380090100c003c001e8104009030002c0c403020107480c0b00007800d4429038401ea0002d00400e10398890021282c030451070030745202d010240140c0081c05103000c0945c0c0a07115075404401075a42025902424a05a0501c00d81a0407000300ba07104a52080032640d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 610781510 1250 610780260 610780271
    0x705090a0c0914060712080603100216030305091914010509060403200102041a07051b21071d1608040b160c1b0806011706040f110402040f0e0703050907050105090301 73
    0x5486c0020b149102c41104c3c0415100010010319203414800b1208041c4a480c1c00e61829483d180708150400e20410000d0502daa40c1020400107481001050b0b00e6044a00325400c0c640d4403400c00200b05803025501c001e0035030800340010500c21011500c1809540d240c1c0315178001d9021112141408030300b002c11200d0940d8207100000d1140d2524511110f543d0070b10b01080d80e0741960303003172180c00c107485060062504004c0c543c054005407074140a10f00c1d40110b40c14502c0c0710206124550b03003015000d41c0b00720003210096107000700d5007116016090007292070b203500540c20b00d0321910070344210001b10b8028000300c0c04800002c40c0302819142c0301c001401a4074020b07002104a0f40e4251624002c2021a461160007500500146808111490260249485040c43c03402d008020b075075103103401440200030100600031300d010081081c141d5004108010015910740da112109055008560f100f01003c01e201ba001140c541ea000c0d12800b4094264800901215030401005594961150b0315503a0550f503640c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 610782760 1250 610781510 610781513
    0x804140a080d0f0b060d0902010309020406140a093809010e07090b03090d0507050312130303180f030305070909060801020d05060a060206070e04090f03020705090a0c09140607 77
    0x24006031031640d1040a426448002c008402000c881002040280143c909001001e85599600594507482c04a0401041c070b0141171004802400c547c0c80003d420609044000c03406008080702040c05d08001e84024800c540e41e02d00900035140c0b2040d0b4902141028000502e4261940c1030740b21003c1c003140380c50b0501c0300c1000013044111400b42c1c03041703040c151f0803000d00200c1030348000004001c1c083c00c2520341c01d60800c15541510340e5404281d0600703008001902d6000c2102c01c2c002e079900c02c01e101400b01940e16003a540382d509a0100c113800c0380040e103030003000b15118842500b582c41c03203604000804103109159800350000c00f0068210018400021000503410030603001e15406414110005031b281c0208002400c290380010748224820201d001d400e0203181da00141d00369100520b8070f0100c554009140125001f4181c2143c0078195081448494081c140c000410500712001914042c61540d50041110300319441701c400140001c10b103000c20131122081040466040340020315032850b1010a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 610784010 1250 610782760 610782763
    0xf1f0509120a1208090a05030306061b03030a0b010305070813260a09081903170c0f0f030f1506090f03011d0a14060103030e0418021c0c050303040e0601080414 70
    0x8918111851240507852000044c1d02014181e08101100020b005040f0283d980780d4481c00010030329409001e000c03c1111020319031081020240344900140d070703503d041c40d00d50301014040820800d03000c24100404142d00718811022a40b06220428200c820019039a41b0300d8000c1b481110b501008902d10465020700b0090394000784106c005a07252013100c6480c07c10600d00b040007069420025130700025011020942000c032094250120f5800004d0581d10100c0c905468014000c205c01c181002060b4500028500c10080d406045a40d6582c1c0541d03841c00000c02017080b8460486400c100b0900c40d49402d820400802d00c0e01e04401800420b1500d01d005c0c82c1041490010304120040d40400e400b2000e110b60007405801d142410800fa1680b50b04544000d0a074082c08c10b0458000d036039459059160580c040e00580038542c5c000d0040911800a0110740c0e00f12088080650700c8111404d80042c503454000125021140d01c5a100844c41d541c4900540d00c030344c4000c1c030030340340f500c1240d200d0001140c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 610785260 1250 610784010 610784023
    0xc03060c0c0708031e160c060818070b0a05090d0f0506010e070c05030417031306020d0212090a05041e020a1d0d03080402060307020708100603020f1f050912 69
    0xa0000d40c64550070385450751460111039621042c0b4582080040f1124007281404207000d100042400c16540c484610b07001d94980721500c1c0113004482c052801094032680440320340c0c015003520000d240602c840040b1582c4403001c80c8200b480e8014100410070605009402409a143c00100820441c06960f202e000001142c2d9204803041d82003c0014486036580e881c1e40c035040106483c010b4880700840d610b0300d0340ca200300c1c06400d148104900320307001c60034000c0044900c1041103920744107503070359100c41c0030359140c28040c4910050302442114413490202c0c0019648000c00c0103100d10b8040d0700d098144401840c4500401907400c080b04940c515170302d1180000e1041132801ea58400c0c408070400c00c003151610010000900ca85e440340c902c0c1d804030b82d20007020342d0841e404445260703032a01d900070180d150548580c0421024003405920301d4607040580d0014080b0782c002c4e1011580c04941208100814500c00d548001c60b9144086814515200d90042c200e0381801401881a143c8004243c2e032030a007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 610786510 1250 610785260 610785271
    0x30c010906110418091419021002030909010e090a200f0a0e0a0f1b0201140f0912070609080f1e0a0c0b0a02090a030b070311040608040201030e0c0306 66
    0x80d1203040c100104100e511452a0001e004166a400c2c1400c10302a52503124082c0411181d6586071503003d024000490300494100c0300c100c2c11242c441d8108690502d11641e00141a482903000d03c94490085c0d001000325005008014800e0820f6802c040042c00450070140c284445c1d03109582d10b010008054100c20b0000c661b085a8103044400442c00300a1291105240d1502a0b22403d4003040080140a9403075003250703c05e41c020881c0079840d09560001c0069041581103501c07a0080c0c8a80d0603019801043c46801d14040c0c034046a9640101740742c4100282e4000305154001061080e446c2aa00081c1407910720442c80498a01d080741c13a1154103410483e0b0700e031901c244c005040002c4501141881404030400c88145040c00d0541601500b280c42105003e41074a01503c005054078890741e044440e10b000c010030388440c1503101c0c00c142001c800c04a07a2030011916003400c020f061401a010780d411140d4a9035101a00e43d03480e401100034081c00c040304840c03032003845821041075500b07100482c03195 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 610787760 1250 610786510 610786513
    0x515070203040e070302090604060318080f0912030306090106081306090b0a1d06131a07110d030203040c05010c0f12020f070504111614010207060c090e07020a170c030c 74
    0x490810500c3d00941c1c6002d080c00702070602c104400320081d242d0780c041e60126080d50a000503da00d030b0b102c28005124848c10f0040000d1400250305100a0f80b08000e04100a02603e180544451468142e640c07880141c440c46d034030a8809004010103842040e106901449034584006900c01558401c007d4800c40c103401c48005586204002011009100e00c20b0300b02e404a40d010015002c1704070254840c480641008a1107070750b401480d05101440a030b003001140d100d001d400351458500030060407034a401c0e0307210034240208004070035640d21a00a980c02140c010121018581c9480010764801c40d43c01000c540c034001d502d500c000490130094041030119030b40d8000c1c100524014002c1ca0809040d41c014511940c5004000107c05041c001620100c03102c51141c20300ca01c0060503c2c841800c40703101141d40c80c0d0b0001841904000b05138100302c0c208000c1d030715011466070700d0343d900710020001221030100582c001e4182d01f02003410020007110400040c21001d140600810a05003142d0100510000a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 610789010 1250 610787760 610787767
    0xb070302010605100807120b010c140c030606090f0115110a1407050109060210151203050d050f0727050a03030504030b0a0b03030403111f27210515070203 68
    0x1c9092244c014103800d00185044003051600040291407d108000c02019469681c800f00560340d0007448400341803500b24041c07800c4070180d01d51441d41d070005003007494003900810000c2600d40c1088855a0701078642090f810307501c0c0e801e148100c3d01d80c0f481450004100000d50340002456082445103c0c545030165000c1000000038418062070b0000944c4031504001c0010000c000d056404a6515640200c0b41e1020400f80d5825020300490007058004081191180f8541010150460000c04803409106028000c99581c11902951403401319010004940001c40c800d45050880c8010f480542c0503404540e60207882e880454811300e000c0d00700320041070f40001c00340103000e01e403a440d591040014105008101d076810100340c40b8000c9200c002c0840041c00c000c81407543c0c901480c800f944110540c1594400b0782050014401c802c01c1c010000003c7d9414a000792000b07560702e0078415103143c2504000d41c11003560450341c040c004d401d0140c841e8021440d015848180b6001014000e130720700d6008544 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 610790260 1250 610789010 610789019
    0xf0c051e10062106090203030f031806070c08120402130e0304050111010612030804140d0e1002010b0303250803040506041203051b0d020c1221040f0f020a0b0703020106 74
    0x4a030b1254206460018504210707030450288280e8507204075600041c00b05542c0a1407002c01d1640c05545016041d4035408400c10005d02d46e583c03610643d028044040f61400d881d6482c082c2c80300e0070340b0040944a05001c1008803041118806060b07042840a0710714030030320b00c0b0f540e07140c400c41d907610403203002e540c100040400041d03034000b0104420a03183c000070020245040c01c1c00c0c60030a13030075100400748440c3c54001002c1c0f000103603007408072080c40403c0d2040c0c24142d800080c4250824103145209011101059040510501c115852281d000d0000e6180100050006844c55203c460135400c0b0604036a000001401d1240618003844c8540010a25402e00703151006501c0483c1c1c00311000c02d86810308002810030700b28881624040d01d500141e40e1900304030511006445656100041c0d44100d241c0d04a1041c1101c000705401940d0010700d070311780198081078a006140541e005045018103507400707008600b9480b24126071034401040d249015a603800c00013513541140c8429070260750340e40002c02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 610791366 1106 610790260 610790293
    0x3110a092304240516030c14090d050a1b0b071109040c0521160f18150303030b0a060e090f0403020c1810050a060f0c051e 54
    0x9030441c400ba01c003c01501c0161008040d40445000102400e031003445288a0ba440681d82d4080280e018180c40701d2503049050b03400da10010103249000000e1040040360020f0307104d194940075070501c0d0500301c1e02000b8664012102c5ca00104241e0002500c2d0b41700d0b0340030071801241c09401580340e505014100800720b40006412100307104c1441c0074000300d04a00e050225214045410340c0a030950340e4400c02c040703841000440485c40000388024842d40007440145281440005074100c500441e030607102007141e00a8010135600c00640c0d0490502031541c0002d4900c0b401c0c0107401c61508000706588440c000c103068030080c45940440c041610070301c6400034590b4002c01000703022032040d40745001810141c1d5004c2411840c2d900004031030608810313a0301103810a40307520780300140b641c0c0d041e2140a00b24030121900d001c1c2300390ba40c094250440060358003500c40d03c0100320b0001c0728803000 = true := by decide +kernel

theorem cover : BRFrame.Cov 610611510 610791366 := by
  have h0 := BRFrame.cov_init 610611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 610611510 ≤ n) (h2 : n < 610791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
