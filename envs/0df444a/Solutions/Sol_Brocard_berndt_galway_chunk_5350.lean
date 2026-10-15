-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5350
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:34:45.933617+00:00
-- url     : https://prove2.me/submissions/61a0c1b9-4e26-41ee-bc02-84f449f76c4a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 962050359 ≤ n < 962230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 962051609 1250 962050359 962050361
    0x4031205040f091a0d030e1302190c021e0f09181213050f03160f060206090c06030a0c030603060e03120f0708010303110f1b130603050303010b0d090213 67
    0x7a100e091500d01d9000008100381c0f8840c4104001c1c14015002d140000c54010240308581e45c00380c3d001c2e400e00c8180c4900e421b003903c401ca85500101e66500005a440c0700941c15a100c2e00c12910480302017103000d08485c40162280c0f40355914000b64681c2d1214405d0051000881c0d01ca000354034142c108418000b80b01003004902c200140c550000400c0d00d03524076100c0c403030351414020034141404901001104000c20708060131a40c00302031000d800d45011041601c081e03985041582d2046449034455901081015414071596030027240ba01c0150a40c4020301c03002030b4040c00043d1100e145555112100740f204c0c0d010fa840100110740c8144288041e00101d4915034407a04440d600d200c4110501c03001401c0e03802201c012911603296601e5170b12a507400e580f42102e185011041c030070f01a105541d440840b001d001c01c0244085c03000400a0050403d2620500407075414260781501020b080c0002440018804020350741036400d80c001250320350b000c0317150700c80203001e10b92800703074100441d040685038000765 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 962052859 1250 962051609 962051617
    0xf0602040b13091424010908010903020a0201110c0d110301230717040b011401050f0301151101020c25170c010306050306010305060402130e060f090609071809030504031205 76
    0x1004020058181c0102c00d488901e1310440341442c0700c0100c00308038030032004001d02c0c068800006152410000d80c441e80c0841c211140e2800540240e07100003c054215030780929880002075000001d00405c000c000041381c01413454420007004200cbd44031001003507481c250b1182102c200d00c1d10003c0c0d400c000040c0ca4003641001600c03294006010310000e401a82d070342c100d150340a40e600c40ca064203160700e441700807030b203400110880604110003002081c000c1102440554080c0a4605040c00d2580c070042001d4244c0034003040078019030740144800d00c1c80f40804143c169001200440700310355034103c44009000007440c1d82000e5a141500001b000840b01e000503c89860f0300f00380c07030411000780c443c010166503d00905c4000d203140d10000008005050030b03003a00c40300c40004080800e815000b01001410b046084924170300442a042c200641c00c0300804c14107400410420180001504161035030703020b03900c40c9658280c042d0f110f030810810144a141190011074000d0341d03802500030104001403040d0300c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 962054109 1250 962052859 962052869
    0x13140709060f051806160f140d0c050606040b0a0906080304090606030605100323010621020a020c12030d0212190b0d02010e0f131d01060501020a0f0602040b13 70
    0x1500c0b000000d005000d0001c0300c40b0301c00c1030000308500070b0000040203050b0f8031241201c01254100b03c5400300207508086240d08540c8203c2101410040100605141103030f240c03c040200188003400c02c0c0400c40104025401280a89020802080e03003008101400019070054840c5458480d000880300c102101420070388201f038105102e17440c0c0c7d400c011030907520640600ba50003000c2e455001405030095000f10840003038100000000c09404607030300d9500200f42e0046010807960320f64000008d00300450b5103880c0c2103400c0c01b1800c01460202c000d50361010f4007225401290440e1000c10400400c001381d40800d007045505654138034800040c280c03085400e0302c10706111000d0654151200340c0901602e0700780030002d0888075485e83c040d0011505a03600f0050709070045800c1d40b6880c1c4a44529040300b01203190000041a5141c40c03840380740003100289212030850b45403071801c1c4a070380e90200386c502006400410174080c03340c050804070003e206680c407403c00c01c0300004080010400c51072410302110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 962055359 1250 962054109 962054117
    0x130504021e190215042d020409080903010c0c0b15211516080c0715090506070e0d08040605090316060216061d3304050a0605181314070906 61
    0x481c80c100035111481007910002c0c00c0024a41014020b8507034a9281c40b006d44500f100070314243e0094000c40c0c00c03620b4034041074070f03054000684000b00381000d0140c0603840d85540340a08186041d604c401c45000c2e000b9090310420350b04035640306150b03a01d0500e40c280003184071075544c80600351040019520480100c111444581d40c10015001041c00c0f42240b003078140030740b62140c01da69514020b03039441c0c0c407003041283c0000c0b1126a4a8101070103108841545120380020882c90030320710805800140450034591098849840b00130000700e18038140d90440300e8900b0541d4031a050000044e0801c007001c43c0079200590300d0399000500641c0043e40c5c890014a0045810803103403500d004841c001c400120350303003000075510b11621060401e80000c41030701820307040000f0711010020841d408100d103a01920040a40030a09204610b008041c8a005001c141400380c80d100000808005866601030343e907201d041c4069802c603202c0a103400c0740362604071100700c0c014940b0b44a10003412041b00c3d801660001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 962056609 1250 962055359 962055373
    0x402040b0d060e0c07030c1a09060a0612050c040203180607090303030b010314040b4204020c06010e090c15030f0108011e090809101d06130504021e1902 67
    0x101a0f0300c82242c042d9440116241c900911514142c1c1c4180c0c2480007101c0703450f49048070300c05a01840d10304030300994600001c4d05160a120391110300343c41c0c198000d44444244841044002040010f1200e10181d094802603100d54640c0c000c501300c3c1e1030285c15900c1a00810f010855559440440750302928401e8a0400601d10514011002c80728400c0e81c000448502c0c0001c40c0c04501e0101031190b1042b0841040c21859210b0300c1150100c0c4c0c01c0c4011114030050f400720320104075682d8452103212030800e450443c01c0c20074042881d642d5240603c01c50441d0064180850800c10341486000c0156001600f4907210401d840f581c0390b2580d0040318008a103028070800450015010f0080c0791403000e003580c040d010036004410200c000d00c41d2b440c0464103001d04001da0303001030f107c560302c80e41a0055074071101d1422000c001805100030320114604c1c803a01041004640e924070300c102c9402540e905690060320340c0c2d00010400e03003102408458200482d4003040c02031140300031005c8018007100c0341e4240d40794 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 962057859 1250 962056609 962056619
    0x101703041d060a050105070f3c17180405010e071b08030c09060c0601030507080d050c1e0a0218191808030601210203010609080f1b010507020402040b0d06 68
    0x220001a18001e034400c03c0000c0402256210754041c1010074002c0e030382c0c0c00101a00b651040101d90300280e800d80f40140c542484079030501b0821044004034003681002c1480e4070240c0d03403022030001554588045c84c001092507443d500e100301c3c1d103040d0188040e00030010b55844894907180f03000c0485180002039140e42074101c0c1000d05400090321503512114240c119200c0000304051a04401c0c440c0360000380510070605002000c000e143d00940c0074001421440c0d081a040b50305001008800105000c0100260581e86000003000550402c0c00d048907403100440c5c4c41402c0c01c0c10038405001c0d62040284a00c18056901c44045e28050709542e9a24540c15001d10048410384585442d010000d011140c0741d5000b0524a000650344a03205142c40c2825138101d910341e046080307200080401040d0b0200052206640241d003403005400c9000c01480790000c82000030350b440d03034554043c9a034840e841114136102c2c1d00400580d06200d50080081d900d85844141501d41038020241c810b41c001e050110000f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 962059109 1250 962057859 962057909
    0x50115080a11010806040905010609060303110714131b27140409050a0212010207051b1c1e030215010510080117030d0905010525020304090510170304 66
    0xc02240c2c400310440c15520940c006481e09240104040d8000c0d031250790400000ea000e01c03601c0f019202498000408070f046050040008045021307095103a40002018400c6100d110701080701d00c14101e5203588110741e9003a484001c1c208140280d60200003070160141141d804c882c14841d1300250050000d5061b008a01c0b0340c601980501c60000030700e00b81e1880b00241d00706a00490400d0380074204a070030524441e4081508224500d280241caa507010030300c40c0801400388200302080041c0c040c0840ea1024220008105507041c000d01070b0b0008550410340208a102c0482c4130076101c0384244440703184050f0401a4440d1411600140782c81e4501d4000f1401d45030181d58405002015541e100032a8204403a03004200c000344910b030201d01c0140039a150f6400c00b40074040240d88140004200c90806d10f0446403003008246092151591602c821880c10b0750002c1030310304840c480309001c1006c2c0c44018005804014540100c400c0000c1f0002c1d941a01134000000c00031a20301c40740c0d80100880c44d0f00551 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 962060359 1250 962059109 962059123
    0xc070614130228060e0402040e09031b030307090509090f120406021005130201201006171c030b19080703051506060912010f06180c050304080a03150801060305011508 73
    0xf0035119206001805200d201303c0220030b500030050001072a02d41c541c5141c01921804890102d89a0300001d0072000070303c204490448500350302d000950950a0140002d07021303104a0003030714010800800010a018400c0161481304040c0106603245260482c0700201254880c1c000c0030054030610400940c0703071102d489007511035a80e070605003030b902d59182d004482401c01d40c000301d030140d800c40c09842041c034000e1040c0401080030000000e481440c089030071030300700c203400102e03841030f00304c44c1c00241091a6030340d4958402080c0e180025890010301c00142105441c000d020000c032401d0715000c50009000114001604d000c2c10413104e89104603030f1201c04020080ba82e9981059050201080508050516035400300e4203000105010295030300b22000c403000e69201c000800520000c0209034100c2d0310402c4420441450164a1803034070351503541c42c0d840b4031746070342082540d5502025400740444000d10042d0012000a1110300d50ba81407c5003c0d00780000100c00c401c2c4110000039a41030006009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 962061609 1250 962060359 962060419
    0x50a1a010912022e030603120c1709030703050a0602031e011202060a09180b0f01050f0301030206070602040503060c2722180b0a0605040e03030c0706141302 69
    0x105042d05025400d0040c0c00b012108202e000d12882c2c0c0c11440000100d80d00c2074800d009a560002d403a514600382000c2c0e4003004801002448400740c01180410510100d6102405095601c160ba07401c003480402d02d8011541d0003e0610701032120791404201c1c030382d0011030244000701c5000803040312540c40402510000c1c81164400e22800340c1040060600340007403c27081070142011101c8580d01d2380c500c045500002180010300781d490a50001034a0107032404068000203280a0b400d080025100030401e10040c000684965004a500700c01c02085404840142c4030140c00e581d102d042810703499185800035400341413902d0201c04500b8076401142c08000800000400c1416a414a100708003400f6500c900c0a8400e5512540c07252413401200301a00c031103c0c414200c02015180036515001141c2198004511641c100520090040c40000580f47c01074040e44440d685d420007460000700401d14002d140e00700b0025101080840300c000a60081202e000751500d80b2400100580882000f50741065 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 962062859 1250 962061609 962061629
    0x2041e050a06080702150403050d11250807021804150b011218021011060c030106020c010f0e04060306050f0a050613180813061119030e13050a1a0109 66
    0x2c100151250b03080540081107401a00e12040145200056030b0504840c168046400021925480041c03480744149280d41d200010b802c02c0780d06140c081e4240c0c141812800880c3d00c0404c2d650511210030b044030591503004120a640c60144000d040102e5421501035034115200024070345100c101d8061b850041d4016550522000319045034800200101021410041490091503006817070b021154580c540040d04d0b10380d6110b50a0f501580750210040840400c0c2070300303200400c07100c0c3d0002541da40211003403c183c8141c1880300f8086512a680e665480d070300c40e042c1080042400300d03070383c801c1d4001c2c0c2013003203010b01d2a5113503010322081e200c2c1900d0b1590840d10760310b071001030100141c1c040702c1c4000095014004407001c81d150129030750002c01082c0c40d0a0511711003000000d4008950407195a0382c0005400c00c841244c0040c81c0e414001c01e000340500500c45484030071039680c42500c042c2070744100d004004a0410072030301002440c010130361142c0450000c0a0342e4041d8026201c900460340101c4c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 962064109 1250 962062859 962062879
    0x609030c060c0f1e020a230102070323100f0204140607030c121205091501170304060f03020c010c020c2704110d0507121703070e09060a05060d02041e05 67
    0x5100c010316040c092808190301240c000000c016034400c00040020010a681c2c81c119031701e25003254107d134550311480c0e03056600c40300c4200300269160079000b0000c80c51002c00403003001c1d000820341c01c02ca46d1034046c034000ba143c06141e18a40000b1780c0540700b550a03000c1284085049241400781030b2041c110301a001c1003000c041080003801c40d8038030790740b401d5a0785490008440d4140e20041a1102503440d050142c0000c0140005132110b00300c6940148500b070f001240c420b1140305015140d2085000e0300c810440d2154140e680d4501075011111b5800004000b00404400300f94001d407500510b0384003a215044044c090300c2d0303000300e445207640c24120006c072084c9075481d6651003000301c20103103581135008540c0c10300b074a0100c0c41c00e0140900910707051011100d0586145403940140701c2c9036603075040c0380c0c00610511a103070380d21400c02000c07468103582082480e251000000c0278075500303900c11036020600140300c004600c2d19401900440c1e0160691034030f02e00400c040c2d80300f1040213002d10307604880100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 962065359 1250 962064109 962064113
    0x150612120201020f2a0106030233121b09031b0f120609061f03021c0c09020c0f0c01051611040507030606020d0806090c0703180609030c060c0f 63
    0x106501034010780001440d0001140144645400c84154403803240c4c60114046a6840303200e02414a210b60000208080c134111360002d0b0704a241c80c50010310005001610b10000766440389080051010b0030711071f64079424410402102d4110844018480d00240100065801403000a80300701c14801005032803145100c0c0c211117240d10091240d158040c60321030344101140c41d074040140803178868202402c1c0529214010300d142802c0505000d03070240110741124928004144500d05490341240c2060308510905d5805402d240c00b0400900b10000c04080060002000e078010007902500000352000c111040345059141d61041c544240880c40810003199030b60303440d403402001c00340306901c130f52030f00c201d540049802ca40f422120324010980d221804d105c60380c0c04015000d000041450032003560324020001c204d0015001e0b10b00301000300d0100e03907007041501640c0b05010403401c280d420004107503030350310040c070b01d6045104c01da54503154524045a445d01c500d45d407446041e040354040c011454a5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 962066609 1250 962065359 962065373
    0x4031b111014030115110607050f1c1a0406050303120f0702120c010501050405130c09020c0f0307050a032607050f0405041b0305060a0e0604050a020714060103150612 73
    0x44103000810802d00c401d202031050b5900658003070000c034007440011070ba6040c000303810356902c40300d140f2265104004005503950310100711030503d208006401e454120494600103601d1504001000c41800e0046035032031201c0105442c2c40c0c102c01280c050069a540384241900c9202e121400188102e1007400680001811010140c02800074412030341920196109800c00d6040801c0d00c49090751228010025840c15010f80ba4220490300001d070b2407101142c0d00d41c540c0c4040c0c2d115070820b658001c6012181190140f212001c070042c120300307803540c448162400c40d4840070103207401c6010500301200104d1200c01100d03500c4803202141a124600d0706c81d807070140c4036034000c64640400414100000710b0140c80f03502a02e020000d100101280f54480384d40080c080e13400007400d2900038091010208070311900c145d0044e802030f405650020b0301c0d480f1100384901a2003411005003080e54088440c80d0f41e0b0b5800a40e0034122030150039120748013106001d0501c155a01c0d4412500040d110002c014049140307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 962067859 1250 962066609 962066629
    0x60a06091d1b03074d0c0d08091c02010c0f0203211903020c150a0212090601080d0201150303200f011e110a0c080c060f04031b11 57
    0x52480e049000c2c081900606507030740e004888000000381c021402c2c100081300c400c19102d1030702d2040d480c41881c03100044c000da40c1243c00050b01c4500c60280305c1020026000b4011400c03510030251107082249550b0400c12030725030000e45500e02601140700151140381010300a03002280d41691002041140354680038440002044180d91601032181804006000c403003880e00305440140d0b4003900d400868050903500d40010040005050042119203000e51000c100d0450310340701030301c0c0c21186031205812400203001d000022002c1c1c908060501440f40710001d8a98101c03154441110800c3d6014a000c80c20f8820070320b84030005441c61503090002174014543d51514046400301100f84010540c00d143c54049420101c0d0b82595440c1008450388507180d022880c8165045005e101e10400e42c541c01406200380c0c200442000051400c010800c02400116200303000141c044900c1800e25154450110714181d034114086007001c06041340707003140c0d80c1c507142206800031201c82040c07003400b00380074107151 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 962069109 1250 962067859 962067871
    0x4030e03100603050c03300f07060504031d0a362403051504031205040b090c0114090405040c080609010609060915030809240309010e06010f03021e100305060a06091d 73
    0x8414450803a1100c8d45401a03c49140150f802240f41c0c1018100034003a20500030030140001ca00d894050241d0310744c8a0500c0c01c40c4c450014100c400e106015900480369407989400048500e000300c0d0307401321103098001a9030203c00c0350203035030b80c0c0703042045102c80d41c2d1b0640300043c0340d5000f20030416481d011003080d031588035000b400c001ea00e2048103141c0030304841d8129022900161600180300881c5000c21100c092280b00b0b003001c625844005d0961303c4e290040e4001944901c2e2540e00080c00c00c0001d07052f4130014a020001c1f21314a041842c05030f13019141a0090220152825a0000b403028540c0104905400c0c0041b10f41030300c9055070bd0354032169001c0b010a54010080407030050b40c60b841c0e150300c0d030030b0641d5a01c040f5843e82825900142925502005031416a000300018031072501c0404928080341da0440b140100198131300c64401c0e51a060790302e01ca40c42a40751044131341c0343c0e40540005114250854514262a449200540e0410318500610100420784182e00708030700c2e40103829036003140d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 962070359 1250 962069109 962069203
    0x3070c030c020a120606030b130206030a0b03151e13080d110c10020306032506050307030906020a050a030b1e011409040e0a05070603090f020904030e03100603050c03 73
    0xaa01c131030503a040c81110340c0c0c0480e03500d6658035080082c0002c40c020650001030882c212503810180342c002406502016081810352591154600d0b12590100080c19501070781601414807443c10301c00e0694010803503c01c007100ea242050004552030143c40340014210f0b804100603081140d00c3c001030000f000180f107101410003040100503d000c004020306035a00d500b203000940d40c1c0c9406010b26082101d41c1600705000070f03001060000500301c0c0c50383c80b0300380c841c00d2810684030f03901c014046000d000b4805003c0c00c00b5100241d040503603035000303001b41706404c0c5544017484190410000d200c4c08032041e403020382d034109501015001640c40b030110b075420080451011410007410303a000508403020701e45030b07000651003000180108041032098000412a83c107040040c1e05007500e40c04029800314200920030b0340a500020209405038091b40303112070002c0c1c04c4a2095140030340541c001e0a89000c142c03510f2050b043d6241c5036140010b10580e4680e20b080500000384140c0c242d140c1c01801c0c1602c0c110401e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 962071609 1250 962070359 962070379
    0x30c08031317070611040302030d0f030228020f150a0902010c02150a12060503030d0c03020d0501170f03090f041e050f040c0b070233040314070b03070c030c02 70
    0x304402c0700129074a0041c1c504082c1c1d540a1a15000d81100e00c0d80c400d00003624000d001c01c101603500030488400400741030412040318000804101c1c0288150302a01580c7c0c03c0176a13100e186520001c0c0030f2080350190750211a0025901480f80303642e00010070354000301883c0706000491580c425000200094418102403806401c00e81c0001d4914404400e00801860081070000c003a030341c010a06141c60022310800c100c002d04140c01700e42c4a00c55034000c5840c0c00c1d00c0d50240032483d4800c1d0304403512124441c400704079030f50f1901e0580b80454031441c8140b80074818425590030420010049031100000101103044220380c0d03e0502002e48120b421070b01051482c0c59901300e00014901840b4030800c0c07000304400491030b1510300000c03040388130780284a50b040c1c140401c800588903158400720024000c04240b4241d05944054041c509925000400302580482c00004000c1110307003110260202d403041c0c40985803a00040366250104661410020b05040c0200001c01d000c0d9540c841200e001030800317462 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 962072859 1250 962071609 962071613
    0x105271e1011280e0105030606090907020a210206010302120a05061302011205040308062103071a06040b091306110705030a020d0906090509061c030f021504030c080313 74
    0x200d9810202d52000707050001038a000000380900781c00007031000014450250051854010180b01c410640541480b00000c04281e40e0b80e294030569140420060505c0c80902e82010025150740e0595421690b281c2c0141b900c0c0c41c4080c91801c58071846080d40d004120980c0303150200202000c098179280c10780c0c040d03d683c0101103002031000c5446180c000d44c40300700e21300f82031000401035000800c030142000c3c600b10a010009501208007900244215070f184008541c070f0156892031080c0401c40c4543c0d1000044007410403901c50b968940414074030308018950f64440c0c042c0000e07200450803060740b02c0b054000140b81206514020180240036000010b04c2c503054010b039400b03a42c0800130a81d80390780041584451a0790400902c804555146020440c2c2458400c000e40305486500983c0d104d101e5460002e8980d8480700d0012100704048a504c600d04809802c01414581000c41d01f04018040e6400c0303200e581e011b1000b090700955040d5502005000759444150407504083c1480d00000d07d44100180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 962074109 1250 962072859 962072861
    0x40602070602041e050603010f12050c090106030f050c070209040201050a0521040b0711121c0f15060f020627121308060c0703081012050105271e10 65
    0x1c090041300412150344a0f101c00b414000b0100c6503c05407142c0420130041c49204101e01c10142214480500104044001e14015040c6040d0601c1160020300c442c00014407117034160803042d20300c2c0304074000700516100c90700c000700302e031050000c069000f590754008600154070810080400004510f41a414840a01c01114410200380221204500c0c002c0600080c00400803142d500702c001c5041c100720810080b60016102c186041038611440030100c0c0202c900c103452450001c3c074070380e01c405c10441c00911030001c600500c2c04030b0904c00684141040412034500a00e04400740786a52303001026aa650800321948540c41004904a400180594001051420805190b51035241c43e503c46e1101d8a15541c1c040c441101e0f440f8485650040d410700000600741d4041306d4043d601464043d60316569801c1e01c54407980140e2003490303602c1f0300c04119000c2c05019404180900041c200b030801c40c0300c900c121141400c251403a00011500700703001441c0540100c030320705c13081810003800341d036080140484000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 962075359 1250 962074109 962074117
    0x30901211a041103070c080a03150f0303090e0c0d0522050f01051506220e0a0c0906140306040b0a150305010f050603090718021c02070302010f0e0a0b040602070602 72
    0x48622412801d8518440c90140210400340c07140c3c0f80610300354a82141c0c014881c0190000262421000103034800005129170040340c0d240d01704032a02240aa5202c2d41404001c056102c2a0001180d20101113503a00c0090000e0f805070940504d000d05004900812100405016102d45811001040103065a0703e541c19010043d40c001c0c0d001d03000d28070902d02c145003900d400032b060700f5014450280c0c0d52084d03503509003922419074141400c1100c560643d244c82000f003034150020144a000e0707000700001e0b5070b09a0030024144503d40d8441c09090ba03101e2056581c03404084116052807000d20004003c1c6c28030740e01915109100900c40d4006907902c4559510000304108020002600c600040c0008504c1c2003614004140076070b1614074610385242410788500b080e0003024101d204440880208405c0384d01544c1e1408880c0030b80c4e244120300102100000d5010340d200314099402e01110240a411798450745014503903040c0039102c0c607049580d56811540c0000c00845045d0b500703114010103d09244064 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 962076609 1250 962075359 962075381
    0x90409050303060a05091e04020a0305011104150f1b06060b03070c0b060a0e0c0c160608011d0103150b010302040e010b070c0b0702060a030b030c090a0f06140303090121 74
    0xa55500e080c5002403100200b11343d000f55009452170b0043c09048400e2455040c1e800d41000000c0c0103035221440003c4c0d120348940d00140c00c43d82044903000301c8020703210042040740e52058140e604144644000e0303500b04009003080010441c40d05801000c41d012207542160140714a0000405546072070003044c2d1904140d40d01e40010360702c0e01644080204549009400080448120b403406242c000d85100c07054004102080e00800070a8140001c10304100c1c02034101c181e40b400701400c42d100c100092480c4424804c1a0f080c045000140c1d0f0303014018040356040e00d401c555040090107424004038041c0468021203030405500300000102b0341c1401803124043d02c1c400c503803650343c0c035040d082245a005080d0003070f00c41104100310040040e510341003107900b18411401c011a405141e1000281000c41c00071030107803c00d103e2400c00c983d005035035000130020511300c00100901500c2da0302c0c0b0340d100c1d040d82c454560158810440f1803d6580580400c0e0350305d4044020340c816044000b4003140a41d8031742020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 962077859 1250 962076609 962076613
    0x9030307021501050d02012d0309030e040b0306070f05160f0201090b030f1909082a0a020a0306050901021611010806010503061806060d060807031a042609040905 71
    0x40c844941c1c1e051044510b00700c800441c51096506110005148040d0f140000b07061003840c035010380240070080c910314400100c0b409031001070221150040c020341249102140005c2e011104203450f0324051061981c4480050000c00103640c07020001c2e200620002040e4045c400309203c41850560307046644000284947c5015401000380d100140c41c0c00b00c030360044003c50a0501c01c101c0e8034150805215840018030360184032000038403007c08002c05540d5005001311200082204219102c07000b030410040207c26240004124544100e4803682c46007802580180c500000304042030983c0c00103504500130400051620042c20150405009840411103111010b140800a01c3d07812036116070340300c43e003800c22501d035143c80c0002803400380325045081e46840d04800841c02c0364a03400c1c191f0381401d555020400c02a5120501c40d540c81d401480101c4071121100c601d030061510b903100503801030394041d43c002c10041d080e514138041b20340c1040c0e95080442c014010b100d000d41d40ca000f00f00d569402140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 962079109 1250 962077859 962077861
    0x708030903060903030705220302090103080318071a0d0e0d08070e0d020f120106052d030f0d080c070609060f0b01020c1f0c061103011d090c010c0614090303 69
    0x10030705080c03003001050103625410a0003041700304c1da000000c4800306034000c40c085241130118080b400420850341c10180d00b00600000210411491000440c0070741e9580342c1e00a03081c000707002000c2e0340c2c0300b890240145841241952103d036503010000f51146d5188900080f810368628180e0130b1400500c0d000010018000350f0074000040d4204040706000781040e1800c400e40c12070382e000b00d94000b007407100007030090007030b0301c18101e10030402e6010720042c00d8000c0400320340d140a580600e0880e503500000303240c028801300c03040d01103150010302c0b90784940c41c0d2000f40960108444042e9280726004101c20780041c8100030510014001d441800c5c512841114001641480350703092008844031000241d065501204000201d076031141032814484961a61090141541c0c00c011600400381803001046582010542100300d107180c00075505071260082507a0b101222494400d450300015101d10a40c2c0d0007c2809054951145089511403405043c01140056462071904695042107404545942000c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 962080359 1250 962079109 962079127
    0xf050705090913020d2d030207060906051606020304140f010f05070f0804080d0213181107081812031902250b0703021c020c0a050402120406150503070803 68
    0x403140e0020480d001d115400d5145501103079048600c52405000c1d0b014010560920040f4010004214810b9610103864041b541c600a5038030350242c01000f006c20807503200031504903c1507080e52003509000b8071042c02203000d13440e504001e40c80500140c8140302d180c015002040c90401000400d03420020000844610703456a080440300b0140101c001c001901b289505d070380b0b512541194009030401d0b121641c484807030f00480024452001d0500c4004801c4100082481c180c03e035400e1560001241801129440610800c581c4104180203207102010b10982c400304c0c2446402c101540c402600c40360034500340042c0d440c55600301d420760509a12914080999042e03061003002d0310b84990315505480301134000200c1200000e140074140702d40300c0100b01c1101703140c42001071117241c000c01075825060340c008410080d229407040031058001c141c2000c4c001000d080c40e100300c0e200e0103018540001d5603102c1d541c5040c068403440d05540c000c08001c41000c145581c082c492900207115070740c01165990008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 962081609 1250 962080359 962080369
    0x303010302040f2408160602030a030506010e1914030303100317040e090307060b03010b01020703061a09040c06030507050a050a03020304020f040c0903050c0a0302150d150627061b060f05070509 85
    0x2603620946d038810003131400c2018540010039510440010300f030100713065440d1401290010f4640640305e5028075900c071485041c1140e49804400d851000016441290b4a00306055032072206460110312500b001c102080820300b40b07400c0b080580160465949040c0d921001c00900301c0b002c1e11040190b81000800320f0401c40144a000640074080e402882281c00800020f0f4a0341400d1001800e42600d503000401800b0000e001c070b0441c40001811840c09060034205003560214500035030300424a4000410085405142903504450083c1d07a0340d8502500c12408a003e034201400498003e0b4107408100501e6685008004188041c1c3e030300c01540902d141051880c0901d01c84099004442080c01070004d038035406c0c4c5140681040c81d820a541e508d900d04580d00a00720000808484004c12602187d0968014010042d021011900e24a400d03c44804811008800c0c451040481d040c01e41c481c00d401d208120130041c0c2400381d10009824554070070303100c0999000b20740d03010025100248107130151601d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 962082859 1250 962081609 962081623
    0x2093301110712020d080c16150c1e030e090403020303161704201f02070603180f02120a0609020a0501020607020c041116050c040509120904380108090309030303010302040f2408 78
    0x91400702b0518940d5201c800300040903407408154003681c00185820705000340b030400c011500240085082e13160904001703407240c02c180c4508081103184185031108901c102c0c1140c00364100c0450b01400c5444a80d0381035885000e5141e0a9a00e0140c0040410903076240340204d8440442c5c482c808845822412000b410403501e81c00403403c0c545003400c071000c2c05070000040d01100c1d13405207a544488180780006112480c0c4030b41146018480d680a402c108040c0380c21401c40c051081d51410942900c030001640c50315003c5408000591111303140c01d4051400f50440c1254428161041c1c2c44c0c10001185860f980040030026a61544420010403181c1400d119803a40004004042c0942c0207050040d0881ca1050915480c4500d84440e107807100f16a1062001c40402106d04407403285e40f011141390000c13486030050702d5010034400c00001e111248088111503403884014040c61550782903500308030040c840f60a0403d00c1030703907851604440701c8089281c60049036160400002040c5000007c62401388 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 962084109 1250 962082859 962082899
    0xa1b031e020714010c030905152208070b030708131407090e0c03011b18050d0b0a27021302041512180209010302093301110712020d080c16 61
    0x9443c0f0800c0006c00ea1192801d42a11000c450202c25004540d054132214010310f148900c42e041002c1c3c2040078421114021402c031042c80c800c0d07484041e940c02048d4541e0004580040102d000800091098000c084580880354450000103450340702c404069440e0045507008841c04950780c504840340d001040200c410500d80450007400001400c95108511010900c1400240801d042090708907a541074084005040301400d8160101120705241c54280c00584010750340034a4214046c81e6030400c00803211122080c074081000b100c00701c0d400e0080c075a0720380000e0f031040d030f0f13090201290402940c01c00034441011551402804a00036400340d0841d813240030a54040c4d10300c003000d4401038803040c01c1d40e0304483d01101d10000b03558505504020320b00312031103d10101d415074010701d85503888100030140d034003030282c0e5002ea01070103002e1929174480140c007030b496032224800a1900149401c03540042c0083c80b41e05058101041c0d14a4945808130b280300b0032207c503603000c1041c880e51a075100f0340710000c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 962085359 1250 962084109 962084117
    0x40311060c0d050d06030615090f05010f1401051b010e0d0201050f060402091210150b03010815130b152718071d0402040507050a1b031e02071401 64
    0x1915054001e07540307403002601101402000b10b44441d070078445502c84001160041e00521858525441d148035840880c018030b5140c034640070510701c41790301c0c034401c09040e501c810baa01b501d00fa0401d0b81d03100f848070981901134104401007090b41008960500782d4030800300350078008030700a0451000641000d40e04100d05086a16210401885076101350803580c214805681c0140d56143c000701040702c1c4c00051821245078030401c03d0003c40b50103183d204409101243d000c916480e5100d41c40034031a440300b13206040701580a00e040910b01220303500390a070000c0b006184070307008803415914140602c004449010044c0d80003a41c65443e07040c0400b1503180b084c00c0036091640c2504000098102d0305000c0c1c0301184007401440005ca41d9a4200700d440090442401c2000e131032200540d2442c003404085a00720700a138100408541428000c4003540c11041e01525003000c2402c00940300403144017030748800c2e020000761100c1140040a141c1c450581e059a40d800f81039503a04007071101580300c1e03c881c1154100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 962086609 1250 962085359 962085367
    0x230108061903030e13050403210204050a030813030222270b090f011a0a0f030203030403482c091219020d14070212120f04031106 57
    0x7510004203000649902d403c00002e02c24009000c0703010081030600c045030307081c40c01d42400180350b04901c184c0124105101d00326a0b445601c2c0d16501a400369110312a00b211943d40140f00050400c0090940f601d01400740c8400c490366900025541d8000c108204140f40851242040c0340c00280035143c0720018150126595070703401d070b5203440d00241245010300345c00045c102244c14602d041c04000c0015440000a01902c448510148204000d802030f0a100380e044070350001b5040840c680c45022250011701650805266480300205060108404069610b9503800c4a2001206080b00400c01000402046031252000d204031050001ca07005a5202c00903c10503503021040b07810081c1a2101194007824039071200642c840c50207602d240b0240600d00302064200000c850525682c9102000d54215100500c40c0701c2c084d6141d459400c00070b8042d2404005d40d03c0542440d001000e18200c0f10012a80f12465407207017103c0b69008007006e1f07241484005030400511140301c110810403a01116010320b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 962087859 1250 962086609 962086639
    0x10e1f0605010815121f06080712260d060312080901270606150f080a020c0a030e0d020301050408031b1204030c051203090a03030f0911010e0a23010806 67
    0x81c4582640c0145c4901c1c520400c0c0ba401d0b0406200102d0846001c8100c10103078010500c1c1c040144c009405210304a12402500040c030f04421006041040e07003042440541081c0c0581461210244100b8003411500800180001c070550703206807001076000700155401042d1509005011400141488503140c1c104200e8005100c80100d0541a400080328a61548001854208060105a4000303e9148031801a80c1e240755046140c0003110005540c031452a41e4404402d2030032402a500d007558250310509400001034010940400740070001030550f80d448900b0303030009003911402c50317045401c51404428820300d1190310a180e03004010450500d42020045442904a038100600243c20031401c8183c030014000c085c03180e00c1c007072110100314980da0701d401181d10380c1d2481100030440000b4035044640318a100c0034800c26030840c0e444020448440301a0004446104900c031156900400708000015924803042c0301004100206290b444c8060800c00098441c9030000d01079070040a120840c055 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 962089109 1250 962087859 962087881
    0x7020a0c141f120b0d0204020d06030b0702060124090b0c071502030406050d0504110d0b06010f08010e0604050702010605100306050405161209030201110c2b050f0903010e1f06050108 80
    0x59140b40e800c4000030720802c2013000171428210150040d401ca44005841d004540391900001e0550b40a1301d4080d8981e06c80d00700c12a40c50501344170701d01c14600c0380b98800c080c031600100c1041c8005070516110380707200d4551888240b603a104031303186002d070385c81048100103148521207580c11401c4e182c009141084c1c60302d00050554801d50340155238482c1d50307000080c20441a00410000500301900c0c49a1203601841d1103620514140c0d000790110341c10280c00e020091142081605030351850030515419182c50f1b0510003c0c03e006400300301555210980450709880d4044a0745d425503541d035000c545540f410041c0012201e001c1c01c00780e540d180d209242c5800940141d140391a117078000500060030003170382c24124010550740510400070880040c648000c2480081d510165150380394411040c942c807034000f01e404414030304510b004200b0a0010403002013460300986482c86010f0000b01d440400c12017624244ad42c1c0d08107001800e222819414060241441003001503e804e013007284443c103002507121 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 962090359 1250 962089109 962089127
    0x10503030c07183210031109060d05010c09031a07020705130605090a2702210a0203030a03020a17090c040203130615140904080a0807020a0c141f 64
    0x948128560b010701420180c595200c000398a1042d14100b0500303900c0196213079252498806513102c1d0402c0e0003c180440c2d0b0320340f40c034000c403075001e10082690301c0d50304c0c1800400c00006002c1030340310040f890f0003008100b080c002d5681010244d640d12289904524140301e00c00400001420312404500c1009095034001030407109540c401c5442c5400c140c49a0401e00180c030494001c0b54000b06240b082c001034140d0351b002041c4542c190140e000d004020b45030034140c0c1800407200030790b01c122028100140304941c411aa49501c2100003500c54406180c1c0120346140e2058061a00103940000e01171807555100f0782840e800364002800301001e007092031b00640d50361002851180306603030020218140344005807003488141d612070003d208c200d05220354007003214154810030010142280f40a1074030b203001010300e07105541c0180f0ba01d081081d20081121004030060a00056100300580a008509013804460003401401d040300100c110711414001509901900b8144060080409800d000d8101c0042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 962091609 1250 962090359 962090369
    0x60305061c0c260312270d030f02040504020f0a1106070c060522050c040f1e05060402040302061206040c0c03080a2d140c07150e0c0603011706010503030c07 69
    0x200c64803d032020141294410900d507145450b200006a00c0590114825041d00c5050400200c18940c4650f51402200c100428a800203a03080100641c0415000707504c50401c0507180c100c018286a01d60b008038040380d100c00c420402074500841c60030f03107807036100d02500100c035810806810542400d102c064484a40204020002900c44000451541c1d100c40d8168501025140d403000ca00024180b00d500c076103012060714040c5061420300b000c1c12020b40141601090202d1407003961400e00e043d00f50045c803014268a03803040d0208000005a83c1e540094025070b40d01410a003020b091030004c000c122501c2c0c2c000d20091195020b0a0740c04640c0080382c0365030000304d00c40c02260703036034580c0724524100042d100090b100449440c28140301c20400e5024001d06500b44036049110740303a010000c4414000c00740c0043c0800d04841289217894840d8101c001c54560400c101e41c10100014001215a0026000440e210b202041910321049040000900500301980614500b4640403203907a00d03100d143c00b070303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 962092859 1250 962091609 962091629
    0xc0320040b0a08071806110601060509010518030109021504090e0705130f0e060a0c0e0a05030319032c060a090c091a0a060e0a080c090a05150a060305061c0c 69
    0x940207070017032074079030b00c03201e4009841e1048a1b2960f101901d0712100b80d8140109120710400803c483d4010710441c1c1702120b0513103501c0e05000c051000d4890030025450f040750155200c2107030304e0058070303008407062021440964880e03e40742410b22401c21252a42001c100603880b032041000151503400c1e400f4500d02c07501c400800c40d107410f05002d60161010b4044000c443c4110010044600000d41c4050701c5c0c807241c0d590f28804000c00c02c0420003448401d020f015450f8104000800c104250100c800300c52030040d00303020070007002d8410320141f2500469103c1204542da8501e04a40e82002e00000780c0c41504110700b0018401c7c41d4640f0000303241c450041e4038200769182c60110001c0b591010b44803402d0001010013521684408000b008120b40540490144a08a401040340e1001151000c0410009020220f00b580ea14103588040d00b40540172003120f41c4c4544c4010f44179203490700c42c50040e0290f0b807400b14541c14072000380715030410042518281c8095101d00c001c005250218000e00f15020500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 962094109 1250 962092859 962092861
    0x52a0f0a0c02032e0b0a03050303010501110f070306060510030510031203020d050a02180d05030a0806060d020703090f211103013903050c12070908010c0320040b0a08 73
    0x20203c0d16007200c1800e840141c401060203a00c0000d0b00401c0d108a4206014003401460858002c3c061503e0103400000d1803908140014042548030b0b22182c0300c0c0d07641c1107080350a40303981c41114508001c6a40c00c2a500c041c0c0312407040c030080c200030300c2001c0d420245103000c0000d0b00e80714050521492203070100814000345070a464034128843c2e01601c0e0101d20f000c0c070403c01030804540e5503000350f101103802e20044400c030b04010854a008102c2c150416003100c00355103041d14042c0100d6594200802d040c0e8010b20501446188034650301c09001d50b0340c441d40b101d060072803d1000d8030480e90340941c02072240d50a00d901650354207003203c03070b01c50072543d01c000c80c980c0700165a0002030142c02d070041e070745618140200d03c00c8404041e0354022306890b50300c00401488800781104c101d098420481c0c0c3c0340030340c040c100686a21050352649580d07000f94545801c106c03070740d1101c8209013074509412140300000d072104200724014002c031a40f040c4101300241c03118503040c070b09404003180b40103445a10042c010b03044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 962095359 1250 962094109 962094113
    0x605160c14010b0a09060314030f12060a0308071202060109020421060b06070807110f1f020c040606030b091e0403050307140f0406180609121401052a0f0a0c 69
    0x50003e100c401c00042002c001a9200d05944c8020241440155110f603041d00d16001c5400021080320700d40ad840e00300f15440c0c45003801c103010802801504032074019078800800008103400502070030850b03201c0c000c4100b203081042c50080c42d024043e0003500280d0310400040103050b00700c007459401c40c1c24200305000b0711005030410030010500c00c0c644c15001903001a1101c00c0118440c0280700b81d511070600a12540030680600c01d6600c40d00c070000c0d03000f08200003503051441441505050340d814620466014074641000301d003d07201d2039407001010a80304e40c0d1981e001c1c9401c0e00099800b42c01c0c8401e07400c070840030441e04448148064030140612030000042142c0511038880c1095008050208075550302001209178159407040c450800052039800c540c82c0201c03079403c088000c030303140356a8050046060140f240010341030700e80c0c00c0701d07109180c00200008200a006482c0301e42c407a26030318090140083e85803060312410200d49442e0030410000d12074080001c005481d000f80c11458100c8460f0790074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 962096609 1250 962095359 962095361
    0x7030503070f142a0105040305190212030a0e0c041a0f01050c1e0307080f030a14060906100302071406090d210c0509090f1803120c0a090317070605160c1401 69
    0x104c546a0010750900c0100801d164000c002000f0002142e580a0040810790504030303110404001c0c86007d08500300041000218140c1003104034800c401c0c180d5510404480c00a0220360794204140c040400c2c0b072107008014074145d4102042601c080c20451b241403d12909282c950300c41c2c5520400110103c490b40424002c100141c40c91941d00c800c50030340c3c9101107215815290001c1b1444030411b81060400c185056240804c03600a17140030300a09010340300c843c00c008101c42d109040380c042507400c2c04048049820690910f01103c60803010780321606000c0251801e00d0b00c19580300003840002c48501000e00000200c500036007500080000702818449401c44042c0300c0c1144071507120f2449400d1043d00342c0c001c8075850040b0301c098020415096403084c00350b00c0c2e014841304003120040601c000307143d402228004041420b05171900040b01c68507550364490b1004010b50111100c0000701ea404200104e91013000e8100c9064440040084045800200701407102c0800a103000407035007901201c8402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 962097859 1250 962096609 962096677
    0x7022103071b0b090d03020414091b0d0e0f0d080403030b010c0c09020309060a1802130e01020703020a050c01181401031401141e0a23040207030503070f14 68
    0x201070454020140a007001c500c3c2400582e41d941c054029910f10511310780c000c0c400c5800311621012080001500001040503401d0001c1501c0c2c0c810224801501c41854030b0710091507040800b00000403d41c12032450300385040c0ea440320301c8243e0380c064101903000315041041030340d002d81e1614001c034004c00b05000484641d00b0000c2d00070a20701d140000401c2d065101d401662256100300125041c5070ba4107511a0180c2d41400014448156040d000001504040c09013818088101c000840c0340098000031508980c0824000d03401038215042a0080000c1402864888842442c20019105402c903080600c40e5091050210091403000b9510301640290024800c03000a6004442550b0f91b45000d102000d40000c1545e10a42d030340005000c102c14a5001000d0183d40949688140c030704100031402d080201800301040c13204500511031031a5164001009014482d90702c13640c0303d0800582c042c01e4000d2041c946420700c83c4c0100f2520107044044251800f0003055000c1042d04d42c0e0104c103034820310b00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 962099109 1250 962097859 962097887
    0x1203150907110a0606080f0705010f0516020307080a03090605130605031302040c0806150711060a21060e060d03020c0103050a151205071d01050130060e0702210307 72
    0x80743c01c2a414090f0343d80c44682101c0712001034800d41c40d255419251581d01500520f4082030f101c4d40007450f00d80c4100003406459035100340e4440c8041d080d400003490a041c40d84410702940c448071001c410960311040d0100100000d0501604040e03c1c51035180344002c0c00d0145004010010000441c4d404003000002d81c242c2e0050300403c896040b1000041c60488221102400b07103071210742284404500104594229030010220403020351080c080103055030200000d0001c100c845602e1015101e1004600c2c444894502c178002f07000c0b4074044a0b030301d10340b100034250751052412040311400f2940202d200d8102c00000d10b8001400d07950662904c00034501c650351b035070282e4100a00400c4005200b4066420240a00d0841c0c070b40e240d81d03014488075207000c000300b402c0110712240104500d5000300c010032100d00008150100300c00007035042d016044103481010901e035455400820141c0121003005401107050f1001c1c0c487c01146000500807400800b0f10194400741c00030001e204d00703200e1401c50300340c51 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 962100359 1250 962099109 962099113
    0xa0315060605430b09070b070305031308040e090610090207031704080c01022b050714160b0a09030e010f0f2d080906060a030f030c1a090d02120315090711 68
    0x14091303003800708400c0c2049070b620300c462181c0c480214110a6090980304403039410b07521907145580301454505c003890700001c00c440c00d280c148000716403885030708005032040d941000100054604018440301c010081c1d84070701c1d925441040031002095000803020104488000130303110325100d516010f0a5441190350300032081d40701203100368a4030b200100100c0c503031101d9882c0c4010001c034240c5110469105940c00c00c04245c400107000001c0c0d40e41400707003104091220030011a5500c540780c1132229181150400d01a99444020004240d0842c140d03000c481402c0c60001c0341402c0440c80506407081100c00c00d4203011584140c0090700b0101903500a0f00c03100040310302e1035558004409000708000351885003882c01194001500d5003062410030701260f03007003552007150f02d40b1601c0c155040345400700161442d507072014180c108040c603011003d0041c08000020598200c10010083c1014101c0e40314501301c043c104107200d404c001e20841807000050881c2c0305201e54881840681c7c200c0c60715605140c01c0c4c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 962101609 1250 962100359 962100487
    0x9020409060e0117030313050c1008010302090a1104050118170705121c080910060303080105120c0f0f1c03031b050309101a0a0315060605 61
    0x440e098000c0350450b604034151200e6a6282c003c1502a40b44040075120154400e00000e80450890f03145540c0850140c015100c9420812001c5007125810070820408604040010002c5041c00d40080ba40400c8215040290403028110700c03189102c0c1e8812941004114140340c2d031782e018140d0f251801000390002c0c009540101038505c0d9150801881018890b0260010902e041900416118603080003407111842100340d03803500380d0717402c50b02500a100920484584800d281e00382d104d800301540c0292514905580b401003046a0605581c0761948513030801481c98410391600402c8850060701124410035446112000c200805d070196001c2c0510b0080001d511300745501a840b00210061a0b440501c0203090107006a41e584000d482d1545181e00524000d5940b8015511682e48075006001e5081d100301035800007802c0d480e07603400a0fa0414400762480b060025948a03001c001c1009080050070b0011000055918800c1741e00c5084000000fa030304201e2807001010042070048045e0013080b40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 962102859 1250 962101609 962101619
    0x60405030a06060602160312080c0412052b1e171006021902090414030f04060e090105010906050a1409060a05070c080c0a031415130501060b0f030705090307090204 72
    0x3d40118407504025005060303120b858240c50809000c1943e400044440400d22081812281800001c24070094603030140801b180058120000d8107400d405400101000070100001a491001c50200101c050f8028130004034501d0b04400c8820b2071954106954062400920060b20320040f082d103842c1041c2482c0c07007049400030203064810196683d03582201c02aa484003040d45048003107400103076206d000c02000800240354401f814902d201d204003924101102d90b05442ca030b40e00070390080c2010071a803010200300c6040c058800d81c010402440e06c0800549041c00107441d504c581c002040c104031154007070080b0b21708600115130780000007801103941c030b48280341c000300b054004040480b00511036440018011000080300510840010018442c440c40e598455a903580e459a8864007401000a00d4400c1480c40100501c502442c40010480d0280d40ca805030071203203590001d1040032418001c1c10412100e1009480e4498940e050284c0d4500300700c80001d21389601680105081c41c000200070070f03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 962104109 1250 962102859 962102861
    0xa1401090b1006020d0314010b071410242702070b0c0c0f01110a0f020f161d0121020f030f16090519021e13030308070f0c02040b060405030a06 63
    0x3048036116402d54108040f0340783c00b20141c410984118540d0009500140309908001008081c80c8bc400c001051440c2c40b1252840c1c01d008580d10080303800341d42c43d06602c0900e4882150150b11904010204002e1410000c9426040078034055403001c0060341040d24400c0c50843e8101d850258200121300750030701e020b041c001201c0e404020300e440c0a01400c0d0540350b001c9014019800c244d40250b4071642400703a03601d0111504010013017100304511a0001c0c40d59804000d004c454005a2023222044400b030401c044440c841d48505500e08480b00ca50004102485100800b04103203056005004841c40c010b00000b0000400c2011559060160800141e28560300180c100c0b1403000b1541026051f9564600701000c46808554503103120850748080c100480071580244030f11001e050b9880540e41d143d074241d0161b60887c002a0f545450703104024000d041c0c0280c142c41d4800b55518041155586484004180180d100c03c004e016a865000c0a0740d20303a51913082d00c01810001c2e0483d880f070645400e20b04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 962105359 1250 962104109 962104141
    0xf05070602072003030a09291803070807080a110f12011406030706020601050d240e1204120209090709020703030501051e030303010b0a020a0f030e09010504020c0a1401090b 76
    0x20f48000f4012490401c141004019508001c80a840d050402442d115000c080c040e0340301000e0301c404201d0060101090400da0181200c2e004081d405a0a90850410b01d45042c1017908481101d070300140c03003003100f490001040c1540b298403400c001d51013100580406d0030103c0600410b948150f505818011044d0154012141d0100703080750340c0129242d50301450b449100900403440142c205000501807400c100c4007040c00c2610800503103501a01d16440c2110b80420081e500444949540e0f46641c2401c04012400360070580028031850b1906d4180300e01440548503500900030320a41000600c2e11809101031320041030001c0c42035503219080c1c90028010202401550711910049101031410180d199003981ca00c0383c0a40191f29603404c000344541070381c000f91840000c620a07103015038000b030514801c24140e140b00c1e46a01159159150410030700200c1600b2a901031403050180d13440c10036001908200741a0402c138610000032a6150042c09040101c5010f0603910842052058406080e0350305 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 962106609 1250 962105359 962105393
    0xa060302120c0a0509010804080415180801020310031103070302030303010b09031506030316050a301103310b0307142d13090b030f1c0f0507060207 65
    0x219038a0781c90319446220340c0140c50f2260300082d41800802184e5005440e081d412034014078110f400d040c1c0e640040f80340b90a0380c01000c0000341402c2c2a464194954070680380103020036000075429807800804181c0f00c1400d911029011500b0031010304020b03282840540c01458026050b2581d88d0784603034103505260310195400e8040d01c15002c2e510300c80401070b01140d006000080146150003d542501c04688a030307264240c0380c0340500c1585000140c142d840034664440104074602c00c001c0c1d001c00842850150541c2c00040c401e03408507000140e1b10100413942c404001000030f9030801108510001800080f981c4c1c2494100b0030040425804140400780d84500c00c0e0703039100a00440303108884034080c01420325001003a02c4c44140e0704500720186480d440103900081680e4145000e40c0801070040ca000d81c001c0340c2c50b641d01d1407494041c1c04c00327001e0382c06600321141c0103101c0000e0300c01e07490034141a030744152402c104e2405e0700d490b145442982203404480e0050402d5440d9885405c02d584690401a60 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 962107859 1250 962106609 962106637
    0x302130801051f26100f0b1e0306071805060f120c070c14040e060f010303020d170a2403050303070f1b02040e100e070f092a0c020a060302 61
    0x30149040050880e80b0252601101ca8480d6412040844401d2024400b00d540c101c1c005c60301003445c400c80a1142a02208a000001c10300d00d5000d41480351452201e60012040d0890b107141c0c4010352070002e92150000b0041c40c050042d03245030300c0d8903804001a43c0215a10800c00220300c008040680d02915109040c00200c03200c680320307032000303008c18480c1c181d00510380441444104800d40640504142e44039000d8004113a4901c0080e0b8203081c4982240d041580c547c1039001403090590400c1014074083c1139042100002819501c0b0040060000f401c20002c0758443c0c000c81c0007084000d518040b04241a034a0308030b440c1e141d2038111740300c1c4c2048502600040c031038810841014403d0700902c95118450032565145480d0b0780a2002800711148070398158460501580d0781250f0b140308d502c24802441015010860074090170809840b030325880050640c0c101241d400b03080114a550141d0f00610784c40c41303d40c403420507006031200803109401a61005509400180307003601034004207880e640d5021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 962109109 1250 962107859 962107891
    0x308060a0b0301060212180405012303030a050d020304050a05030f25080a0e010e1903051e06220b0c18040618021e0301080307031101200901030213080105 68
    0x200300c00790b400248641c400580c0030300080000076807014010304030200860b110310442e600190205050724020b0703014001c07044240c05140c4210414110349905500120701440c0340241d51701c0c00500074002c41c1c080c8550f00d030f070020110f004c20000b0055142c00b0799002007642d40712200901c00103a55000307c1d10310170300010340c00841c0d400508880c1905c01d4440e40404c0071800d1500c01c0394221000781c0c40508c1113040c010745110f0135100d07035905046080310f8603801c2c1d000c001071030561034100d080011070b1003900800c1d4a2442000100f0303001141c050f40c0405081059200c0258400d002840e0030a01c1d20040d00300d0a000c030a03c9800c0380e0007401000c2003082004804002001c06081c40120f41081c8280880010120010040100b40f41c0080c01d0071491155180c2c0840d488549180c0c03554001c0c0e01a000b00e51001a000007055084400c0c4034104441c0350080049041c0e5a05041030100070044184004e400010b070740c41c40380e020b503066030790b08110440788000b21502d4190301e900801003581c01c4100356522003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 962110359 1250 962109109 962109119
    0x309060903020d0f1b1e050a030f020d03050d090c030b0105011115100b04090912080c030a02030711061e16050d050a270c090606050a0f09050d0308060a 67
    0x2444001207a0b80685200080d420781e494444c00701c02e60311022941508100d10b41c1c41034404035244280500401b0040f0316140034030307000701c210b10481da038480b0f8000d01211100f007002c2208446c1c15139181d901a43c2c0050303d50998070b07003200c00c0d01c251500016268548440d41080c010020036400a80340305005401c1c0c81c2e40c84200545810300e000d088882a503000d10310b4074038030703080c011072054100600341c1300e4846080e12925600016041303608010000d5554140c0201482041e03003114030404d42c0e506100b0764506102c05101080c0c8402410014686c0c0c0020202c1d5845201d00148041002090156420f0b400c0403560345401c50a000b9112034141096404207a0326042105d40d04440e414540301d030352034109410010340141500400084840380d48800380f82e0101c40b84001c03c5068840c9403100380440c0728601d04118038007059002003c603185061001e009041d0408100d600203550f40c03e15951060340828100c0341403180c0d410003500001503501e0301080541010015002d140111a0310951903224 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 962111609 1250 962110359 962110367
    0x3080906010906081b0f0a030803100e040521090612060406090b011d0a0b040617070203070201170402210c031002071e0303060e240102010b150d0b090f04030906 71
    0x84c0c0645104c640100d068900d52030328602030010f1100015000016503619000010340aa0781b0741d1054800000000c10444100842c0a0030409804030548031409414540ca95a69414552a82d0581c0d4885801813003590407410017941c04441000380030a6032030001c4080000991410759245d8000e40c2002800b080340105030240f24004c00d030603915217103030411368426030540b071800e030041c903070400c07a60000030502204040040002e04480d88541c0d030468411100e05088400003881c202c215003085c040840180c2c0d0041c40b40c0d000981d8441001e0346a25980005043d50b8840008010501100302c44500010000714586052103400c4041e900d0001220003500164882c0c000004d12410250403d00c2005d2411803913014154020b1800154442d110340110609010075259240724101194a2554001040c1c4010131640d000380b00a00c05400d020380490075565200900140069011980305010640d503409414010001810031046090602d80814440810b07a002d0f40003a01900002c80e40e5401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 962112859 1250 962111609 962111621
    0x120204081f050a052818050303041703070206072f010e16150c0f06020a0801030209061206012d030c031a01140402091c0b0a0c02010e060604180807030809060109 71
    0x4888034004a5145d5480340410803130144070708528180c1d90150152000802d0304943e0a00e446000196a20308040c241420744c005042c0c0104d2b0b01c050100100100c00e580072038050f4024681d810701e0390b840b82c0b100f03500318030f000112980301d1400c50018540740501c610542000b200e82c9210000e4401011130201560300e451201d0040c1c00813401804400c0300c040d881508031000d4540115140907049a055075181c059a100c100300d48000f035481c00051003945002c00e51582c2108044600311554554210540e80380d41051195907580b601d51403000304100174600414860032a2801201481e03a228039107540c5220881c08155905440302c0e0300c100c8102103040380300c0e0584a0300042e61004140c20010040654414103c254020236202c6180034401010154038440702c1c03150440408620713048241c2c1081300d103500780d04800c5a04000720301c4684c61020035915084641680c0201d0910b4084000c2c0c540c0d0f0070340e24030007400020002080e10605d07502c282084c2c001c500000c141e988a0340d81c1c400e410103640e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 962114109 1250 962112859 962112871
    0x141506100507140c12010c1202090906040914030a020105370507030f0203090105090d0201061a03091608070305120f0f0c07050a06030e19080901120204081f050a05 72
    0x300c1040314102007441100c08401005007582204d00c031120f00c90100740403c1910130702410aa445003141c1203410303005981d510800f03800740c10450809039000000343c2c3c9845c0182200c0c1c01142c0d200071650a001c083c0a40711a00e103161003c40742d0b19010000024000d020881c7e024503111117811a409c0c8403503501c941c411b03012588030401c41d41e50030010501c0c030050001804030400d069581d41151b0980c45540080d500c5103284000014161604e019003d04094000380202e046916121086c00600c00c2d5052100c02c064800e5400b64417555255415441c00401d144a5500092008000584030320300140318001d0364407400a4580d100360320b848013641c80c086c2c280c0c011420502031007400080c1400702c0142902074122001c64858980c1c660100300341d01035a400450010f502c1d005640241038042010f11640102c0901c524544007058a45502030701030762121a0402030f014203400c0d0003084070380686018105c00400d0301d070010700a403030901002c01c0b580e245260b281d0419000550343c0c06284141031040c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 962115359 1250 962114109 962114117
    0x11060612030316020f070303050703120b06040627030606032f0103050a0b0a0b03016005070201110312010306020f070c030803060f090c0d02070f14150610 68
    0x180b91030000f07000e00c440c82c000c2d601c21442449859050900f04002c000d00030760181d00c800d82d41c0d84281c20020442842d440f143c2c0606814603c2000341078580d1011201124200e20340343d45008054440e0a0240c000220890701d00030b9a6603011060084171742c440d4080724400c1c00804949101c50440030102074645110004806000030200095402074010a038081d03050302d40014020301c4000042c025540d01c0d04005184031010006200c050f03083e0480511112a2012400c5000b81c50600ba50340e5010444000d4150b102003001544081682c1d001c019912414070360800c02c90017040001003541d0040d140a0f40000c04004d2411034110011003210107644102c0091005c0b80e081d511204041d501841101c0c0c4a0401042180c022a1003002c480015621445500d0780d68106401000002c02d00c4001d00e512071548172003881400b4416408035120490340348005611010301c1c0c200b0440c50072240501a1544000c40580200010003042aa0002c051400743d07880580305c880520505500c4044401c02207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 962116609 1250 962115359 962115361
    0x16080d150905090d14030a1a030a030e1201021c0b040608030a031b0503090a140f0114150604180510090c050a09090501080c15040f1205060a0507050f03090a060c110606120303 77
    0x4012500b0040c60071071041c646114032002100480e140c010074ae10f0550000d5850715100148d0f1528560603105288140020360408400700f00c0b43c0c20170f01c280840c105906503605184001c41c1c541d500048014046481600c0c1c440c130040d01e0280c054841090f94544a0030846004204180500e081c0c90050b4020002003d044025a4071802400986410321141e4891199207460f01c0d00300340030b09081c4140c5011114054109007444081b4000200b08491207100300380804e02002030751000c85100c3c44400140400c1d141c42d00711020150142e01d0b0091600e090070060720030b280b1170b005001440501030903903505540070b5644003000e046031400e018000c15a0003003441d29000d89048410659242c0d031000020385401c1e61110302c901064000c0c0c0c00717841040c2034500611f00303015090107401d074071440f19142482640f4140380000e0251044100d0100714100c0400030800110003000f82809856010b003003000449143c08c4040c1814850b01c010903040e11800c0c0004050b81007640c034840301811807000031821 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 962117859 1250 962116609 962116621
    0x2a030a060e040840080705040501030b0f0a060b0f0924090d030201020d05100f0e0c040510020f0109060e0c01050405030a0809010c0b040f0b0601030216080d150905090d1403 76
    0x904000c12000000b8000318411680010404e01554001c40c0b1156074142102441c0c016614240706944d07024070300c528a05801000031501000040d41d114050407040281640d4441410004103090780000103103901c081503540100b000c1600070b104080b02210202001400c000403000d05002030480424800d0003405031a03043d00b4598208880e881c480c4c0009130034810094800011610304661002c05080010002c100e211031002c001c0001d400540b00740b251a180c07085130000075203d04d01c01c00340150f4843d60513007502031092080040301030007032000380108000c030700301000a000c420294504074080c2e04009086136000390111000c447c0c002d0060a052070b5640c03103900407508040e48450502c50b00941c180d0004a9000c8854440c500c0b030b2020a4840040b030815151140c030042810341032510411181c203041500d181850b80c4503510809490b5585801c00001c409484c00c80404220302040d218045840c21700d64002c04d20407440785040322952254103200b1101a0000001703018070500400200d46 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 962119109 1250 962117859 962117887
    0xb010207030303110f0c06010510020d0906050a091e140109060909090602120906160f05070f05010f0e0312070503010e0408160b0915010b030105182a030a060e0408 72
    0xf502c079000301c04c60400c144902c410080d81e03c00e00700b0300070300d400c0400180101e1821403032050200c0031a10040440741d1055a014107070310070314007604040c8500490020710301c0303200d00d06000c09083c1165083d41a01c4101345880301c601c240d80110301440b00d641240c0c90396035104600340c8045030040d0380c800298620b050304800040189010540300e541d0208410644250b41440040c0a50b10400041c1082c0c6000c0c44d5541000060302ea400302002407041a481e0f906603c4000d641e00b00740c0201c1c010f04400680d262070740c010200203009100b22070034104c5d040010400400580301a03d0101c04060803a41d030301c1411a481c0c0301c24081c4044541c2c86401040100303000e8009014180000c00e128000c444846d141c0443c03011045401d00099400b04503a26000000151900e005205032040c86055506010000d000291f4410141d500c142c3c0c03060014107420001b555960f41070108020009254840000010701c40d801103829001240c03c2280006008100c0a441ca1195401400c4a4141401c0a500c90 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 962120359 1250 962119109 962119121
    0x1806110d200f0601030606091407200105011511071a0f040513020409140f070c05010908030109091b06090b0702010225090f021204020111100504081209010b010207030303 75
    0x41c040c80003021545480789401c001400c0103442600060900358590328040c01915016048034003400e040000b10300c04504184001508500103051980440d41075041d00c0c04c0c41080341d18803400b6903080c2400010460401450036050040c6691036018501519454035a110200c1c0302e04a0002c42d2084010194400c0750041e02d11520000c95242c90641d4540015049042c19207030390041540c00039080009010a01c02c0011004400a100f2040d00c2c00110805c13195100614070300520860160719404c0200a500030403210384d000340f03095141d5840c2d82c0c00340001e154158080760701e4180307a0b602070320008141b10b11000b01c801d41d41d1404100c500781300007121203400a04d002c9055105008034a0b0381200d0b0300701813413001910b020b10648400e03d00110740381915407007034031130006500c1001401d040d01018465a948a502804c0c980e070004407103a0b40c2c03803401100162608055140606110800c494400203007847c550690b8007071295120900003500b00d40b080a051800340c2c2c4425400c00010307020b03400c04c1e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 962121609 1250 962120359 962120387
    0x1503040c1512020a020c040f0b0f0613030b0906070e1c0201050d02040b0d15052e170a0501030302011a0306070e031c030203100e011a0903010f0603031806110d 70
    0x2c0c079004926288414166045224620050f8000301d8600c0d2607410148103900c0d400c11080c60520100b030042001c01d601811141c3c0f254011074000a0b040c181032840c0d401d44c0c0c0255802051408249003d140643e00d41c101655042c0000d003510b80d100e0f205281800c3d080a40030032170642581c5102c07050740191f842c0c3d8803411080f0300c09074090000044005080001d03107407000318034401103a420580c1440ca42c03001c1e101e4102601c150074200c1c64178400411903202c009035a200b20204640180c410701c5c2550b0921000c2c0455080e112102c080050507004d0340c01c500e0485e446a0001d112108100800072601c40f4004030064041d4440d0000642c503510900203032401c03140180c1500d01c096486400c040c1d090341d9410032440420740000034006a02c1e8000d140100a0100c054265015414000c090032080c8079013448a0b450507000c51070340c103559000c0d88041d040c8440300a0400429a0b04c2c90082c3c001c0d000c5060050f5002d5075088001849030051101c0140750354200040e10000c01000016180e04e201e400325 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 962122859 1250 962121609 962121617
    0x30504051504050d02010c0908030a1d0406060507120207060807121b0306180603232e05150625061515090b0f07060e100b1503040c15 59
    0x52101140755960985018074043c80c042c0c18a20300d81003019007541e291401350300801ca0041000c20503a9004400c1d691010342610b060003a08400704401e00000020780602607201e4a401400100d807070f00308000b409004c3c441c01d20398a289040505c143d8840c031451141d9070204a00710005020b080c46000c0440f03090a03124000603464035411480d0b92141400b02d00600840d940f41000e10550714100e02611401607070904c113015240c00c5a80340035910004104c072000e4045564a0041ca2000611802c0c4139881580342840c10150220050710b407070054000661080f41c030300303404901441800382c00c2120019000c1e000501c0c0816544a02c00d04688aa0344551006008100710000891901841c0401c21030500c3c3d036085c040c100801c1001e040080786c408414405a504104003011540d41a41d090040740a80541ca0342c041381801c001401042d00f1b00a094003500c044291544a0359014060100301034a21100090224512172030a12066401134060648881c0800a07010604603038601b440f45468 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 962124109 1250 962122859 962122873
    0xe0901090b0d0f03020d0e09100902032701060e0a090b240310020c0601082103150d0b091b0915120a050c091312140f040603090213090c0603050405 65
    0x1200c940c0f1070021002100181c201c070f080b203800e4683c0b184e414500084104c80c0380c3e840f800c0c51051540900301911940a0440d000f0001540d25034511100b00414200c1d101f840020508080915000746500d00621307440f00010030105042c0c00040c4903481c482603000c0280b21498035403440f0301c1403240254010306031403030200a1413105920f09001080d2001c1281c003000d81c441c081c4241c4142402c4058018044503400100503046000030202a200910981d0600302d59a80710929884c0b0303030109452009400a1101d2104801c01020180c180c6c0f040b04020240d811102100e8100c072072900960002c940d200d50340a01191480d814031403c0708140c040148554006600150890f0410174a00820707546900440315068841c249504010b50015001c0203980c882503007a1b680d842d548120b1038007181004140016031460322920021a42200d00c10000da984035940ca03800103001d8180c5040881c005c44080f940b034203040038140100d10306954072000c50f6080504000c000c8000b03040c000e01c140c0b12440340341 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 962125359 1250 962124109 962124113
    0x1a032a040303080f011505310b07140609030405011115010f0305010c08061807180f0f1a07080d0609021c0c0206070207060f020f061f060e0901090b0d 66
    0x40081000714441c0d12101414070381a510400b41100517071108030864000007910709601c3d030090444401c01114402c0c1038000c400f900349062010301c10f4810404c40c020b20790011600d44031810141241c0c900c2455000e41c000b48280c00151101300989110f02103a00900c000d1100d03600510a034414081003108850780f43c5122100000c1640302a032005140c0c140d010428410b101c002c2c05070140c06000c41c1000c1400b4103000c030120307030b41140228188100049120108055910600303580484031051a41c210007151075014061110595104809280341d600c2400180305082115039140080102d102c0c2e070030034400e600d038404503511408074200301070b54854020900303000501c058020000b49224510425080b40c103514115800c081d00c000c00e542c4010204510b80380c0c00a0742c1c0040c1c030f54900e000319060502c0c0d0b100380c2c80c0c1100c0014460881c050041044040da484525180440d4512003c06120075941c201c152501c240751614140c11021a000600650a498201c003480b03240140c40390303036400c2d503607 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 962126609 1250 962125359 962125441
    0xa030e040e19030c03170705030f25030501080c0a0510081f0801020403020a140904060e0f01050103111c03020c0103200d050613020f04170a051608071a03 68
    0x2e1021408900300380005801d2603071115001241000d1000700484a04100d00054600e0000421180c0c80002800018003100107100b100212181600c035035070901103070700758050007038442402141120320401c850441180b85c000412411541b02a03c00152038000707610481d1165401130680d84a1380180d280b11948052003030084009100c15000117840d50709500c10441c5074032603507014900d4020a40b01d112501d644501116402a501040005041107041c40306820224482c0b61003140c1d51800c00000140180c0200100180034200c54105416004160b00054032800c010080c006901c00d0212045a5020f90b00c00c0400360700d1084103090000000d40520120f034000e0b62100e8085407a54240007175410006000c20060b90050300c01d505240708801c90058030700983c481c451240e48203800140d406001404000c61654010090300e544282111181400031864030400d40c00f441907140002d192481920301c1c01308440680712507403940d254070034511442c03104402d81d45448032402088105075411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 962127859 1250 962126609 962126653
    0x1202011803030c030b0406180903020111040311040b0102241f090b120c0312090609040603030c0b07050306010e130e0313031a090606120c060f03180a030e040e 70
    0x70a603404910b1441a010040a030307107410903100d01031070802005110798141d40100060200025000295004c81420101c2c0980821504151450030004020051094614a841100700d045c0c0e8240080c1c40307090012a5940b02d105045502c91460140d860950034031803401903040301c1081440200f2240040c91400249491340c0800b50113a522034091010703041c20001044480101c00103403c141001c1004030b521100c401050640b000360002d2461400d81c0e81200b0b0758030022025000f0040d1603240e140207440151686c4040e101d009104000901e038510801c1103c2c800e11040e074070625814070302014410828440b504684090f07807512204580641d040002c1c000c251003407103c2841c01d61071804d10300644c41d0014001c10340103020000300b0840c9a07001901c243c2110080d03602015000307050100c01c1c100304005102d15171110303000074500ba5281c08100598040c5101c00103102600c5441b1680a40d91200e8040c0140450084641c40001d85880d81c0085a44081002030303500400141007007800e203d403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 962129109 1250 962127859 962127863
    0x5130c050d030903320a0804180f0c030b010219020a09050a0209090a2c120c0708120403031101200a020f060408030f010b0f0d021309150e060103061212020118 70
    0x1540e502c0c43c000d0090501c01c1e07006160320fa0162000d20f400b44c0f981c1d001f510450041c452002c12001d64052203144a5208001c80103480d001080340e0030307541f000200a40445000c240c01442528400003000000361954100c0c0b9500500c2c0c022054907000551020b010010300c8010301c59030034040003845407903040b00c01d840790f0b00502000031604905c01f80307031b0340c103207150030781c1c08401c120119031400309000000d0b0001d80d03072443c02040b645070000d00300d080c0e24095082d00300d5078260203400344625560300154050410780b44282c40f0604907007081ca45940c220b900601c0400c11041712401101e00401c0030368002c105c100002e10548039414102c1602034644001039600f196500d80c00002c0000c2ca4012050041c090201451410310303181c52040d081d180c500944041d00103581e400682104e00c840964004001494921018443e030f551003900546001c0081c42503e80381d40410380001c40942c400e104540594161204c0b00380c100e5050f403200360a125035807210b141959a0b84117240c0c0010800001222054 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 962130359 1250 962129109 962129153
    0x302091b0d0c12021303020d051e0d0206010506070f022803150506040207030804032d0806030709020903030a20031b0c15030601211e05130c050d030903 67
    0x40302c50b1000b002054142c3c0c01250301d52042c40205256030425000008480c1c0494046c03540301a9410310364140a0b4445016541c5402c540c00c4204200c8041419034846c2425000d0f15250b03030740c0d84d09106c804d1243c00cac4000c00c0c090060200c0310052030034005184120303045044030320400768840d0320b81000003080d400a80d002c1700b404424600c44400c500a031540610300f03440a40c14000f03555405043d400010b0001024820800807405c6580c001e8640c00c0e021000c10200e800d99002c3e61a40500010025140c0da4028080c03004040340101c1c1c680212046044060b0003103181500b071450454040300d00300745494051944d898407406a844c2080a44025141c1d101c0441c1c17600400d031002d0740b07400c43d00e09040d0700420702c407a403116105d50040140e039070081080c20f120181e4038500060007a01c801c8200c800f81d54a02c1e01030008400218840c4007998162400c0040000c0d1300e600c154580e002d12009401414515500d03000d10650501d622000441c9201c1e00781440415202c3c0e9505041c07108071a030b404400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 962131609 1250 962130359 962130371
    0x10f020f0c2b110f030d0c2705220c03150e0705160f020307060801150e0a030f02060c03030f04020f040917091909020a02060c040f0302091b0d 63
    0x1420a00c1503a40c00c9100096025140c451141440c900d580880a030340700344501c10070003d4041c8410310003ea078901404003170340e5803000e10342009401002d503202c1050001d540741d4010070760f4400c0c0035200d842e061190104440c3c090314207401c1001c0c42001c201c2408140900b615020040c0300d15001d038411750003c07900c0100300c203101c1082d05402c4c004103522008507116041d09002419800c030040310120340742c820b51400c92001904012004280442009400d07200f00d2500081f05640107003c2c6050f9240501140d2400080603800c90b05482c19010150340112116803c2000801d4015100549440074210714100880c00807090308680044800c60541c0c9030141c100011803030309400400c000b2800f10b6007004100c400d922408000030008a01d0300c4030b488000f0340d5515560340d40345c0c50141c401080420325901912071040d00060f401908404001d8840e9601042c114980700c0c09135400e444280780c0c0c40a645285d5000c01a05a0029008520341c0c413066040c81103148000004200000c4062008241 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 962132859 1250 962131609 962131627
    0x7080601091b0f0f03060803030928051f060f06031b08070203030a15050d2904020112021c05040807020f0105090d060f0b0303071208010b0301050d14010f020f 70
    0x165140720800400d2003280384400345446400c242c02e980b0800f96441c0c02c03031415540d990b065006100d980c20926891201104021007080000f40c11401103880d0b1000c0c10102096440c40a05204034180052031500180c401c010000042c00790f001d64107212910118210380e8800402028181710f410000010b52100d036240400c07a540701141e000d030f00ca02e20f40640d0340c0c60548002512400090145126152500e04401c0303c7e0130540c000c2c00140c5030007421903844068900c0d03e4a50903414034105d0700745098441c210078144903200890ba200c0ca4042c0c5451f1003105040035000000d60280d900c0c8001709060389940090310403544602403040c1d22413189190340da038550040003c48043d0380416810400c00700156010341d152440d0030307034000f9070113900030500305d07982c0c065030003c0e1035004102c503094400420006c050068058200d0094004c43d1100481640c0b03444070f12016100074050760390072001c03241101c0000395203c0d0144409184480c00010030010200d2000141e07445101500d000080210701008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 962134109 1250 962132859 962132861
    0x51b07050111131508070f1b05010204062120070c0f06090602060a0510090e0c1009170703110d11100206190e12030601090e040503071202060405100e030c0708060109 73
    0xc69603e13035003001c103407078030b0071030401454540c480b40d403d010040740001044040e5480c3d90f088080036406402135481d40d4880800030502c0030b40b8483c1040444100104c80500c51141c0308000a054110155811180500d03d90040c0b030b43c0503440c221801100e00500080d8001c0404c0c42d14081c02c65941c0e034280e817602d00320000b442c002015141070703445071412013885044800c52a098044445400300414040c50001045040515110380140c04c0404c1c40740a890007a80440c01d40150340800321841c40f0000b449940999807007485c0030041480030020b42c410000d1400c01c20512070f00380301316001e81005580768081010a130b000341100000da07006c6802c0c068100511444030303000350440441000340c0c90101170020b03a2000105074900700d031030f4008040f441c0b592142108078041c14086c2904449403c20307251240c4ea9600c202d1041d2103c0796070001c001c0f94140b011403254011074003d8002d110350381c0e61060000080400310004006032008001d580306106040c0101402800034101030103207589480e103904 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 962135359 1250 962134109 962134139
    0x240706050127020a0c02310c02011409030d051003060e01050601201906020903120a0201060f0506031609170c0306090619020a09120b06030c0103051b0705011113 71
    0x800e0351030051225030313001a40318192140064040312805092003c81c81c3c0ca0901070720501074440d8042810861481e2031605070001c192001c030740d40c002c005a1104c40b0340700503449000d4a007140140c208100b445140d0301c6070f0700016080500460700030340f0b440d929912941110003851303809101d0b94407481048074640e080b6407000e0020040ba00241504544042080e4a40c01d141440000745202401d280081c0310650381a1905520042d0840d500c0030b84e09040300040b600840340d554019800c0034800300d20080c05820b100201c480c003406243c00c6440e11505111342d464622030600800000d8040018051800e039405030000030002d015100b0140c185042c142401d0000b0181d581c2a48200709000342180840032003d08406075041c0180c545051400c00ca602d1800c80c0d01c0700c24440c00c1d0000d041c0034080c4507160f03540180012001c07103050240c4880190117680e012600a00c110139040c418105d2000d20307d005200540c0316400014200c000749510680d40d4009810220018030604800d00c034102002420b4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 962136609 1250 962135359 962135429
    0x20f04082b0c1403160341070303090215090a170604151b050325051c0f02041e080c0a0512030c010911030106060e2407060501 56
    0x3440340149069000d000c02c0403804006010325401c40d40c0c20040c07607050003900c52880707004005c40402401750900401d90100c43d1700a41d0802043c0b40c00403035100141c0c1b0741c201c5a001c0d00c07004d00d1402241d1a0514015001803a0550034992548114401a5180000c1009e6280e6048090b0f48440d6440c041c805c119071260082000114413009001e0200c00020b01c2941c040c1d03102e041e81d040d01d81007030f82e003201910300c151041c001d80c014841040e035200c1e0080081c40c403424100001d00c4400c0020144040e0351012001e00d5008a407080040d00054a9500c800300e10340c200b0020702040d21502c11034854100c1e8406d034008000310900240d103c014014070b0340c0c01c0b0005e100d4540241803540070080041c503540c01503c00e2505c2400c07203840004101000b0303c20f0f1120014020300801140c4607504221001d03110b00b40b0301e240b10354030b003d4000c103c060040c008081e044602034071165698511041e26019130b40900400030700d000d4140042400600c0c207000d103a0180c0305030941e00c401036000c040901030300c080007158 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 962137859 1250 962136609 962136673
    0x10f0807020f10020a0e0d0c05120313030807020108070804020a05270a02090a2304020706060b0c01141803040e07092309061c0b1b07061d0d0206010603050703020f0408 74
    0xc42c07c0840c41c885c011006944080b1000080c040880150900d54030070444405000341d952000007091040d001c000d03040c000e000b80c80d070340c1030342c0d84007013041ba640c180441c6c00943c8034103501c405220300c2c2003a18109100705003204109600304030b1034903800e8505c1e804841c601c2019800040c41181820102c010000400f5590300303e444c0b00c0c0039400c0001c0d002d000f00c200240901e601040001c1030120541002000b45401048155150390074000580a400c041c52404041201d170004248009070b5604542080010302c0003a60501d4140645214441409480513003006540e03000442c51000c2d81081d94003549c90503840420380040c0800780700700f01100a18080c46024002c86040c0307800c0095402d5040c2d40d074428a40b2500360b03951080d00846071001b0304c50b5480d42c3c0c40864810308210306035214991480e40d040a0000c1841c00302070199891090040e020010b07002403004100d8a402900403d41240590030003605104c409160310a55400c40d502a280507844046c60365405a415452030b18002c0340651 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 962139109 1250 962137859 962137879
    0x110318030c060c0f1e120c030601020a020d0f08040b03040c050415090f060e091b041a01180801052502070e1308090607051c020a02010f0807020f10020a0e 68
    0x710040c0c9a440080181c2d81c081000180290103680c0d42d4110740084100c02c50948600e286050039411507005815002d04181034540821150340c14403059038410901680101070200d590f90901c410b5a4541c601100e41800e01170055002841010140c005446200c00c055203900d818248901003c4583d401035005510381410105d040395180e03a0b0105070340d0010b201141610700c003000075004204950010084000400c10b2000d01c090204070201600380070040304200350b09010401c801c45035601e004a0700c1058240b2550302c95402081c0c000e1410581d0040841300e0b543d200c1c0e4481c21354204607505c014040d070307081c0c1003850682a00380413000c0304d56620041c10307030b68200084a000160b010380789100c4021200d4004d4100003003c01240e08001e00a04031a848120702c0c5441641d44a21001c0c007500f0301d00d08002420b6591002464070358103030f0142d45000a1440c05441512078081c090203990460050010451001404000d4414001c80c1c0901c0180c2d40e2004120041c020a50149694030440310340c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 962140359 1250 962139109 962139127
    0xb031618050d080c1005040c0815010b070f0c09090b040b1501021b03010e01020d020a091e0608150d030e0f04060f0b0906040f0909170c030307111011031803 69
    0x307070142e0701980d01c2041599551800620341e8502217002c2841000d0a05250800003084204038008e4111a00402140d0300e0300301154440c0c40070402400b640c82002010300505020404013002104014047e918012815407100000380560700010703001e03114206008103110400c20003d1085900102c42c651a038444516070f80000c0d10b030300600d0501d520719500d502d48541315540a60001052114050086582d4405480c03500044c0d000030709114003044442c00e0000d4003070204c4c1c1c80c080800c2020707600c4410351400c00401341c030b0103000580340c0030b288014200c0400072510b69050300c50342c01e4000c2d21200011030440c0208039040050100180c0200d003085410840311589103820b40940c1c4190401c1c645420b14030006c105540259031207075005041116000a40140560040b040310303000d482d0400524820091082482c421403004090744d600400024440740d12a11400b600035400405880805400c544404180c0e0840c4448005c0c40d100001400849108404011004d0441c1006941024220 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 962141609 1250 962140359 962140369
    0xd0e0636030a0804020307320406030f0f03090504050a0b0307081b09130206120109050a0908040b0a0903150e1c020d08040c080601260c0a1403070b03161805 69
    0x401c90080c01143d001150846d902441040058582860841d420b041d07082001c00c107444030a00c846e403a11300d80c45c0c00e0740c2c0c01d82014003407801583c1d00600a46014803103030b030b04d00344441d007603103015410001c1c012804686175445025540c02481c802e01d0100d005000c5100b054100704090b4043c2c56248c1c4100351042c100441c1c440542031030901141c050360155a46284200ca1400740e280c02903010f071001800c61526402a07691741d043c1c0e9481d80c420041555058542800c0301d40310300c03010304803080502041141c0554078000348109861460005c802c207640e682d8860291a200203001070581d200c044540d0343c9142042407e581c00308024bc00410017030346001c00b075141c92455001c801000303000000101800038500815006280c00401c40f01c40d0b40c0d64455604580b60100014040b08004403c414203400300000e0543c9840402030004c0d0001d0f14008150b450107003403025168143c003424500041204d0120042c502c1814a8121100d4513071007018020801030f4910144640450443d90501c420307103038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 962142859 1250 962141609 962141617
    0x240408030d231009092a0602070f1802090f120d120504080901110a050d0314061801060e0f0d0f02040b06161101030914100606030e030f0d0e063603 65
    0x4c43c0c1c4002041781480c00c0c14a003414520a0607035503030003000691824100c420711108101e52980c1d00303a5902d0b170344415034041d41c5080d520592140031404c0c08100750000d038590041c01c8038071000300244213502c501c601048107062000d200840c50707000011070a528a8100d0f202c0c064400108004000c00e241581e11000c907401014005410080040f5080c402c5001c1002105201600f12084a0028600385802405002c040500001110340780c00416003c2c28086049503400c4072800b40b820013a801c00c03c1c00c0f10000180300e50180d0004070101c5580007900e0f10382000340000d019080111960f8100e0041c48140da00ca1084070b8010201000042c40c407070780344844406400e0340001c0002400310204e004074040d06507210f015000071a03a84000002c0540000c00b1700d8920040501844090764881c2c098007207540c880110042c90300b04215910040740304400800a0b05a00d050000c2c50044c030a405a10382032007103c500302409840710303102c02e64901e80c0c0002e0002d10000c190028107040010401912801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 962144109 1250 962142859 962142869
    0x100906021c0c06110f040b03070e06070201080a051009021209060112030f0804020402091c050606010503010503300c0607020708060403050a0c17030903070b060906240408030d2310 79
    0x4e5144040c1c2c1c20b40c0755440403208580b12510304541c8494548038815856401922038001081c107003010f208450030554155040c02d50140c40e512400d986411000000c0c4c1070003441980500c0d80c0d054081408500c40c4046c1040d07a01024102400349030070301d250b601d05a810b80010f40c1d00e04400f00c401000a5104001a0340340420b460611a2612a072010401a015199505c0d5001e518005003840300d0004555083e03031140914203c51a9031600001503a20f80b00a014290301500201c0030103030941c9103107404490b203098081c1170542217009054961855008a591428a50444130038040d000d41c0c1000003e003d010114003405460a059802a0062203041c241c982031013028015403041c0460409400b91503502c10610645d64501100000d45991202101b02c46011420020841c5810225007d034450700e80a403180c24900700058035000004840604409012030400010520724000e1000e81400c07000c3c1070b000301d10413030307410003070307004040030040d003281c0751008004004001c002c00c049141224 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 962145359 1250 962144109 962144111
    0x102010614060a1218060507081305060c070312090c1505041514090307060e150301050a03060506130c020d0305091902150f0f0403120807020a030f0c02100906021c0c06 74
    0x5800f4210b40800340c141005440c0c0a0707025089000241b1800c4c0e040948655410b684c1d0500564030203100e4082c441c0c1c440400740050b8000c0c40068000801680201020340c000e0500c2c0455251500514041e1926100203c6100b410100104400740e801906004801c5040c24440e09041c104101043c1d1300404605000801462800200300c030b4490b0310032650030510160940d100c0c5a1a45d00290001806c40751090041034010409844520301c0340c00c0c1c134141c41e8020007880c0300b00d107140c0355200034150240299a0003030100e2000c13001c4600c0b0344503842010707101e03070060f103040400a84c0c081d04030307440189011160340100e1044149503200c01946641d5645c12280d003000d030040c2907981c08650141181d42c114071880000c1c111003458504000c1e01c112403084098014140c5400300840341103506556090240e40f0070604500003d000303442c00040e1744103e107070044900c03640c1c0d0009125084c2c2070448401040d18040e09003d80c0742e050040003c1c07605012a940d00e480d11065000f0082580344601400782 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 962146609 1250 962145359 962145377
    0x10f1b030e0904030f092709061107051506041418030f0c031804180f0f0819030f0b01020c090c12070909060503061302060d06051309020102010614060a 67
    0x14014240000307544006002e42d6003503e0700c0d00d0090b14480e40d007214000410445940015441411965030000c00d4003031000382031821441c48003401819280740b0031501d4907103c03030115540c0390810019054143c003810041c8058241415009000c280c0640418040c034103281c44201ea444060403882e802c5809500ba08a410602c58030b06070030f6024100100340d40540000b80a00b41002c00405030006000034407040000400c0700007040102c86c40800c405d100e0301b40c50031103900844d98810700e07401228046c0441d081d03000960b030b90744512503200305c82d0b08104040a5074151f6100382c1c14400c0c80c0042c1c000c0c020400041c65101e00107590b4010300c03842c691203111140700103850389203d0401d582d42c0b51003807090100c290410000c064076681349805180c85103032416400243c2494002180c6001d0b032281d0a0b5000703114025020700c081c584c0715a004030815503d4500000341c80d16110102980e441c1d8014001515007040d00c002030a42d2083d40c44440410061505002075541341c4044031302403425400c01d6001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 962147859 1250 962146609 962146613
    0x303012c04140c102303010303140f12070903030e151e1e070201021b0d12020c030604031e0e090a15030804060203130915050105030601030f02030a0e0705010f1b 71
    0xc1c184604060fa50007001c4e02c0d003002002d0341c005aa040080041e08078075095030440104403000c0d40005d10025001402c10500402040340003002410942c40035686103260540041070f4045c503040c02c0e50039100040c00c41d00f080003817584c0700441d102081c03005c4440030000000400584850700403003038403803400a058030800174003d00b41000c03250008100400c0e040e202800c040b15a07625045004142c0c05030103070b204410051084156040d800400007445400b108020751100c5400d08602c080200c10b61240c07518154040da401c00209100d90310039036481050a0240014590781c007140d4070b415040c881c40b40d510440ca81c0da03030000b69510100b004800240c04c00c41c0c004030705203181c8580c400b42803540c00140204140f6404801840c0000c814a20794030100d55078081041141c4118110701e01c915000034040c0840e40c410802160080746c14540403841c1c2c1d110001034822680140c0f00602d18a940f03840789610400284000030042009003000000e0404501001e030102e0500791004640451300303607044007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 962149109 1250 962147859 962147863
    0xa1e031205041802070212030307020d05090406080616020c0303070b010b1806030a0c031805210903010e01020c070618090519180204060b0a050d02090d050d020303012c0414 76
    0x14000390040c0002c007491030f40840300039840207400f68051160b426a0070309801000044078000e1000d47c1c003e086200d0703480b100b25402c0e0844502c66600640b140e40c000742004082260a000e40c0c0c00c52840d40c64030081a001a20b410400d410b4103004e9002840b04401158907824800d0440b401101c4241c0c0c0d0320781e180c00c100b1a000c0001d5085038000c1c0040107205521206a0040e8602c3c050307614108a009080390f01500d07a00a29a0010040d601001c0e180d01c00b04810b4042d45168401a041c1605004600380000d003502e007801c4c1c076055143c0d8042a007200c1c0c0401046102c00806040c14044072110051101d400910414050645100e88910202310507246400b242c5158000300001040910451440c01004c00000c000603841541011710109540c0069001c44215020540720103107032489030380000020350420010203a02c10502d286144c08079206000680000790143d0180d5661b44c104080c5075041c8180d05041e100d5065a03021816000e6100a1a80e030842c1e0466020745481d05100017481c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 962150359 1250 962149109 962149117
    0x70305071d03191208090111030103060b0a030c06050a1409101103070605011823060409060b0913120e03070b18131e0506030a0b13080a0e0a1e031205 66
    0x2205204a012843d81030005003c1030314803400c000e40d00d0010f503480744035010b802c2c1d450790104081c504000700b004100103640c03540503020860026281e00c1c070341952a25001e071000c0450388214082840080ea255220398810b5016494150000000e4244040c400c00f050f9070030181203c0740240051010241000071003041680c2e030039540108140620b44c0c5030700c030038400c44256030709010036107051031003034901c0303040584e840603a0707619060142c20b80350b481008200c050b040c118001d55500c0e90720b1081c01d02d5901c4041f14540b04110040781e139001d006152508600400c0340100000130098404c80290090b80c020619500300d4a003551352a0302c03a03030080c0108124000d8407a2140d4020007607800e940342c00d412a001400e44800c8000c4900e0603180d03800411040d180100c415641c580c020010800018110300c85180d08030710800102012a0140c0e07072145d940c0d921450b0302d00301003185441ea01e4590f20701540706030040d00c0800e03080074818141c07400120031456540401041c18044c0e4038005201d038072880030380b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 962151609 1250 962150359 962150383
    0x71e020316090204470c010509060906160804060f0b0907020f0f03091503071709061609030210140906130305070f05150327010b09070305071d03 64
    0x6031080507696042c4000075407091241405081920628030300d0660b18200c0c0742c2010001c2c0641350070b8070b041206140f0146000c10340340c440e101428440039110746400d22419210703240450080041b410510381c01441d0803001000f58104a0103041d40c0800c16504c0303003005400c01e40c40980440c540c3e0688005401600c000180c098000c1480c0081044550340020000c5041844106843d40d2803020700d00280c403071181e40102c940103090101e080c2c000382425402140d11064a00d4401040300c2c0548500303003500c03007e481c0a00c040e8019000c1c400d504a56401880840b0000d0421000c40c5103984c1c00701c0c04018450182d00103106940b0103400850310910304403108070600424490352401c1e0200d5010107422680801c1d2103030302c20f03e40003140c01030580350b040e0240c50005202c0b200307440012005140d01e1703100074004103031449004416001e9260700140b1101e565501d5002061803424541400752038074000380080d0400d810801401002c0390481281401108442c4113040c0721240300c008240350501c00004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 962152859 1250 962151609 962151643
    0x30318030a06091110020304080c0105130801110d051006120504060617010e1e0c0904030306050d0b062e03091e08251a070320091302071e0203 63
    0x258000b04072030624010300c10035046602445c40600000b00b01c0e500d02660107444410b9110000d046079a6024502401c1081e402c600300c10325103921107061754256500b100c1c88a401c070001150301c2143d0b4000340243c542c004080302c04141c00780d2400d4001001304242e00503030202240e841e004602400304c0ca8000360b0141050803840440e030041c5181d050700808102d07012240901928100803990805002401e5a04800d440240001c248040801010100190040b801c1c0b40c1d9802c2e00003029100d485440d90303150301483d081c5001d0300c0d00c0e0061100b945004044003003a503c45442000e960400400f0440d0300444a1500155000c1c0d246082403a4512030f10041454000d400d903a80100301d021402009a082c41d41a06d45111804440d150319076114107100801714440541d21200445003108401e600890528021404e0350f00724200080ba6005104244444000090040307654101242d000961500d44241145044081e444140c0e125441010207400e091280c191081990740402483c0411200051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 962154109 1250 962152859 962152871
    0xb180a02030105041101030f0902030c09090f0604030f030c030c120f090818030708030c120a120c0c0605060d050a06110f030a140705040608070c0203070815040c050f030318030a06 79
    0x24107038003100d0717000b440b075000900385841820b8a5080b03011b240c841301e60103401424640e080c0d100f003108540d00140044204d200c0d010b1860b1749251704002040c01a0301a0b05c550b141800c80000083c10b4440096203c0141410302c0914071025030b010658103a4603143c1800042c80e10958220701c00074260b40d04000e000c010300841c480c0b9824a040c1e4107040d62035000c41c110351100b03030b46102d04c607204d0007080003201007070b008802c5441d5421a0200103000d41506454840540c507880c1a0610031500618540000580640078803000c11800d0311070190001c90880700070301c600c031140e0b803955980c0400300c0000700501e85480602c0c4041e04440103585e620104105021b071246051540e002c002e0440001e01620180380790f011403c0b1a000381c0488007545c115660f0311030166108642581c040c82d08940490f014032450700700056000c000d1064040d210300186003900c1605160801200380d1a03684c100340e11502000e144040259400404c0703454030201c4c1c003611803003400c0120009081c24900c020250503107007001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 962155359 1250 962154109 962154113
    0x7111e1c03020d1406091302010201151806061107030837080f060a0306051e0a020a030605040b030304060f0504031709030f0601030c121704091509090b180a0203010504 74
    0x1801078a00d1507043d500c100300301d0799038600e04112010f05030342c9a038100200c200811041403102d81c540802c2401800081002400c404100f0300280c0280d01600b104a520142040200d03810b0051000824680c5490005800d03000030450305d8039542d00c0014020403002412107642c5501c020703288104103140e160600002100140c24103a0900140080300143c074079000034250a02481640380a40d00241c15042c1032401c55503410014640504421100c2000009203810f100018030031134230400501c6000358459000c81c0b0040d082d0348854020303d100c5c0d410003141c2000ca80b000010740d022580b00d03213040c081d03030403184109031403903c12608080c01c0031650100d0668400401070060030990f0003a001c42e510600201c03000744d1544000e000040c074690f240700c020428400d00070035001c0e599020740094925045208030f108400c0d446030780881c0c1d01540726003d081c0001c02c43c4d082c030001003102c101c040c8002405507988034540e440040045180000101d803072900000104500d0004945c0a002002942014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 962156609 1250 962155359 962155361
    0x5070504150905033003070804021e04050414070501021f0c200a0b061f030b04150e06030f03070c090914010903120e03090a0909140a0807050607111e1c03 68
    0xc04200e80c0361414441d003045076440e82a084900c1000b17540e4980015484550800c00c900bd400301003010301d01030500b0320390001e81c0c5510072280298404c604507030640c0701c0c1800442c10100707a6070000e030542d0480510000ca440705c20348060401540c484c0f001400b050000c006485003484003e001038444810306401c6450900019500c1ca41d40c010810041c50ba5031b09001c00c41e0440610504000b003000c51103228062038001d40244250303410040000c114038480c03a0324001c1b42c179038580c02510100030460030b000c2d0904082c0500b0418400760b50180d13142110a45a40c0c1d07034400244600344440303580340c0d038040911a00d05104514642c084c0001e00c00802c203420010020b42544105407002480c2c107180c0b0107003080000c122241004040c0c00d41c5000d070310700307440c000c000d10403505c05858020305002000c43c0c50006112550090307200704540d40e00c0f40d9050600a14102005000c0c009100d0320784043c2851440c0007400c41554915014030b00b01c0c3c4040450740310304204607060710204c0f08041d02900041d60b501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 962157859 1250 962156609 962156653
    0x5131403030103061406060a03090c17070f0b1312020f040203070210050105011d2b05030703030c020304030c12031e020c130501050d02091302180406050a0507050415090503 76
    0x10081407145c0d00d002215a00e0095080e0b41480c0e0000e41005084c036414025000191041d005040344e2411564404044a80303c48240951680c0d0700109424495251040e10346000b91440c0f001c0b640c2814406a4502c0e0080c410340904a801080150240115a2074003600c07034038454050f005646a05150402a42c2c6005a1008800e600d04010001c9100c0d4424520040e000c03000c5500e20a018442005102d942d4074604841220381404080c1c605020300260700626840e4841e0700115542c001c941002003c82d41560004000c540081000700082913041100d0342c25074000002a416208482c51305485241090352501401c41d59120380d0120643c0118601c9009079080c0c81c3c1d40c0c50414850060400c4500c240240d503400410b404a02c005420000c034407651150214580a91401c6141c0000d410100302a040600c910f04010402003006028042d090b0000c1c0000014800741c05c0005000d4401d010314001c2071076040464881d04c11491181c50f13920014036001e002c4c2c4880d544c91000c94058050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 962159109 1250 962157859 962157863
    0x20010e1009020916080a110919210c060e03030d090605071121160606082116080c01140907030311120a030b1f0e0f0307030503070605131403030103 65
    0x70f54030010342c0168020840010f007119564440c1055a03c0840a00040c440d20340311980c0038805120000f0705440398004554110b00c8070702560f0041c0e14008801c015450782484640600d11480b5111000507122503030f09003601c0e900d007400f00c2e0036562070010074518010605e040b0040c03414450f610040c4031141e1700c0640a02050fa44210007032040140640e6120000208048040d004002c041002581240548980000f00307031489030180b1140c031117006a48068024260036001038041d540c5a03440c0b1340141c1c440c100d409009604100300b01004010001c1500006864510000b41490200c50298001900004040c45400d110f04040b184a0396810140c00120702184842103601d00c003000c00200031660307109031154586040700a0904501500e0081d0070140c00c0b9040e10a800e4001c4030070000e6000c0481c103940ca6070305001440d802c000403e1030b0041c007030f8002e800c4600240003084011045030007030307600000c010410391502002c1340d00b108034003540070b8600a00c640c094a407140c000300041d8100d034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 962160359 1250 962159109 962159119
    0x1a0405040f0213140a0c021f0c0810050102190201030e01090b040510020403241d0c030d030605102712050609011803030e0c042c0106030320010e100902 67
    0x2c0c901000c0d680c11a80360500080e000d01301c040003d0040160f90b00185174003101c6206903110303680c1609030b05001c204610f00500802e80c0303a9007051109940070701802c0d4010003408c482e0741c1c46d03894840080e44540700c4608000f1608a000f00d0242564000d8000288010b5408020401c0700c1040c20000f8140e03809440454403401021b10004011419000780c50569800001d8080846604100742031588410354000d200c0a807074070303040340e801d9204601504840341218040c242090b02c0c0000c2604001c00e0031140018945000300038000c5440d1403510b80501c15003030511440300c807042c00300041c0b07000f80b18642c0710702c5003203240000c02c00420340f04010411500c80e208070fa005450702e0a09130700b82c4050443e81c0c0d00d18a1041c801501080c0b10350072907186e071400e86090301c81c00a14440031a0550b601d810501d42124004030380740c0c0788030940d0540c21107140543c43c02000418203540c0e00400d800300d9800101420039241d00d1007600d89400394002c84000e0b54410865003d04c40c881c0f42d00d8082d00c80d414059120b5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 962161609 1250 962160359 962160379
    0x3031508100e2401180b1c05190302061303140a200708030f0706140705130905010810110c0d2c0907320403060e0703151a0405040f02 59
    0x1010441c3c10900c20040b0b9403031210102e82c20b00c04101040000c03c402526a5034441421b120561684200c15820307002070b4000145c078075540c0c100580307061101014604a107008036504000720f5400320f40b0307e0308090300507154500d000301400c00f241c80e807542048480115900103400d4a40135048035144440000c0340d81c2c000050b4443c0641162034000c1072084001c0c43d00b08000b500c00ba0744901b0000c20010344034001c0011041d510002d007079151003045400d03501003240090000a0001c000711120018000c0c403034140f00c0340d81000c00c4161140307189007a032507000741c031800303c3c0b02c2c01c071101c6050341c50b8202241c0880c6c2c26200c0f90000141410000780c203030050071490324030584040c004807420002e030200107405640e60351034200c03040b02c2e01c60000d0700091082ca20000080d01001da84a0104150004d07046402c5d111815424440202c0b1510114003100703911100c000c0001030780840d0504101116001c000130075910101c4282c800d000000342c05607019240c50204402c100f4031000303c10300d8034000d803144820 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 962162859 1250 962161609 962161633
    0x1050c04080f1c030c0909090b0711030403030e0d140f25030b070c060209130b030d0201061208031e131a060f042a0503070e060405090403031508100e 66
    0x4890200c0d0b0a0f18001080c405280c4901d4001d4103c0d04080c2d5107460f281c1d06003503407030600d00c003101c3c130315041240c20542d8041444001c5a21103607a1905200f0740c4061490945140c0d0040d000d400d402100320b003e1a8000522414880c40000b03040440c90000203540b160310452542c3d5807a00700c1428801440b82920a400e03190366015104501545c3d405018042079854101c010f0b58402540c10702200d65640030000924292989110b0700b01040b9081741c04070f650342c208410907040c46400c0d1178a508580c5064000c0100d100300a04000030b4941002c03441c0c0d540c0d1a404076036001a185903042c800170300041c0050028080b085002003403680c0c06100e8006500b002c414019100c0802a01c580360b12030403030075422410b80b420754040301e03092880d40510b9250800c0024400620030200c48280081070001c0204240f450f0070480e2140b10440c00c88595150134240f000044401c0740140c8003904143c1d90301807017414551901c04071400307000404116801e50540c1d14030030b0060b04201c6c05180d40e6004102c00a24 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 962164109 1250 962162859 962162863
    0x20705060f01060c1e0f140c0406080609030403080f0403170a18061d041e1b030b060304080711090a1508060912074b0c09050705090301050c04080f 65
    0x1050b400754160007105003545e094610030802031000d0b42d00304503a548540c0029201034295080703007203000250409003441c100f004200e401d19400113006400003004c01480980220440f8240e035401840310340c454560040358850341c003c981006207941840101c505035142c943c1c0c0075020548287d69200588040c611150740120302d544201070124501318a0360000c80780e00300c0640c0c1100000303880007512410454605d2641c04090b06e003481642e0b42c6101206002c40700e00c3c00344505030b40c0745c1011f010350074240d0042030007448000d0018000d804041201010004842030702e1100d110010032800c0c039170900800f0007000700300c5e10526410401200d00c000a07008000b0800a01c03a4078154060301510f00c0f00c00c0aa0340a90003400100d48000380c5621f107200c3d035810344038802e000c4404072107582c44000c07070082504e80b90100142443c0c004400c90f460000090280310002050382c4102e100400d01d0307200c401d015650340c0a0700d00050790550800c01001901000e540240c012101c0305400c50b8201500741809903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 962165359 1250 962164109 962164127
    0xd0902090a0911150f030f070e030d0507030503040c080102210615070b070504081c080a090b1306060b0a08040605060f1806010c020a06110d03023a020705060f0106 72
    0x40202010b05402d00052030300400c64074020000003c41403138485c07030b5207041c9007030340c8120740481110640c0030911a030107034480440c90841005030010b100303038aa0400d01030100c0c022070a006040010000c0042c08020b60b8070240b00003040001c00a6450740c10a403440141c3c5050500300d50007002900c8001016443c040701402e401c1e004c944001c902d40051610340844880004000e2018040b003004000350300c0c0c00411940c034002203c4c6c100340c80e071081440c20080580344064900d1080c1420940080c0100d00c03075000107508040c006196061008003807810780050000c590049880d88004123003403403125040068540300c0c92080c40c0c200200d41d109020406011100701c45550861491850700b1303900350302014101d0704100c050506680c07400301540021081680c0f40c01000005010740003001004800304107414119200781420760811031090303180020100c100742c012858503540300c07012902c12800c0d000440c1d041101242590345043c4d9080c25a1764401c1a0b90101c4c0000c8050300004415110b05011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 962166609 1250 962165359 962165363
    0x1030e010b06041406040807031b0b0a12150b0a11070e0403020a021309050607030207140d0f0e04180b0105120a080403200901030b06040b04020f0f030c0d020d0902090a09 75
    0xd8100780c2001c0a40c9100d20240401c02d030017143c104400304071220204461130003144111110100f46010005200c90b185440d03008041c010001c0c440ca00708182c0100c84024034003840e80e4000380000f11030407120ba109a090344541009840050400f220075804404542003a0001c0308840d03c0b45d5960318803001c2808200c9025005030420081c3c040146000150340101801c008004100c41001da1915400c0450940e040d601081e40016808200a8031400e150600040c0001900c3d51241d5940040d1851441d511030b04104070894045c4440d698032688a86500d0102c00b81c10310003080c6600e400c91f1b242c4001c0c090540b0a20222020071504000042d041d150b09500c03c00746418035245940721b00b459040e444a41c4025100601d5185898440d08035a43c000e5000744001c04080c00c1c004144000c991414102c00c2c0103c0c0100305640306181d071841190591450340320207954a50710304081200c640101c0e00c0502d0114000240a440c05030140c11912101d8004c4a098443d034030b078440c400d8100c1d08440c1d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 962167859 1250 962166609 962166619
    0x27060c040504021b0f0d0815030c040c090902030c040e09030322031e021b0303040e04170405060c03120703090b0412030b030a05011506022103040302160e0601030e010b 74
    0x105201e1810681c0180c4103240401c1303a6458041d40354944a410000303241d462a905030b00629525456961003040e590300450074004c004240500c1d070b00800d2301c604108a403076009546480ca4952160703c102c0d0450f0050110181c11500c038149040352001300d034407610502900d440401d0225114403000310460703015068480c0700030054090700400b00545091184140c00b803002c0c038216000416991403403920111a20350241c0091046410207000e0030104030512400703503000741700900500c034510740203c0d0880d070000c1001740d030500345c8154001148034581059400180100310180f104400201600c40010340d180c0f01e44107035075020b8003181212110080030b0800100c1501080126042e5400c4c502c00402d10310b40400d41034280d1020a1405900a404480603076440755400400440080704102928291010300b1404178084407403140101e9203040074039071100000101f030400d4002c00c0110001407030003a60f2030741c5030760715019074402e19000c07910280441e0078180004061001881342110980b00100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 962169109 1250 962167859 962167867
    0x150e1c0906021f062c5209060807031107030f020703080c10050619051e130501080d0314070c0f0b0408091c0c05220527060c 55
    0x40d5000050700800040060107031350f18004565030001d8425410060308202ca0480050007491039005401402051942c44002c0030015025400f01c860340d0910b002c0021080d441c01103c0105502c40b4903020b002204203c4040500082c03045d50044045400c641d0641c9400700e0b296201e810507010f641032403203072804403182040444000390044600111075101032044850315616a03071142c400b9442a00300b980719900c00000b100ea99074039409030a911a5041d44d0801134252410000c41c00e08940340102c070701c1000c10b06c1c0d40b1200401c15035803022400100070300c0c4c1d107000d150124034400101420301031007009010b00324460010034040d000d12408213401c5c00b80e10701c0565400e0301c2181d07d00040201212030600b04414080400c6801c20214011406004103965680b6841d04201c030000c40c0e10003281c014521080c3c1b8401155044950746c0482d14169801d0074020901c680fa500702101c190030100b010b41c607090602c52640440c1a441503d0480511120102d00c0c02c460f407640c3d2110122085003501c08200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 962170359 1250 962169109 962169133
    0x90330020a2001060524090628050d110309150a110d050709050d0b06010507060b1809061308090607060618050f010909150504150e1c090602 62
    0x54001c064401003442d000003060700c45842081189041d00b111445603456940074040c62030b1204500609005561300e148410b846807682c11224014201c0281c420200801c848003085a841502d0346401c400d2643d000c912000c5174000760080d005032181a0310b003882c0c5000120103c1010301268014003120000f0a90390702d1000000c00d100100510b801c1d490b0f80c80e40e581c444107a0320a0060010480c0c10340c0301145902c1c03e01401881c11119a002521505003c1a08008140a4a000340d0466420300e07100b50764903510b0501c40040c0034600b0000703801c59003600340c200d107880c550304515001f1403446095a885850b010300282a0303011304400903185c80c104014907203d40c904a03004000c010b12400c404120782c1c0c0c0d180d180f89404500607a100317801544840403c00700640944401d40902200042045000000d841d408031020780b461000400c103130b81c0c40c08030f414041040d00359004140545030a01c120402e1080d40d0f83c44d02d1447c081c4480f58403c20380345250150180742040142d41c041c4e401012103500f50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 962171609 1250 962170359 962170361
    0x6141903020a23091519080706030f0b0306100b03040804170c01020724030e1005191112012309011805090303040b06240d0912020c03030d0b030c030709090330 70
    0xa00c1d0100403034006d03001c0011140307400c2c001103000700f000303860000d40030080500000550b040201c0c040d03c290000010041d14008410803c1c090b5880b141d24035032281d8440c030700840680310741d40100911002c6504074880d295000907a2a44425081e030959494541d508508010086405403c201c001e0300303d115001403d110f5404010080c101c041141c10002d041012801110070680380d070b0004d41c840c507522410074030050183c049040c0f40c0055551601400d2440c0064180060040d592644450fa0806441009880007021800e1005081e0340c15135960b0070540028886020f803228009041c400060008400441900d00c80c03600041480c2103030740c889041001045000503c9091115203200c401d41ca1030303543e0064203002254080c00183c001c0075046c40c5180ea4084a02002190710001c50700c50580c03004070541d0075040100101098890000c40042c3c100751200e404a50103220b02d000000c0c03c0f89003a0130500380303036000f512001940740c200a41c286004001101041c20b0400820350f9201910381 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 962172859 1250 962171609 962171629
    0x1a040507120c020c0904032303040c0303050d0b10050a021209030604032001020c06060117090c19211707051209061b160906141903020a230915 63
    0x283e2050b511300b40e2440e03001410460040c1c03010740004240b2a455603032071020741082d00e081b0b078215081e01d0440c42e00382d50ba43d0b8000e426002c001c0c10000f020400420340350344ca810006540304000c013100e0550807146001040c81e003008060b180103114414420740001c0001c1c003141c0030148054041c00b1035542d240c50550340c150302100a0303080417051741080600301e10284043c04a0407460030150003141401c1c000100600c0126203074100084020051050001001400c40342080090f41d01031118041501c8481e0b88a40c182c0c000b001c0e01003081460070508104154001d0131030310806001d0022071b0301d80302a40a50144079401405680030140465407818840094040d15000601891a040d05c000c03004040c901042c0c5d1042c5c80740c0c0900801c550760380501310644040c000606040152030f2a1000542d071018400714114007500d0885185400d1036030884822028607000340420221551307404d5007141c2c1e03620240001c1c4618031001188030882c81d007203400b41d01566806500c0b00340354041d403003001041c0034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 962174109 1250 962172859 962172881
    0x40815040809060c010608070603052208130e162120040e0f070e030703030e0301020c0304120615060e010806030a02150d05160c030f031e1a04050712 66
    0xc082c0260040d0b039460500501c1688903050000c0340c80f40c40c0c44140303032802d0600c0e040710007814240010000d42c10f110001e84a000c0080403010f000340b50b01130509003082e204e00c01c008500003003988400304240d8803001c612802111036500030007820480020807503001420902118856076031048a080ba004590800180d0081c6200c19050036044480650002e622950040070b40004020421880403030035000c217a4400700c2070400801c98040c440c0000c0c3c441d265400000c05114017440103403d1038500b5416502030450803800c50313982d25240c503480000c5802c2c6040868a960806008070500c040c1d020304103084030119141c01810403400c8005545503000182055018820340c2c8070440543c0d0313a65a005200c1c00f018440a940c1e141d00c40420080c0c0d10010000d4580380c40001c0440e0015502c611540251600340c906844400540c42c0100c002c1c218448001da100c08800401081400d0182c0c05880c030103140c02e140407640c034401010302c400e85008070754400c00308030181c2c3c4c5803800c4425074200c507922130 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 962175359 1250 962174109 962174123
    0x50d0e0a0824071e0f0206100b04053703290c0d14010312030f020f03130203030409060f05040c0f0e0f0a030209010b0705060f040b06010e22140c04081504 68
    0x540110130301c0310f2100c031003081e15001490686500e0386498041c040590000041c0540f0362929003030144141c001d2003a4440c8600800940031146401c5141c0d45440f1082c2c008200c3c031402d91503980b0040c036400d06850000783c401900c0489034547e0f1114040603580000460507501486542d03c201580540e00407132080100162544107002441c1c4154407982e02a520840070a54180180c13440102198041c4004c4c040161040151480039442101640c6e4003450007044000741001e2032000c0313429401658001c105103410480302103003c17002003200c00b0039a0800e0781c1c00c11401e03510b044100c51138a0105200c1000c01c515286152072420884103105c51500042c040369405a902e9012618010302640308150113030011444a040103401d10040d900030302941c1400085041503140d07040300403806041141404400011000720742c42d4498140b41c102c84034a4811000c003d10300c003040c041c16005c10146d0808240b1800592402080810344041e50706240041010580c1000f010414000180044d1582c0e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 962176609 1250 962175359 962175377
    0xb0601051603170903040326040305060a05091c0813020a0b0c060103110d0c090f11040b09090601030c020309040207060e1e060c030615090409050d0e0a082407 70
    0x114000d00700840200d8429999200080f07102d041d03600410001034120403035504100004c0000c103040e0926002d440c1011526019100a4440c3c041d02522607684001c0041c00340c0e004100c1d503031446901183c454601d0070300f0303503004445401c42c840414189407038030008110607402040640c035442c2e403460503261000c0d01900b0702d151141c02002c000d40045201a560740e100c2d8005000304008411039060101c010b6075050856840e03640e8408c00c403a0385016038003900780c0e9500c08200029554108414402806442c65034841e00c506202e00da07503102500a0340038502020101d00294464032542c03c0c100c00c2c581c003079818050500c0400020b5884607800761542ea450349640c00700907105000e40c1115050204180e859150741f0182c1c00c2c10414001c1c11500300d55424410403000f612580c50241c50048080d050584d184d001d400014004c1c2021304004d07001e4400c03503410b0000c1c580c01102003924040c00306c0d6800c0010750340380310300f42d914059890502e8654000c0314100c80c65180c00c0c511980c002c111400d00d600c075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 962177859 1250 962176609 962176627
    0xf0418110c0d0e06040e0705030c04030f080d230703020d060807080c0915030607110a060603060f0b0406030f0b0601110a060501090c0806010e0907021501030606032d0b060105 77
    0x25044480305920300d8000807507100802d81c010403200c1c5046415a0480e0400b40340107020340c05000003c04003c10300000100180100ca540380844000e10387c001001d01c0118051b0078001d03a07517003002c41981545460300050100742d46180500c00c0d05483c01c1d510150711595107100c200d02942040d48002e00346611180c0108000405000c1400541120802030054032616410060801000b900051940f120511150f842d900e000c240c160b400b240c10b0074040440d5142240081c644194a800070f0500c514003c0c0100400c4216006204000c0310010140001c0301785104000c2201c9062000410070380c522042d8000181803051510b44c02101410501070340c07503420104234200004014200c0d14039941f100140314800c0140708140e981d074a50315100f0780c2440d0000c00070b002e0700c80e20240c0c1ea10410304800000c020038400c000c10a4801701d46004a5005c1d6074924149010b40001d0004456510141d90f1400c0e802240c04090424a4103002954082c0001030710341e880714050240c500c0c1d04011042103807000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 962179109 1250 962177859 962177891
    0x40e070501200f0f0d110604031b0b0f0405070f18051b1903061203020303070305090705122107021e0607140d0f0806060403110607050f10110f0418 65
    0x11041e841c29004d0504041c1e0044114203044e14250000c0c00c3c001d10410020006100182c0fa507401941b506041c401054012070040b4582e507481c2c4000c0c149032500c0c040200f40d80300411641e000da4460811291019240e82095421708050b0082c0c030f15001084039141030342031894001640006c0703ca03941000c0540755064850071544203141c400542101c914101040c82d034548540002084c0319151003100c070342c1c2c66500175107910000e08400205a280c1700450100d0038144441001400014540407075002894138180e101d000d00b0360001c14440394402c110300c085681c181100c840e0f6078001e00c0b24510b81c0300c04562030340900800c3c41c00e640121040c06a440018008041c410308159140014140c0c0001060020480c0c030146c0c05c540100004982800403684441040c0c1d402d5176880315035981d40321400c2d4042140c50050841c003920340d01c10307030913803800e007240c04641c1e1900614801e40c24804a145040e8901c264801d4040030035920404100803c0300c640355010316100c0c0001114042420120010b14403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 962180359 1250 962179109 962179123
    0x60411070c0612050105130504141b1906020303010501050c0a05011103060f030a0203030904091728020d0c03080601021504060b36060d080a030b0f040e07050120 71
    0xd0741d03071600d00c81c1844a150030040b203401c040d050000034081c40d81480c0c00304200000f04200040d400d0f403941c0c00301701042034904948810505500496900042c1412010050400b8030060f601665140c0000e6080c81000c0203a81c0a44120390000c40c5540d280034011540703a881301e80340200c903015041400e40000c0c3d080c0074490f034004400001d152203080100c100b040c0711031100b070050b100780d0140c03012900584001c030990740d00034422030f80022248254106802101c234101400401d0360b00008103184030006480365801040300010560034038450982060307944450051940022413945510800043d20030420103500400610644410300a414a0316404c400240c50881e00c154460003985a1414103040c429030241c102400e0030360180b010681c0261184004a60008880600000a140c1c2e02d231150702418081d408001c8035941c042c0207000600400880240380d11030b9800001030440c40c0f500e405008038091a000251110924200040d01c3c0340701550b500c80656449031000000d18442030000d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 962181609 1250 962180359 962180363
    0x304030c0f0303090b2703030d022205010801081515060a09241403130b070c0605010506030705180102010b030106140f010c150c03020d0507020d02070f060f0806041107 74
    0x1000102e0440c58040c007018080e400072a1070807070070f120903640111060500500c1e0508a81c003880f0280351200030030300314400c2c1c0590394080350000841d070704104550440409100c40300c4100c4001c041d244c600440d040301003841410b095030b03c080814021006107000c003d07000b0040440000036200400702060064101e803420704041036410308100698418915234200c00f0000b55540c541d000941c040190028014401121844070080b001910040c0c0070b4091600d0f241c1c00c5405920103181500e4001c08113400c4613011601241094000241c41c14040e050f04c1c0202d03c0c5495103420410030241e0800c5e0788071509040744c1199201c0240075a00c0d2000e100b40006400009503560340500403e040c003004050090000d81040080c01c0d4500100e614041d800d00d09441c400b0022030001c140c1901240a030041512881c9c82d28601400d01c0400b5400040000c3c2070801d94007030381e44a564174809520000c0c400e206e801e001ca0702e00c0106d51081c0c1c1c030900c40b03141c0c8804000d0002428100c02045642650406401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 962182859 1250 962181609 962181629
    0x4050f010315021603020c09150a0603090804030812190603170309161503151a0f07150207030f0c05060117120307022b020c040903050904110306120c0f10020304030c 73
    0x1087c00c02d07050100d20180e03c413005001d8101407245500c0858140703000e900c51b0908044d42d80304d6250420941c2e0007260300035500321812945611555174145020348050340ca0240701c050421005240408500802c01165006070380c1c000007081ca159901021703800148154800e01515481c00820400610b504000c0c00c1200d03a0b9504001031500080e00b264480b401500700302062010401148940c03a500300700600540a40300d8440b034032405035840601070b00c7c500400c110001d0340319402610f100c0e40a404042d002c1c1d55284803c45013000c058686c0d00d500e20024205070080c4005006c411003000224110300b1100b0101e680e941c11862001c0c0164205440320801a002420000190b0038840c0c070003800c000e000e0740c0b0380c42d81c0d02ea003080103590b0744500103005010b2502c82e05c000052600a1f42a02c07481140904144560640070f0f007491019442159551700c22210b4014510071203800140c840c0000d14007401e000c0303040f5080d608100d40c001c480c40801c42140710402c800301c002a20784001c0720041941900e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 962184109 1250 962182859 962182873
    0x60c05010e060711070f0305070b1c0905150c1c15030818040e460b0603010c03140a051f0806040c12031211130609031104050f01031502160302 63
    0x1040c1004040d0f40002c01486e5944014400b16501040312000c840010740255907070340b00b000c0080310344d984040d032064840c0c0c41d1a040070144a40450b0400441e5034201a5061903514401400034074060310440758a80c03810004007041d40c2c09960b00c000100d24500283d018120703669526041d690b40604041ca008007038a1000f110182031a02482d00710008810103401d6034070ba03113500c48401e407003000c2610800030086054440c01420940103a810400c400c48a02e0150031035081281000d1790a40b038140c060f62802d50103211540c864400d4091041000ba000d00ea151180d41c0030310098000601003075041c00c900104e0581150300001e4a400074131194011741207604d13050130030754803001ca258003464400414111040c0007986c400702d41c1c450386842000000d4041e15140d12240e860041519084044000720004545550407081003401c42e0b2255400702c2510044100f40000c0d15001d6440501e401c149400500010b070301d0300c0e140d80d031a103c001c80040c01d242e40c148688032880e800d00800c0d030258110407 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 962185359 1250 962184109 962184137
    0x18030c06290a05040b0603041101210207050f030a0507020904050c0d0b0a0b090c09091b0408100e070e1611030304120206090f0c060a050c030a030b0109060e0604060c05010e0607 78
    0x250001e002090b08440800074010b4110206c0d0043c800100001e00c50700f0001c40105082e80140314412412501c0600403809250310070f2203000951109505440b248908017000e03440d44800012a10000701550742c081c1000c006500780050108054411980d5014400c011080e42c1c40c1c2440361003040340a00d1481d5107600701140003400720b030360020555015203209010000142c403e4022540c041400b540e80703000c1980c0b10b5800c110700c07010544c041040a40000b0b13002400307140008441094118100003081503241e0030f40b1040e0b60303005a12170042108034010010380001241c01c4411104103240c1450343c030f0718060041719400c5500490f02100c10001106000102c01c0d410400503600c422814010300720760100030351080d91000a004054419040060310400447c4124151185504040200c0c3d0b1903001d102c4010f000341c070703a0044003030000c1c442620000d2000d1191525515000c006005079240c20704100341180d00c1c1e00032810981d555922012044a001010080d061161250341d854403141d031105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 962186609 1250 962185359 962185369
    0x115350d0f020705180405030d050406020c01230a021c020706020a0f0e0f0f030c032a030304030c0905270d110a0203070b0a0903020312030a0c0318030c0629 69
    0x101c40020210343c401c010900c1643c40d0160104031484041d0000302c0e07240e4440c6002480c40c800c4094400100d070618040c4000c00019070054412188110f0003444a549884030885291000c500c11035014020070001c240307084150307802861058030b00e80c3c0d0610300c00006020701e42640c0c081b9808640d402d03400648114540e0b401341c81e1070b014011a00e0903034001420b070000500c4c441000c0c00c582c0e1094411000d41c00d01e50350204010f01b0407580c041d0945032444d041c80301104143d0151118001b55445481c0a41e01c14030b40441114162940003449c1000103040c0540074004010041200e080c0990b8003054400c40c0c0b00c1c40980d204000b0808000300b0300b2183c6140d00810651700860608a180c0c0602c411000503034000c1014000d07900c2d40740b6140e4441c640b44200700c2e0244100e60000e505401040c44101c6807003403420085108503115a02441154001da008508032488110201c1c401301c100300180b40002e201d50101c8100c103018036804031b40403c1c4000d5000c0500720314404a02c1d00c0c200491411141d00341 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 962187859 1250 962186609 962186627
    0x120301150f0c080d1104050406180b0303070b15010e09180115050a030b1504060303200d0804030f1e0201060602011409061f0909060b0102010e0115350d 67
    0x150346804450b90300a9950203070540210020300e0040d40d19048008600c16410341035600500009005000c41c13036a4442c0303001c1c1d9010035200d001c4201d044c84200c510f14180007003180e0030380d43c2c820028803a5549600f41312820100e02d020280c1000041d6840800d00e54540c000343e40550a81c40c10148200c20f02f51150342180c051118240c1c42404240702004076640d03500c0c0001c1102d8200304440d141e5500c01c40b2141c0c40c04020742441e6800340c58100003009042c1e00800d840400300480348060701032903a00016039a22465441e0042c0000d448100040000b4810000c00d40040c1c814200b480c402c0c01240700000c0b030801c2501034400180e54613141040016824055801d4201c08048a8200d5041c07420300c45403520710041003038440c3c203204008095001d2038441c0030402041c8220080080141a10302800a8004d002406005600300780010f02c02d10010b12490106440010307658030007510b094500d11b0b0180803000c84410807222002011020044040d050b10302c1800c1ca0003402d000208202c02400d07040c0c0e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 962189109 1250 962187859 962187887
    0x10506010f2307080711090a11040501110f010509010e2a0f01023301080619050a1512020103060f080a15110d06080c0103090201050d0e12030115 64
    0x85680141c821490304000107503202503001c001c0e01185684190840401e10803003074014082d41d00000d05070140b00b000e50501c05411400c561203420b98940110420a40c0d202404528050310100310401c020360151038804c00a9902d4400e89220600c20004142100c1080b610030909035112580005c402c00144080b2324480e0b80500600c0c503034903011918404030180782100c5400351a000f10369000680c02003002030343d440154914000004500c0b0321141601c90748241c04035000076010000706c0e2052010078242e1040d00404410b480c40840700340794002034007001d8401e409556481c1500c0302c0c01020000044050311143c01c0c1c504c9010402c2c800101100c805610500484504400c28840c60001041005505400003800746041248441440c0100200409509404000070b408201c502ca1908104100d03812101a1802c0d9100000154161041d5020080c0040c20800100387d450340c0b19448404000c068070b04a0320500140e040d00c3c42c0e15170081c0c000040024202d4a140c0409611805c8841540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 962190359 1250 962189109 962189117
    0x15010f030903091e181505040c021f020d0903020102090f040605030706260f0712680a0f0807060b0a06030c0306090b1804050c04020703090801050601 66
    0x451240c8004010300d140713003c0d4100200d0881c09040d40820560040c1c00a0401e0594a02c2e600b00b400f0000002010300c0e1020311004c0219000004040c030b894860322007020b29a402a141700c0c481c00c140074814401030b60440c003032030343c0c2071041500c101c01c9446101d85a611a4000503a551402400c00290000c400901881142460828041c54130081075440031902582001020754120403540c20343c10504041084550f0316040c10401e00340749818001e400f0301b4051312034500081c8000740d8601aa52403240580c801c0504842030203c082400c10f04194420524158110050503d080000180c506006072000c0c070320640e0882030b0000c0a000c484801503014801020040ca90b0b580d0040d80c3e05082c100640b00319800708003c0f00303101540c2c21a0540c807400500b505203940d01e481d0050014903011802e00002440c1a50104441995208051141c034008240406510703140c1e00102e030b2000010400c941074044c011f143c0001e6281ca0000d04045846034030784d00c030072904000380c881c21594002c04140c100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 962191609 1250 962190359 962190371
    0x7051815210a15030209090a0204020a0e010f2c120307050705120304120f020418050f07090b060f0a091a043602090a0314071e0b09010804060603020915010f03 70
    0x84103c400040c00f00d0380d042d94603913034569620b240b0500788100c1401c0a900170303000090b185000340e0300c0081d07602c10110980340c01c05c0c4840d00c01811160b12042d0100c0848408202c40180d402d1050115000818400101114900e0b00d2560785181550041901102e8682c0310b54828041850035260301e0800c03044034002141802c0c41c12202441a04440070702400d01106d1104200954440341c110b441c1c04060304003074044078a6149045666101d8200241031349015010300402c0040d11406005c41c0d40a00030081c40c28490101040416988021007074811b00c45004c400095403d0315104400e945400004c03d9900c480ca88101d207007150342400303603078001583c01002c480b020082c2001c601c4e40a4a1031100181c9488100300030514440280d04007a0000c191030354500c0d41400c1c00030b020f1080d01c1110014120142d0b4094102104202d1405451103905003808007482d954031032101c49500c24040c2d4004240f003540c2e5000309207141026540000c400080c1c103801110b650700511510941c81c0e0318641000300c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 962192859 1250 962191609 962191631
    0x90204050a120302150a09140f061e061903050f0102040914010302030613170d02190e061b120d09020a0605040b07062f19020607051815210a 62
    0x11101d60000404104581d017011555041d180d5000c015025800308031422009030a1800550700c4108284d1140284102e1001032050398100da0f1040c5504003000d1002c1c501c1e21074804200001d00c595019800c120f401c0c541c0040440e4041081c0c0c006c0031882070005030355900b04290361099400c044000b0300101040c500400050b10000b5a4507800a48201c600082035480d190554980d0103100311750086140205001040709200d44c001c1004007080140e03031098000240341541c04444150344980d004000340300c61a80102d07010120459003088000783c1741445c2622841d01c00603000118502c0f0503554523040041181414030804c00500081e00b091414070b46810f80800c0c9910031544000c002c40d03154118a000810120b40c20900f11482001031010070004401243d030a0304404422140e52400c0c407000c00e000b500200380d550058465941d01460001c917651a4100c1e0300c1a240070030340000202d40c81841d00d0b440003001e0302a02d000b0b020708165600c003603461803448910140007440038501d05030800381 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 962194109 1250 962192859 962192863
    0x5071d0d080f030405070306060b1206120703030f05160f0b0f06030c01050c0703020a0b0c070b0304050615030f060906070f36090e0c01030c030e1b06070606090204050a120302 77
    0x2c0d42070400c0407840d90b2a552460100e0901496500c0202950700340400403480c142404003404000c401c2c5264ac200503039629003080341c402e030004d4142c909600820301c00e00100707100300c40d130b44001c030310b58108039151581c0400d13181c0300d01d804244c00317a8820540e000c0340c4080000616450b038205010702c100c51050b0402400103510b5548401c040340c10f0210008400c14040320912040c00191340050200500c182c7d9800c00c60800d90010407400d44074003807a480440c160040340c0c1940d0055070090020701d11661034029020407031035000b2402d58188180d121a0113000c6042014900ca040302101612950070107860103850401c01c20031200501000212500d0703600540824006440c90201c083c140c041180c90000d001580c0a820044030075040c900d20301038140700010030a1200100f0f0303808006030022080200c01300c600c00078a103601703900b20707040f07012900c4a502d054604041c8000e000c20700d854103a5460b94210350741c1d548207a21554020a01b0071452a11a003600300515400061000e903442c141e90082d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 962195359 1250 962194109 962194117
    0x2e090b01020c1810030b131e0305040506070c0e0403120b1c0206030a020c0703050705010f0518040b03250e010f0b040603050c070f051b0105131208090405071d0d08 72
    0x4800e00000002844c5664461401801075421203d0702c0f21071309003055200a03100c0d2605003525841520f0380c2c030003060070081c500c1c020f03600d40580d2003a04141c24a403c0100e40d0f070100d28240c501e80300001011074108411048039003e10702c01c0e2075107590031407000400700c2030b42c4810b500c079889683e928000d1060b0088017690b0606941d03048890703969942c5e074110900002d000d8003462007598440c100c00071003000f40000d1518151102604c9000100c2c203124003c5819204210007100554610312980348181440d40000040440060a41e2051450803505101e5120816124144006414400c00046940742d03105070140c82046100340005061108440107403003540b044500301995540004e01000c403a0041e6504103505c46000c0e010880306040180d910401c2e5002480254039114615103158061411a0f21452141540302000c0e0720b0724507400240141414103031400c0108010b240c5060307450341315440c0f042800381c6940410b0b41c210302c07003103040a1b541d0028602580c079120140e00450240c40c299 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 962196609 1250 962195359 962195389
    0x1401030b06180603190507050d061a191e12060b0405010203190c020d0c23100513030c0e040b0702031303140a02042903030909010303082e090b01020c 66
    0x4544d0307988804030600c00800104c41c10590725440d017818400c2481d4404014003803012225420312519484810f640114000d182c3c08600d090020092031001d000300380b0400503005814101044c0c040c42204424485090b802c48110001da600410698a202c1034407490010f0544080c0ca98245400c00b00040d50303a11840c0c005030410b10340314000d00107080c032482c591303852254040c0c14241c42d40b0301c03440e0814450070b55001c1c2c0d13403000f2800030709200d04440c849001582020002c00c464080185400c00b40c0d00d03988070244030f20100c400c0301000310120319800c603100000c8c41780349011002450130f0b0500daa4555000740c02801150010802151141c10304210601600d404c004200e075134840040e1403c0ca0300e240f04030000e41290800c7c11002e00c0c0c40c1c41c00520200907200300c10b1001000058000c1544078401d48114590040003403006002080c441d0b2a9980e200e25160102c507080622840020301d1510600012555160440c10600003220b9501503014600f400780000e01c0f13198040c1000850400c040302c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 962197859 1250 962196609 962196619
    0x91a0306010e03030c0a060911030a03020a06240803040f080a1a07031407020115290930010c0302030906040b0601050f040f05090906041a0703151401030b0618 70
    0x104010980d8213008444050704c4040844880329818a07200c0090469800292280b030791100e1400c800c1d06010891700f024a41c1170b405051080381d10303035903c4e000b401c090190f010441061020010719aa11410843c040c11046e801152100d207802c10b0440c080c400c54124082541048121034000b60140104e00c2400030f1883c030f0842c041d42d40f25003c8000300300d10049010f01800170400d2110298040d800680c0d00c01808001d44c09030340d01d03210741e45041701000300300c5500c102c0c444202540e02d9440c10090846a04024080403c40001d080c10343c0c9803146d4501d84000ca031102000c0103131149800d00c1a01c91141080c14194154548400016100c9400400290504003480c0008006078491000c03224841005240c0c030780c9a540312581000001410300031540a07800c80404141c1d8035400140d2248070380e500581c404013002413241e480441c1342c000303400384040c1078031600c0040c004d015840d95000640404d20f0b406019040120004054401c40c10b100340c010581002007505c0503c01d1101201c1c0103900b651 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 962199109 1250 962197859 962197877
    0x607060e0c0a1404050114010210090c050a060207060f02010515010f03090819020f010e0304051908011d0610050a051e060c03090306100f050d020d061506091a030601 73
    0x22a181000e4420040340c0d03100310302c0d0380c010440304200b0f00d05a4503248182c40401241e030303c40483c41003402101e00058003581c4a0102c0d02c070743d041e150b000b14181c10702c5501880f015aa4038408102502c485030094000340e0002202400f55680c4a40c44c01b1080325903100910460170650b1240c2010000c4103031140c1009901c00450a4003030080e04103444060b17000c4030690342c070401c1500d00550b80080f0000c100042c0909441c06080c0d0505000d014010b5011101842c03615103000104280205101740841c60003100400020340e8150070300c00d8050444000c440000b100201c86012801c00030020901c4144008840f024071003a1607002c0c045040d10000c1c1c8a0541e003003100800280030009541c20154003c0d0b00203820500c805000c40504090720060301100c4458036403a8021010807081d004051064450020401c000d2502641d2052460300140c9050304079044d680340d403000d0380c00c0129800c42009184c00100101c0f544542ca00d00100260602d5140003008500c028005100103000203040020180c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 962200359 1250 962199109 962199131
    0x1003031704230c010e090f06040c0908060c0306040605012d020307051609150e130809041505010e040e120a050408060a1505061c2a02060a0515060706 66
    0x2c00398075001800d80c8020981034a0340c40e080c0f40d8406a10000318000344040b5404e007a01e00300080c00c0c1c0d002d1000702001043c0d030390324841840002d0244024100410100400000340b0f07440c03d0194600031740d04000f9117507892a0080034001640d6541d8000f13410005840a0900c4262001144540c520444100c00324824016001217155020716a00a06540150940c0180e80140c00050104403004c2000521080c4820054210010481c0c031a8540c0500a4800142a0824003d00c003030351038441c9052500b01802440450202c0d4018280e00000c4100520188159a041008100405003c440601400502003a13903a1100307024103881034654000f10f1114051800b035400d031400b402ca00c4041740c0c950314240000c0409807460407940c400780e03010001d0102d05400d10400315100118003602c1c80f0041506042d902c1c00030103030640000f00c100c006264140c003c108682051440501e6a0700411550a0100d1301c001215000303440010700f5000303184424110340b5854140c070380d155006480010300d1050342d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 962201609 1250 962200359 962200373
    0x4050c180409051e031305120a2a0905060909010b1e060d0c080703060b0a0504181b09081504050c120f072418050f12070306050f1003031704 62
    0x1110030713610181111195000420000014000000246002d0302d0101ea8802c180851a2405c1034440e040d90070000850010680d01c90300ca004d50040051200b802c00036a078041c0d07070780e414241c102d416040d0300c078000d00c55a841e0280046030025214002004003500700e0000561419191414092059024440c0c440594445090302c0320800118410700115106d803200520240040f1030a40100e890020040340440c40350f8185e9495a0640e1101490f0504000014070610a4080c01c01c50b41c0744c03504810b02c1d800101a5810500c0790039501c562410754180845c140c1020303403400c041c050041104c0101b0020510021f07100301e85013001d1b11031490078100070300f589007051500b054913490392086400004042d00310440300b018030f031006040d1807901e0401c0403040310a014506411441880d482505125a241500c40d01e00e50305c038010700e00600c94100c0c101182c20004241c0c400d9940b90380d50303020070840b14000c2040e00d074480103c0850300401410b641d00034200c2d403001d07007c0744610444000014100828 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 962202859 1250 962201609 962201623
    0x31407230910020c03151e06120f030a0f11060a02031e091501120b07050d2405120307150f2a090828051f090204050c18040905 56
    0xc0602482c1e14806040c80107503552841c568014013a00c00c0c100c015240c40310001602d805004049482681d800244404c01d4000101400c483d41c00070844800c040c07070440411000c41c85071403d1001d151110005880580700100b112424010712001d09002c2c1403170303800441c003a0360106e400d110041e00da803601c40f9803410880c0c114009401000c281030500040c4d010000c1c00101a0112404c0e0b8000740c0e880b0401d43c0b10032485118010b101d8403946000c14000c90086000e03003400c1c0c400c9400001c64842078141d01300415a0404410f0034007801141c01c0c8a2810084415044002d1800040d0300c0d048041ea02c002002c145c0041204000380d4640e85105900e6407900100d00b0209400f1074801f180d1348031210f40d0414090b110030a00452010302d40000c15103400300f50110017807645c0040c030031000e51501200d281260525421580c2c1e004814102c3d612000c4e141c500c0141511441000420282c2441804201c60014004600c4110306100305250581030074511410035009517804100540e103458582d15090b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 962204109 1250 962202859 962202877
    0x111091f0e0909010b0301050c07080703111603030e0307120b0118020f0a020c030c040c1b0609081303050d050403020904110d02040e0c0f0f0d030c0809040204060f03140723 76
    0x11100b040c0410800150880f110b000e000318001c0086845000c250030080c8694400140488810300c59400484e010341c50790b00c50340c00000207440111580c0c0309510440344507600102c000c54001c04903102d450030200000800380203142e00560340210552101444007005124070000c3e1552450a82d04230500382d01a2146503100003080754a80c10003400194032903075048070b618002d2151524000c02ca00c0c06014138400803029440b10f0070005074080d42c107107005a000409031803054451081c44001000c0100404050218541c02c21085043d450103078202010081d1440801909001c10b00150356251042c1c0d4000303510902501c1248a180085000740d035500402960182ca088103204010101084ad1a000801100d40244881c1c0c4d41042240c00c00722001c00c0c41c2c1211440080800082c01411084800f1f07015544040c20700b60300700001360a80e406904030360006404200000310086d01030081d0460f406804041582a14000b40000c000c1e20365112500700d08020b03002108c0302c1059480460300204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 962205359 1250 962204109 962204119
    0xa0c031e15060302011803021324030c061101063005101e06230315010315052206020924210c1909081e0111091f0e 51
    0x9060300100c0002c00d02d5100681c00314410440265013146080074020a0741d034010121503100e81516100704c010030094640b21080154007920080300400b00120f40d00440c4507001b0314691605000000f8541000c8a55400d12a030500d001400403c030a03116400081ca90401804529003880c1c844c031204020007080606103000d12421070041d0b041d00d070072400d100b00d80e03071041c42d84000440c030b60b00040301c000e4410415682540000000290041031502036038281c01803c40313940c80b15002040340c000000382d104840740401440c4900880d407041c01010350041c2103980e030b403089000780e40d00c0c0b241c5140107020090159038001002d182aa54010790426890240f071300504c03560b0801d81b003c51440d8001c10150304045a00c2202d42800000540110302c13406200000c0340c01e2280030307050320b00d9a250010030070003404200380c40418061800c20542e504c146c045200301c0e248280103003556003180d458800c2c11042280400c144101515440000c40748150390308402c03c610700b4150300031550354000360381d013a03444 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 962206609 1250 962205359 962205383
    0x203070f030c080c07060810030c140f090c180406051806030f0f0106051f0c03030b030703080a180905060d1401021926060a09050702120d020a0806030a0c031e 70
    0x6090001005c8090b40d41d81e440c1d000d01034442031180d45044c865444002c2046400c110240121680f4214403c8020300141c101c000c0b40c0b802c040000e660040456101e42040c5002c600311241c0e00759030400d1010340a0541c1c0c2003240a00703120101d4046c104801c003000420f43c606010602946003000300c0820708441e0001d480710781c1e40740002c540c040c0c120351184a216500034035090319085419a1422034910030740d181d02000070a295000d502804a0050741545809800f80000c08141e100d0b004086800103585e0b02e920400c4004415000a00d0a4002903041442c0004020036030711041c0c4075681060308040c9036043c0303100340c0041a01900c142240b05582c010300b86440b10300c0a4104904416911039010354542035030b070501c01150348040403642c881e4048030900007080322110b1030b4072868108040e4810f0307907840308000d04042e4060307000142c068816030307000900701798a07a440505550000d00460103018070039400d03100da414000b014040644803072100d00d003460310503142c036482460481e408a01d10601e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 962207859 1250 962206609 962206627
    0x933140307170105060a0206130f08040b0d0f0c0806010c050c040c0c03090902030c071e06050c0309070f180e160b03150102061b09010306030204021216020a030203070f030c08 77
    0xb490480030100881e60000c0c0d03001040701c0c03070941c060301d10188507039005042c1555003480340c80c030b60140c0720029154140c4040151002c01c40b0b000c0204080c0c100001156942c0740c1550030901201c08030941f1701d0a151074a05146900781e8415070050b008102460195403000d003d080c5103003800c0c017a40c001d50b030003460b22200d900ae494101a91041c4940684c4900c00d180703a41c0e040480c140d102c1100c850160010030065507002410f1055103140d002035151105420500c282d03100d00840302d05840442010300f0110070000f18030010882da0700a0712080c03821520040c0341c100500d61181064444c001c8640d160032000515520811110042c015040c6201e00c030203030340b0425540954016600d001c450410300c00f05816030350001600c24029010111300c60b00d00c14202c00e010b1f07007503040b02c8842070400d6155180003015981f5400034041c850001c0ba69491395051144030516581e20300302e54001590030030085000440c1c0c01000b0713112960340241501c044108030f490100c80d414450316000300491000b0840b560 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 962209109 1250 962207859 962207867
    0x31b03150405310602070605151c020612090c030a030e040b0a060203090d03020715120c0207030309030b0405030d1805011d0a060e1c050a0933140307 66
    0x8090006560070091622141d070b14030100103c0c0002003031460101c501182c1250245000384000d54000c0d07900500f880081d40e15070055402c00e54600ea1107402841c1207251a02e4070b490500c4039501008151000c00055501003504c6004004007288034540d01b100103041070740c0500003070001d214010240c84c850b14680c54050f044012207480203021f00d00e050000500d50902c1c2c0194025101d040d001181000b0301c0108000c1d03508090f20044007140201400051560f02c00481400c108105454800513903002d141c003c0202d81c0106401300c115882443d00b040400c2d08148004207903500304081d001242d40d14280329113035105440700182140e10301039803041c2c2c01542c60040000366110780000d020344a0080305402940310f1110203a41150450f41c251000511503501032034030428690b00341c0740110004030041d407040d1181d10008000c900c0002e080b4004550101c507640140268410341d400c4074151406c0343c0b10404018032990300080003c020f2a044030f00903c0c14140c0f8400400034281e0303d05c0c0c0341c03034020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 962210359 1250 962209109 962209141
    0x724140d23010803030c030a0c0306030c0b040e090c01050a0c06060b0f0705060702061513090c0605040608070201020f1608120103140d020a05102d0203180c0114031b03 74
    0x8a079460701e000100e2000d41c0841241e0091405882d000d0440e1600d5408d90010401d41c0007035800d040d03980c8c1d07000000551410340c440c010601c8070006600c5500e041d00954002703c0082851210ba0007100d020a1184c0e04201a103815290754681031030510b00c2c41c500070005120503003115180080100348000203051800042103903038402d9054030039544400c0340988c5e641c601500d03039075160001008045400d0820300305a18002c4280e000200c0da00c42c440d01d41c140300148540218000603000103040c00400d801245154001100d0b1008510340203a20318402d0782400f8001c020840700e00004030800c2400920030903501c0711328105d0003859036941d42e031800303a041000b0800d40c00e81d24002d10250708500760012450b00105034011010f8110240750300030580003404031008640c1c02444541d40505483d400b0109007613204000d00c00141d8034200751010710f40780001154080d05a601070440300c102a6130004000710310040c100070983c3c407500d813060050a50302491500d00e1317005002000700500600000410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 962211609 1250 962210359 962210411
    0xc0f01061509090e0a060f022104020315070c03030c0509030f0c01020f121c060e0c07020312090619050405031203061905031908090405180724140d 65
    0x41040b00c0e0364118440566600c0194150340d600300807201404030380c80343c02402602c10303ea0401854002c03910601e007451920032060100d202c102504120031828100a01845100106c00700c010034500404000e00314a070081006003050348541800195500070000d40305a00d00003020307103444503c4095456030350100b44001174014400c0d0f1040c45040070001c01c002402210441d103040c540030009554403c2c038044c0c0d001040e030300f59540303400044444441c183c0718010a02c041400e07546018070b004042ca848548229242403034810046e00710b165031182c0456000e25001880c00740181581c3c03c050340c0c580036030740c01140c042c0260040c00b25031941c400020340c420b20003114440002c035040b052801c4401454003449425904c0a40d520b4080f118110504161034428500103140000324004281035032010340e07100c0c0c250118580b50fa061204188203940203068035184601c2c40d00c1e00341c0c03140301d003800d1108100410b100600c1c071001c1d00e443c001d0b001c4030b203420186a814802c0c0c07030128030b4144a0001103005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 962212859 1250 962211609 962211617
    0x60c0a0525030503091501060e060f04120f2d140a1401090303060f06140d06180b120d020d0c050a0204050c0a2a020103112a0c0f150c0f010615 63
    0x100e0b401a068600d450b605940455627908810780915003801847d90114400d405005014080040c070300c0050b01e00c5004031440382d03080345550f04140c54002c00701000c22903007102c0059100324941032034001c051020303909a08640603000b096003800e03d0609080c450f90300502003c07100f80d600840c030340c0150042d1841e01d10907a0308102d881e0303503100403941000c0c0a004400c00102c968070150344074401c200140404ca8104000000c0c00d0b82d0b40c60b11782d9078510261441e0503010307488004410542c039110003031174100c08103180502000c0c002210001d49a1120886400034030060b54400c0e8107011003000b0b001d44a0b51f000c1c01c10440780c2004c50448000f81c000d11400e0b0001b421320560010000c1203159241341a0950300d50032a88820182e00540141c0005060754075841d10a1140c0c0600c0540c0031400340b54400404003500d0303a0703d80d1105050a1994005400c1c2c000e00741002001c0c0c0b40e80f50051890301004904504170345810680c601c0d80e0814145883c01212503003800e201064900507100e41002014864403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 962214109 1250 962212859 962212873
    0x90c030209120a1104020f070632060f0108040c08012c01181e0503121503030f04061428030b0a050904060b0103020c07080c031608100c0201020f0406020601090509060c0a052503050309 81
    0x3011140d0031104482d0550803014260f200b8002c2e5000e40301c2d840d001032140c040340e901e10d13803149115400c5840c048200c805035812496071b40088845010144100840c0c14020300100891040044001e031b04050b00800203610313216100c041c4020a0030040c03050742d104003682d646941119500800303882c00d5402c200865030326811550945400003c030307601c540403100d0442c01c10740340c00c506a5190f001c1a652070007003c810450001e031951040d5402c0c0c02c07164a90400b85a003e01c00c80002d040f11440d5441c0d41c015002c005d030034441d541d07540c601d4a85c016407008000c6165020040100c029015010645005200c1d14102181d41d6902056601d501e402c2034084070041c03000311300d00d4080f40d03e045c81600311356040744850541e0410950441c4100c1c8117940000b40c500f4006880700000c075441540090010b0b00200010310040e0000d000d90b0760405890001002c240c1440c00e270b228042d109080160b02442130014200d18041505520807000550404080e80c580d03d05040140c40b07a40202eaa06030030340280c403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 962215359 1250 962214109 962214191
    0x60f0e30070b12040303021321140f070311031203040503030f0f0402060d150302150c01061403030a05250b0603060604290a090c030209120a1104020f0706 68
    0x141c16030300041d401001192075a01c485c0c6040d00298054601603420803c440c4010409181000000c000c200c00c000d00c0520aa4003030416070754070103410350803c2c0c2580201c03190201424000450406403a04041c0c181681c00f900c800180c60140055020040c2d2031010040006000b404405140b00c3c1001d100840e00507920342c040c602854130308942c003d500000a02680d003103e181548039521130800c42d0801c11204d600c03038002031010420501048032070640001d101c01585000e0007400c0c020107890030007e62048917100003c1d124000c81b56140c04100001c10b00d5460303440c40c403030103440004036240b1551034901036041200c1e00500c11030b00ca900134410003000c150103003007a120b070702034400c0548600c02c550404418007060032202c0040c580e500c50480500803414198a120341c0081340c440d0303140107944481100034086480702080310303103115420030458003020821030300d646244004125001a035480240e0389981ca24002e00c2c2000e0206032a01c11200791110507981814107081c0084008180e8007420 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 962216609 1250 962215359 962215379
    0x131502150c030615090607050a080a140301030c090b2d150c070303030b13020310031e080306010e0607080c0a06062c061f02071509060f0e3007 63
    0x64501c5030300702c11005800c04e180b84001e0040c02040d040280050b10b4204d264a60b0351a01240d1501a1007041000494121090b04400e410368500c2408030624155031641d21890304e40c20603031040745815515074841070072030b40c0c4003101c50034408000206914680b0b80c0c000e242c1c000340304c00201e0078040d0b81c030350081c400c4010400066170b10450f461002406000e0031135504070040c12840c5006a0000b0081a42440108090018511444503a402c0d034502e42d256040030b00464117415040c0e071000b8090305584010510000807251300000a0130542c118401c0e02012402510581401038810b01b00419102c0c05018085005100c2c540a20001c1c011b60b51a004120895010101c2c500c605400110291019440b8110070350340c0044010903109801201c03869100303c003aa0100794a005802400081c01007101000d400b00111030307182b410800181c100f4802405500e15958540148003201701e451a00d41c3d0b0b12044100301000070144030300014000e410042e80349903013a041c40118098624003140000352 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 962217859 1250 962216609 962216611
    0xf0506102307051501060c0f03110309060d0b011409030c0d0206091c03180e15151308070e220611030430020d05131502150c03 56
    0xd0100d140204924815a04801092076056148100241034081c120707800018261450185010382010b88000c19031880700281604544c0912242c602d400000c904d050b40000c0140d50706040202c0418060391406140d4020644155072100c400148547e00094503045004064020b880340c0404840101803224107015400c51181c059120801d040b0507864003400707a8216500241c5081d02d864030300b10201d014072164894604c0000380ca10810820140d0017000c000f00d00c40c171400b0800d405070400700840e50120000c0c200850496114424206a690b40c0d004155410380306801d181e600e0494481c1941e140f1442d214441d0b49005a01c0001024407074180305500c02c0345080304142e4040540020b00d408940c081c80242c60441d0342c0c0a009600855030001540202e0281c0e540b02100c010128010100c041007a010010f584003a410054046800203117851681d50707d403c1c555142c980650820f40d611140f40c2c08000e0340078540d143c441c4950b40201b040c000b00015040600c080e030307413070402c0040f0700d05c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 962219109 1250 962217859 962217871
    0x9100e030618033f01050a1706040204050717010e16030e190c030503030a0b0a050402070218130c0e090607050a140d0920030705040c08040f0f020316090f05 69
    0x40000d4801195000d04084954040c1c480c280366121486061030210b8813040c601020746201c0400510031803400d10000c50040c00010414148412040c59407501c5042c0904001c0c0101d07254000704080341d000c2c010958143d108414003200660b91000e1000c070b988000d4450a5101d035841480c030100605c24050504200d40700b500820300e00c0380c00d01103906041260038050700c00101015020000440500086014107020034002c5001001c03481001414035143c1e102c3e82c4103920401030100140c031000c00341c8412045c501420038190391140032001d910f0340d40c4c5a0091204290400101d80f0614141e0341e24011081c0100300e40c5955109902661644203000d142c4011071034200c152180d1155500c001d018001640002055410041c2c0c0c809000f8002c0c00c101c58820b0714820401e0f00302c1d0a042001c18010b1904480034416036241042c003912006000d0b001820030380010610500748000c0f00d000201059010702100e08603808035a80c410400302c0e40c0a002c001a08040780007203070000398020640641 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 962220359 1250 962219109 962219113
    0x50d0908150112170d0b0307060f120f06090c050705060606161403190804020f010e0d0215070503040b0a02010b03010b0117091c03020d05010b120103080a0509100e030618 75
    0x64206400c00c6207000c3c181c9800c8411429400b000c0d040c9441c01400792902c50300b0b0b48408184061030b14209818840c0e40d0b00310300704000d0007217012202140d000c040c4203116142d43c40001402039800200c0f90180895400c04560142800c0c4030000881d800001005814043c074161896501c0314801c00459200b2010b070460351580e0490002c0c0030a04103688000349400e000d040f01d144c01d560420340060700001084840c0400c3e840c1041005609015030b00b5424400c00b460254241860f41c0f001410f010030411001e4050b002c10304402003140031410480d83c1994000c02140d0321941c2c0c408401c05250b120b4403a02006500302508a505410140a950481d40341611000640d1095040c0d480040b08018004840752207040725921000c990445c10042150240e0340150356420b840c1494016a40184e00c41320350f0182c10011000c140a8010245054035070000701c3c1656070011500803a464090012030a500c00c82800074400100c4c0c010450600c00c1c0d40907415100c0790b50b600500c03583c140b0522484003902d9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 962221609 1250 962220359 962220361
    0x8340f080f2a090a0906061206150302070314030f041a06010c0312090c150933090b0a080a0b041a090a0e06040f0302151012020616050d090815 63
    0x7002418101030290b0b036203618140c1c10580c4030f0000507a42a143da21100302c403541c84100380401c40c0e01c01380f281c460f030340903135814000185402d901401021135000c40d10101540803a40c50304051084002040f4507000c00001ea03101c0c1001c440300034800c481a00d04952a60200e80e0984044c0ca80030081486114141c480d41703841c91454400790b900c0009000c0080740280d5608984001407070000c2d405000d010a40c140c4080d00c07a030300e41c014003449542e400c00c0b0010100001d580c04500c401640fa9100d0b403036800141e00485003d00c0068411566940000f00440c6010518104c4503600c424018400c0c580b1082c1846584010b105000454100c000d02030030841b03840c41d256a650510001840d0482c4e6030540c0080c80507080c52010b410718106030303800c03207400325905091400c2c141c4c10010903181000c11f00d00b601503030402c0d680300c01c481d442500c50740030051102c07002e52040d03584580070b0ba2130085036a01c2da00044589440c001d52100c0c1d1001c21103011503610b60b800318080c1c0c0f00151250255801c403220b1130b01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 962222859 1250 962221609 962221651
    0x17030306040c17041205040816030b0c07020a1a1c02030405010605060403080a0e1201110c060906010b12040302010b0604060c12230903120a0908190308340f080f 71
    0x80a417401d04210900508110001d101d410070040120b5104c6950302c28044241035250281410801410301c40340034a090100f040581e440c0c00c07140c400c444c135402c501e02100f0381040303001c822402010340c01020082e025905101054858008511482c4100001c22030180c48000b007007154051400041c000c00e030148400041a40174201d60210010000d00045804c0c0102d00040c0c00c1d5401c43c40e0340e800c914004900986c20b032200b0400150403500c0d0202400c2c0035810920803103528020a03429101e00401000403406041c001e42c00110801c5026014507600ca488802c00780525480840417070b100c000c03a0000c02d082a1044a5003442102040b01c45070139050404a10071030b64020800c5e01d0b9040c01407235440d480503d4070b1402040020196240c80000324900009181850001041c400394080e03007418003c0060350040b155540040c0d0b04841d500040100d010004a03500414124428a440c8485409106402a811f00b4241c803d43c0d03604c000035036070703014900103032401500c013070a0b40c21030300c000909 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 962224109 1250 962222859 962222873
    0x71202130501050306150c030d060b0a080c0706140103120809010e0309060d1b030e070e060f2809050a060501050403051b01021204030c14030624060417030306040c1704 74
    0xd00a07400801b22484410006030a02140d40403014a10155100084106968045000d03400003094406042400c028076083d015124010040c042140720030000380744000c018103607110702106c810302c0051101c00c0d1303184d2600311400030700c110445004c0f680c0c2c4000500d040c2d005000c0c9011620f000f0000d14100400c00701407001d1354020101c51104c9540320a540985800995807445000442d41d07804600c5000f9403600030306084441d04201d1a543c000010003503192034040313100c002240b00f6540440081d10003010741c00e06040e80c42d080041c813140c0c04800511616141c100d02e024503030600b8100b207001d503103900655241c4640d12005203603412805140d100040104c1010a800406005403500c03003204100c101ca0301c2d807158000b200e10003480c40c020f008170305030400b00d030416060590050074203051840c00ca41c1241401540340d009044540680074640c0c94150958000b80120088140ea01d001c800e03410707072030340c04c21111180514608482010724501c0342112000400e02a44490170685550329241 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 962225359 1250 962224109 962224111
    0x1050306010c050105160f080702030909150d030f02010b04091e050c0d031e05030403120e0f0f060103021206190b03030405280506093d02060712021305010503 70
    0x1e0601c02982c1811001c07036030a0084c0c500c030311002c880786052014101e10280124000c0c82e0b80d401040703030f0881001020f81c1c000085464282040381d204d5203582c3c4d001a80e20300c520303040200d550002c10a001e160100b640000d03e540e114807458000340000034099090200700da4885402624002c4800c42d0103a4181c8503092000c0746074003a500b40c54081c0134200210b8000c00c611441240040c00340d000389040c050702140d0301c02c030990343c1e07180051035410142c80060121450803040101c8651342c54031844441003c008a01c403141200043d5600c8581070541d540d281c036404d220503801014060f001c505248400f050080c482d2080c814540480c10102c01e40e4401012451a040e8042c8420840807480c0d41e5607442071447d120300c408105080141c80001116803401a900c924002c0009100c0d802c06139440501c11113000803405060740003140421100500348054020381090080d02c0381c0703c1d203c01c0390b0204107030342f0a280b103803941c1e0041c941c540e81d484200d01c51007210030410040340301700b80415807040000f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 962226609 1250 962225359 962225371
    0x6080604090c0f2c0105040c090801050a0e010f020301033504091d2a04060306050408040512060f06280e10060c0b0a050403090308030c09042702010503 67
    0x418142035030b21505600283d8101820740489000200031003c004036900b2011204892100b03140011100d041ca8840c0060141610454588100c0160300e48901804001040403400900260800c541141c00508898160548950904d00c044820300424000c4a041300e600501c501929100c2c3d807020b0321350718942c40b40c501c1e1b00109101c0540c0c1d8003d450b13019002601100000160400c030f0320326882500000c80700700c542950080f500001030301e0b840c12403101e6810810039001d08403198002c0007800914141d000140300c00c0c6840c0502c0b0600c6022005071003a0362045d184200101803803040700d40d44100071190750310111120341c00241e0509000c00c40303440248403002090f030046035000c2e681440400541228000d220603004106039840c0c807020308070080c0500c3c00c003245204140d40700c0000308100245540361041d2a0008a000c042c0f00c2d80c00440150780020f0390585071300709180440000c2c2d02004c41d407803080341405105040c1d01c5006000204080d241052074080c3d045503801900c15801c02084 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 962227859 1250 962226609 962226611
    0x120303110706020316080618010506130810020901021203100308160f030c031e120c090b0a030506040b040203010b0a0c03020c0d03021c050c07291204021e010906080604 74
    0x485002a0300b034009140503002084141c031991000460040a0600041519108150900c6922281e507403100b0900e040d5901501c80c240e0b01c0005960b104003041066100c07552500c83c2032031200d040380080e0b02501080742c1c245d0035030708406803449807004580000e070344d600b1000c100210b00300b00040702ca8000b00300582c8000c0345808001070b1034440002c4441105015030204200545541c100741e0b10020b001c1c0380c004001040011035106c80801071201d682c09220703600c2165078004800545002e240361500801e0051141640c6a0995100401400081d10490f00542c106841501d00d0329190080e41d050f22908480d103420140d195100301c400100c2403070203038154019500b8083c059204c00c07003070300c0550703000b60010140051010601005200c940c9442c004020042c0111004084c0c04208401107403001e14484902d00813994000c0000703610b03203403021130152000442c08080e00c95010003902c1035008482800030880d03103100b801d210b03002d50301d100d50000380c0041342403041c1400342c03841540040d40580 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 962229109 1250 962227859 962227867
    0x524010c06090b0609180a150b060304050a0b01060509061213080c070303200d082e06020d0c0201140d06030212011d030a0f0507020112050f01080d030612030311 71
    0xd80c10700720780045500341c800308560300400c1040e042c009041d0760010344154008000c2e01d80c0703100103615003200400085c010210b01030303070030312110b8a40c000203060358008000e1b40d0380703041070320b040c55456204050440e4207140800001440d1806403050322000480540900e14080c07903000d001086000040901e00500c880c000d14001240002e070207000d40f0404c02008003c45425800c0103807591400c846075045801525072200142c1d800841c001c40c450308e045c01d10403440d458400100502c1c94840d040e6681c0c494005511099070f070101d04041040301c0b115020749049400c400000c490b0300718140006030106800000d02001c540151005105620040400280d86900c0c0e03400204040301e5103800e42c1c0e01307a444e01125440c107104c1079030406250074240010340c41c0000c015005020b110380c1c401400203101c004641c003001d40e4044c0100010324450350700104880d2401083c0c46800305000c1c090010030748076803003101c55058082c1c814142036640600c0c40084540d040d0b602107000d002100c83d00e04d2544d400b40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 962230215 1106 962229109 962229113
    0x31c08011a0c1e07083c010e030a140307090611030702150a020d090f0608061c0c14010c030e060a090f030c031509080a030c05130806010503100524010c 67
    0x181d4411b444003040daa40d8140c4c103540140107911075080605010031880c01100411508007070361a01000d100340424592030601044800c8008610b51040a101c0e503809511101159103da80440340341810641c0421a10160014900c085c0784000c0b954114413a010b00542c80c0707440e042d103440d03400d013845c1598071003990305144908000d00220401090385501c0d01c241448480d110b90b0100c050255113031901ca0072130307811840350486210700c10702c02a086600c1010a41e43c1c01d901541d45940e4031040500b045284da02c0b0618105c103202082d800043c0320554990540001d500809111101c00d16508203000001e060042d410318980c41e00806a0014032540700792040c01403149000560700340c0d6880c040c1c82c9403240da0b001176140c001460300001c5440d00007401c507041c0c48003502610f07042c4405036006402d555081c2d4502c400c0031a400d101d01c1c04002c40c0b0013052410b100c14908032082201c16 = true := by decide +kernel

theorem cover : BRFrame.Cov 962050359 962230215 := by
  have h0 := BRFrame.cov_init 962050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 962050359 ≤ n) (h2 : n < 962230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
